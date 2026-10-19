"""Checks for honest static/open results and fresh exact-consumer orchestration.

Fake compiler tests check Python orchestration only, never mathematical validity.
"""
from __future__ import annotations
import argparse
import contextlib
import io
import json
import subprocess
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

import verify_first_row as gate
import verify_project


class FirstRowGateTests(unittest.TestCase):
    def fixture(self, root: Path, witness: bool = False):
        own = root / "Sechstmoment"
        own.mkdir()
        (root / "Sechstmoment.lean").write_text("import Sechstmoment.Unused\n")
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
        (own / "Base.lean").write_text("")
        (own / "Unused.lean").write_text("")
        target = root / (gate.TARGET_MODULE.replace(".", "/") + ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("import Sechstmoment.Base\n")
        (own / "A05Candidate.lean").write_text("import Sechstmoment.Base\n" +
            ("namespace Sechstmoment\ntheorem firstRowNumeratorConsumer : True := True.intro\n"
             "end Sechstmoment\n" if witness else ""))
        # Neither a current forged receipt nor a historical one can satisfy the gate.
        for name in ("first_row_verification_receipt.json", "extension_verification_receipt.json"):
            (root / name).write_text('{"first_row_status":"COMPLETE","consumer_status":"PASS"}\n')

    def args(self, **kwargs):
        options = dict(check_sources=False, consumer_only=False,
                       candidate_module=[], prepare=False, workers=1)
        options.update(kwargs)
        return argparse.Namespace(**options)

    def run_gate(self, root, args, fake_run=None):
        with (patch.object(gate, "source_checks", return_value={"source_scan": "PASS"}),
              patch.object(gate, "source_boundary_checks", return_value={"source_boundary_integrity": "PASS"}),
              patch.object(gate.subprocess, "run", fake_run) if fake_run else
              patch.object(gate.subprocess, "run") as compiler,
              contextlib.redirect_stdout(io.StringIO()),
              contextlib.redirect_stderr(io.StringIO())):
            result = gate.verify(args, root)
            if fake_run is None:
                compiler.assert_not_called()
        return result, json.loads((root / "first_row_verification_receipt.json").read_text())

    def test_no_witness_does_not_trust_receipts_or_call_lean(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.fixture(root)
            result, receipt = self.run_gate(root, self.args())
            self.assertEqual(result, 2)
            self.assertEqual(receipt["consumer_status"], "OPEN")
            self.assertFalse(receipt["kernel_checked"])
            self.assertFalse(receipt["historical_receipts_used"])
            self.assertTrue(receipt["first_row_status"].startswith("OPEN"))

    def test_static_check_with_named_witness_is_still_open(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.fixture(root, witness=True)
            result, receipt = self.run_gate(root, self.args(check_sources=True, consumer_only=True))
            self.assertEqual(result, 2)
            self.assertEqual(receipt["consumer_status"], "OPEN; SOURCE_CHECK_ONLY")
            self.assertTrue(receipt["witness_declaration_present"])
            self.assertFalse(receipt["kernel_checked"])

    def test_witness_absence_scan_ignores_comments_and_strings(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.fixture(root)
            path = root / "Sechstmoment/A05Candidate.lean"
            path.write_text('/- theorem firstRowNumeratorConsumer : True := by trivial -/\n'
                            '#eval "def firstRowNumeratorConsumer"\n')
            self.assertEqual(gate.witness_modules(gate.own_paths(root), root), [])

    def test_exact_annotation_is_independent_of_named_prop_definition(self):
        source = gate.exact_audit_source([gate.TARGET_MODULE])
        self.assertIn(f"example : ({gate.EXACT_CONSUMER_TYPE}) := {gate.WITNESS}", source)
        self.assertEqual(gate.EXACT_CONSUMER_TYPE.count("Sechstmoment.Arithmetic.Watt →"), 1)
        self.assertNotIn("FirstRowNumeratorConsumer", gate.EXACT_CONSUMER_TYPE)

    def test_candidate_names_cannot_inject_lean_commands(self):
        with self.assertRaisesRegex(ValueError, "qualified"):
            gate.candidate_modules([], Path("/unused"), ["Sechstmoment.X\naxiom bad : False"])

    def current_reuse_receipt(self, root):
        order = ["Sechstmoment.Base", "Sechstmoment.Numerator.CertificateStatement", "Sechstmoment.A05Candidate"]
        direct = {order[0]: [], order[1]: [order[0]], order[2]: [order[0]]}
        records = {}
        for module in order:
            source = root / (module.replace(".", "/") + ".lean")
            output = root / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(b"fake objects: metadata test only")
            records[module] = {"exit_code": 0, "source_sha256": gate.digest(source),
                               "olean_sha256": gate.digest(output)}
        path = root / "current_strict_replay.json"
        path.write_text(json.dumps({"date": time.strftime("%Y-%m-%d", time.gmtime()),
            "status": "PASS", "strict_args": ["-j1", "-M2000", "-DwarningAsError=true"],
            "modules": records}))
        return order, direct, path.name

    def test_valid_current_pairs_can_be_reused_but_not_unused_modules(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.fixture(root, witness=True)
            order, direct, receipt = self.current_reuse_receipt(root)
            reused = gate.hash_checked_reuse(root, order, direct, [receipt])
            self.assertEqual(set(reused), set(order))
            self.assertTrue(all(r["reused_hash_checked_object"] for r in reused.values()))
            self.assertTrue(all(not r["freshly_compiled"] for r in reused.values()))

    def test_changed_dependency_source_or_object_invalidates_unchanged_dependents(self):
        for kind in ("source", "object"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                self.fixture(root, witness=True)
                order, direct, receipt = self.current_reuse_receipt(root)
                target = (root / "Sechstmoment/Base.lean" if kind == "source" else
                          root / ".lake/build/lib/lean/Sechstmoment/Base.olean")
                target.write_bytes(b"changed dependency")
                self.assertEqual(gate.hash_checked_reuse(root, order, direct, [receipt]), {})

    def test_historical_or_non_strict_receipts_are_rejected(self):
        for change in ({"date": "2000-01-01"}, {"strict_args": []}, {"status": "RUNNING"}):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                self.fixture(root, witness=True)
                order, direct, receipt = self.current_reuse_receipt(root)
                path = root / receipt
                data = json.loads(path.read_text())
                data.update(change)
                path.write_text(json.dumps(data))
                with self.assertRaisesRegex(ValueError, "strict PASS"):
                    gate.hash_checked_reuse(root, order, direct, [receipt])

    def fake_compiler(self, root, reject_type=False, axiom_output=None):
        built = []

        def run(command, **kwargs):
            if "--version" in command:
                return subprocess.CompletedProcess(command, 0, "Lean fake (orchestration test only)\n", "")
            self.assertIn("-DwarningAsError=true", command)
            if "-o" in command:
                module = command[command.index("-o") - 1]
                if module.endswith("A05Candidate.lean") or module.endswith("FirstRowTargets.lean"):
                    self.assertIn("Sechstmoment/Base.lean", built)
                built.append(module)
                Path(command[command.index("-o") + 1]).write_bytes(b"fresh fake output")
                return subprocess.CompletedProcess(command, 0)
            source = (root / command[-1]).read_text()
            self.assertIn(f"example : {gate.TARGET} := {gate.WITNESS}\n", source)
            self.assertIn(f"#print axioms {gate.WITNESS}\n", source)
            self.assertIn(f"example : ({gate.EXACT_CONSUMER_TYPE}) := {gate.WITNESS}\n", source)
            self.assertIn("Sechstmoment.actual250RawMixedMoment", source)
            self.assertIn("Sechstmoment.actual250ProjectedMixedMoment", source)
            if reject_type:
                return subprocess.CompletedProcess(command, 1, "type mismatch: True is not the prescribed target", "")
            output = axiom_output if axiom_output is not None else (
                f"'{gate.WITNESS}' depends on axioms: [propext, Classical.choice, Quot.sound]\n")
            return subprocess.CompletedProcess(command, 0, output, "")
        return run, built

    def test_wrong_type_rejected_even_with_correct_theorem_name(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.fixture(root, witness=True)
            compiler, _ = self.fake_compiler(root, reject_type=True)
            result, receipt = self.run_gate(root, self.args(), compiler)
            self.assertEqual(result, 1)
            self.assertEqual(receipt["consumer_status"], "FAIL")
            self.assertFalse(receipt["kernel_checked"])
            self.assertFalse(list(root.glob("first_row_audit_*")))

    def test_transitive_own_axiom_and_missing_audit_both_rejected(self):
        for output in (f"'{gate.WITNESS}' depends on axioms: [unprovedUAsymptotic]\n", ""):
            with self.subTest(output=output), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                self.fixture(root, witness=True)
                compiler, _ = self.fake_compiler(root, axiom_output=output)
                result, receipt = self.run_gate(root, self.args(consumer_only=True), compiler)
                self.assertEqual(result, 1)
                self.assertEqual(receipt["consumer_status"], "FAIL")
                self.assertFalse(receipt["kernel_checked"])

    def test_fresh_type_audit_pass_never_certifies_a03_or_a04(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.fixture(root, witness=True)
            stale = root / ".lake/build/lib/lean/Sechstmoment/Base.olean"
            stale.parent.mkdir(parents=True)
            stale.write_bytes(b"stale")
            compiler, built = self.fake_compiler(root)
            result, receipt = self.run_gate(root, self.args(), compiler)
            self.assertEqual(result, 2)
            self.assertEqual(receipt["consumer_status"], "PASS")
            self.assertTrue(receipt["kernel_checked"])
            self.assertEqual(receipt["first_row_status"], gate.FIRST_ROW_OPEN)
            self.assertFalse(receipt["baseline_full_replay"])
            self.assertFalse(receipt["reused_own_modules"])
            self.assertEqual(stale.read_bytes(), b"fresh fake output")
            self.assertNotIn("Sechstmoment/Unused.lean", built)
            self.assertEqual(len(built), 3)
            compiler, _ = self.fake_compiler(root)
            result, receipt = self.run_gate(root, self.args(consumer_only=True), compiler)
            self.assertEqual(result, 0)
            self.assertEqual(receipt["first_row_status"], gate.FIRST_ROW_OPEN)

    def test_weakened_named_paper_input_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "Source.lean"
            source.write_text("def PaperInput : Prop := False\n")
            expected = {"Source.lean": gate.digest(source)}
            self.assertEqual(gate.source_boundary_checks(root, expected)["source_boundary_integrity"], "PASS")
            source.write_text("def PaperInput : Prop := True\n")
            with self.assertRaisesRegex(ValueError, "source boundary changed"):
                gate.source_boundary_checks(root, expected)

    def test_actual_source_scan_rejects_candidate_hole(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.fixture(root)
            path = root / "Sechstmoment/A05Candidate.lean"
            path.write_text("theorem incomplete : False := by sorry\n")
            with self.assertRaisesRegex(ValueError, "Forbidden construct"):
                verify_project.source_checks([path])


if __name__ == "__main__":
    unittest.main()
