"""Regression checks for the explicitly limited extension-only replay."""
import contextlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import verify_extensions as extension


class ExtensionRegressionTests(unittest.TestCase):
    def test_graph_multi_imports_and_transitive_closure(self):
        with tempfile.TemporaryDirectory(dir=extension.ROOT) as temporary:
            root = Path(temporary)
            module_dir = root / "Sechstmoment"
            module_dir.mkdir()
            definitions = {
                "Base": "",
                "Other": "import Sechstmoment.Base\n",
                "New": "import Sechstmoment.Other Sechstmoment.Base\n",
                "Unused": "",
            }
            paths = []
            for name, source in definitions.items():
                path = module_dir / (name + ".lean")
                path.write_text(source)
                paths.append(path)
            order, direct, _ = extension.extension_graph(paths, ["Sechstmoment.New"], root)
            self.assertEqual(order, ["Sechstmoment.Base", "Sechstmoment.Other", "Sechstmoment.New"])
            self.assertEqual(direct["Sechstmoment.New"], ["Sechstmoment.Other", "Sechstmoment.Base"])
            with self.assertRaisesRegex(ValueError, "have no source files"):
                extension.extension_graph(paths, ["Sechstmoment.Absent"], root)
            (module_dir / "Base.lean").write_text("import Sechstmoment.New\n")
            with self.assertRaisesRegex(ValueError, "Cyclic"):
                extension.extension_graph(paths, ["Sechstmoment.New"], root)
            (module_dir / "Base.lean").write_text("import Sechstmoment.Missing\n")
            with self.assertRaisesRegex(ValueError, "Missing own import"):
                extension.extension_graph(paths, ["Sechstmoment.New"], root)

    def test_manifest_duplicates_unicode_and_command_injection(self):
        with tempfile.TemporaryDirectory(dir=extension.ROOT) as temporary:
            path = Path(temporary) / "manifest.json"
            path.write_text(json.dumps(["Sechstmoment.completedRiemannZeta₀_conj"]))
            self.assertEqual(len(extension.read_name_manifest(path)), 1)
            path.write_text(json.dumps(["Sechstmoment.one"] * 2))
            with self.assertRaisesRegex(ValueError, "Duplicate"):
                extension.read_name_manifest(path)
            path.write_text(json.dumps(["Sechstmoment.one\n#check False"]))
            with self.assertRaisesRegex(ValueError, "qualified names"):
                extension.read_name_manifest(path)

    def test_fresh_replay_and_failure_receipt(self):
        # This tests orchestration with a fake compiler, not Lean kernel validity.
        with tempfile.TemporaryDirectory(dir=extension.ROOT) as temporary:
            root = Path(temporary)
            module_dir = root / "Sechstmoment"
            module_dir.mkdir()
            (root / "Sechstmoment.lean").write_text("import Sechstmoment.Unused\n")
            (module_dir / "Base.lean").write_text("")
            (module_dir / "New.lean").write_text("import Sechstmoment.Base\n")
            (module_dir / "Unused.lean").write_text("")
            (root / "extension_modules.json").write_text(json.dumps(["Sechstmoment.New"]))
            (root / "extension_theorems.json").write_text(json.dumps(["Sechstmoment.new_theorem"]))
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
            built, scanned = [], []
            audit_is_missing = [False]
            for name in ("Base", "New"):
                output = root / ".lake/build/lib/lean/Sechstmoment" / (name + ".olean")
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_bytes(b"STALE")

            def source_scan(paths):
                scanned.extend(paths)
                return {"source_scan": "PASS"}

            def fake_run(command, **kwargs):
                if "--version" in command:
                    return subprocess.CompletedProcess(command, 0, "Lean mock\n", "")
                self.assertIn("-j1", command)
                self.assertIn("-M2000", command)
                self.assertIn("-DwarningAsError=true", command)
                if "-o" in command:
                    source = command[command.index("-o") - 1]
                    name = Path(source).stem
                    if name == "New":
                        self.assertEqual(built, ["Base"])
                    built.append(name)
                    Path(command[command.index("-o") + 1]).write_bytes(b"FRESH")
                    return subprocess.CompletedProcess(command, 0)
                audit = root / command[-1]
                self.assertEqual(audit.read_text(),
                    "import Sechstmoment.New\n\n#print axioms Sechstmoment.new_theorem\n")
                text = "" if audit_is_missing[0] else (
                    "'Sechstmoment.new_theorem' depends on axioms: [propext]\n")
                return subprocess.CompletedProcess(command, 0, text, "")

            with (patch.object(extension, "ROOT", root),
                  patch.object(extension, "source_checks", source_scan),
                  patch.object(extension.subprocess, "run", fake_run),
                  patch.object(sys, "argv", ["verify_extensions.py"]),
                  contextlib.redirect_stdout(io.StringIO()),
                  contextlib.redirect_stderr(io.StringIO())):
                self.assertEqual(extension.main(), 0)
                receipt = json.loads((root / "extension_verification_receipt.json").read_text())
                self.assertEqual(receipt["extension_status"], "PASS")
                self.assertEqual(receipt["full_goal_status"], "OPEN")
                self.assertFalse(receipt["baseline_full_replay"])
                self.assertFalse(receipt["reused_own_modules"])
                self.assertEqual(set(receipt["modules"]), {"Sechstmoment.Base", "Sechstmoment.New"})
                self.assertEqual(len(scanned), 4)
                self.assertFalse(list(root.glob("extension_audit_*")))
                built.clear()
                audit_is_missing[0] = True
                self.assertEqual(extension.main(), 1)
                receipt = json.loads((root / "extension_verification_receipt.json").read_text())
                self.assertEqual(receipt["extension_status"], "FAIL")
                self.assertEqual(receipt["full_goal_status"], "OPEN")
                self.assertFalse(list(root.glob("extension_audit_*")))

    def test_require_full_delegates_to_the_strict_full_goal_gate(self):
        with (patch.object(sys, "argv", ["verify_extensions.py", "--require-full"]),
              patch.object(extension.subprocess, "run", return_value=subprocess.CompletedProcess([], 2)) as compiler,
              contextlib.redirect_stdout(io.StringIO())):
            self.assertEqual(extension.main(), 2)
            compiler.assert_called_once()
            self.assertIn("verify_full_goal.py", compiler.call_args.args[0])


if __name__ == "__main__":
    unittest.main()
