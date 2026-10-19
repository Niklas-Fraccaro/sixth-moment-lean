#!/usr/bin/env python3
"""Verify a necessary actual-250-row consumer, not independent A03/A04 closure.

Exit 2 means OPEN, exit 1 means a rejected source/audit or environment error.
A static source scan, a declaration name, JSON status and historical logs never
prove the consumer. Only a fresh Lean check against its prescribed exact type
plus a fresh transitive axiom audit can do that. Even a valid consumer alone
does not establish the quantitative A03 theorem or every A04 obligation.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from verify_extensions import extension_graph
from verify_project import (ROOT, audit_axioms, compile_modules, digest, lean_code,
                            source_checks, production_paths, validate_recorded_modules)
from verify_a03_resume import normalized_records

TARGET_MODULE = "Sechstmoment.Numerator.CertificateStatement"
TARGET = "Sechstmoment.FirstRowNumeratorConsumer"
WITNESS = "Sechstmoment.firstRowNumeratorConsumer"
FIRST_ROW_OPEN = "OPEN; A03_A04_NOT_INDEPENDENTLY_CERTIFIED"
# The exact Watt proposition, historical contracts and proved AFE specification are
# pinned to the supplied project's sources.
# An intentional source-contract revision must be reviewed and repinned here.
SOURCE_BOUNDARY_DIGESTS = {
    "Sechstmoment/Arithmetic/Watt/Statement.lean": "4e7b5b7fc1e74b6756200f785539ea8f0bab768d82eb47c41882df48e1ba5688",
    "Sechstmoment/SourceContracts.lean": "f01dfe0f23156b4bc3e266a1a5885dc8ff83c8b7759ec125cd25eda33eb25939",
    "Sechstmoment/Zeta/AFE/Four/Specification.lean": "345523d4b2ace7380c3ee398428adeb7fd6e2ff0cd5fb950d6912eb3c687c0fc",
    "Sechstmoment/Numerator/V/DP/DPSharpSource.lean": "3a28b62fe156e7e9bc0bd9e831f82670c887081c5c1b12b512aef591fc9bf2df",
}
# Independent literal annotation: weakening the named target definition alone
# cannot make a vacuous witness pass. Source/module hashes remain in the receipt.
EXACT_CONSUMER_TYPE = """DivisorProof.Sechstmoment.Arithmetic.Watt →
∀ (Φ : ℝ → ℝ), Sechstmoment.SmoothDyadicWeight Φ →
  (∀ n : ℕ, 12 ≤ n → Filter.Tendsto
    (fun T : ℝ => Sechstmoment.actual250RawMixedMoment n T Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9)) Filter.atTop
    (nhds ((Sechstmoment.arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (Sechstmoment.certificateProfileNumerator n)))) ∧
  (∀ n : ℕ, 12 ≤ n → Filter.Tendsto
    (fun T : ℝ => Sechstmoment.actual250ProjectedMixedMoment n T Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9)) Filter.atTop
    (nhds ((Sechstmoment.arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (Sechstmoment.certificateProfileNumerator n)))) ∧
  Filter.Tendsto (fun n : ℕ => (Sechstmoment.arithmeticFactor:ℂ)*
    (∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (Sechstmoment.certificateProfileNumerator n))
    Filter.atTop (nhds ((Sechstmoment.arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (Sechstmoment.finiteNumerator:ℝ)))"""


def source_boundary_checks(root: Path, expected: dict[str, str] = SOURCE_BOUNDARY_DIGESTS) -> dict:
    actual = {name: digest(root / name) for name in expected}
    changed = [name for name in expected if actual[name] != expected[name]]
    if changed:
        raise ValueError("Sanctioned source boundary changed: " + ", ".join(changed))
    return {"source_boundary_integrity": "PASS", "sanctioned_source_boundary_sha256": actual}


def own_paths(root: Path) -> list[Path]:
    return production_paths(root)


def candidate_modules(paths: list[Path], root: Path, extra: list[str]) -> list[str]:
    """Module inventory is an import choice, never evidence of a proved theorem."""
    if any(not re.fullmatch(r"Sechstmoment(?:\.[\w]+)+", name) for name in extra):
        raise ValueError("Candidate module names must be qualified Sechstmoment module names")
    selected = [path.relative_to(root).with_suffix("").as_posix().replace("/", ".")
                for path in paths if "Numerator" in path.relative_to(root).parts]
    return list(dict.fromkeys([TARGET_MODULE, *selected, *extra]))


def witness_modules(paths: list[Path], root: Path) -> list[str]:
    # An early absence check only. Namespace resolution, type, and validity are
    # left to Lean; finding this token can never yield PASS.
    declaration = re.compile(r"\b(?:theorem|lemma|def)\s+(?:[\w]+\.)*"
                             r"firstRowNumeratorConsumer\b")
    return [path.relative_to(root).with_suffix("").as_posix().replace("/", ".")
            for path in paths if declaration.search(lean_code(path.read_text()))]


def exact_audit_source(selected: list[str]) -> str:
    return ("".join(f"import {module}\n" for module in selected) +
            "\nopen MeasureTheory\n-- This annotation rejects extra U-limit, reconstruction or target premises.\n" +
            f"example : {TARGET} := {WITNESS}\n" +
            f"example : ({EXACT_CONSUMER_TYPE}) := {WITNESS}\n" +
            f"#print axioms {WITNESS}\n")


def hash_checked_reuse(root: Path, order: list[str], direct: dict[str, list[str]],
                       receipts: list[str]) -> dict[str, dict]:
    """Reuse only strict current-day source/object pairs with valid dependency closure.

    A changed dependency invalidates unchanged dependents too. The exact
    consumer type and its transitive axiom audit are always checked freshly.
    """
    candidates = {}
    today = time.strftime("%Y-%m-%d", time.gmtime())
    strict_args = ["-j1", "-M2000", "-DwarningAsError=true"]
    for name in receipts:
        receipt = json.loads((root / name).read_text())
        if (receipt.get("date") != today or receipt.get("status") != "PASS"
                or receipt.get("strict_args") != strict_args):
            raise ValueError("Reuse requires a strict PASS receipt of the current day: " + name)
        for module, record in normalized_records(receipt).items():
            if module not in order:
                continue
            source = root / (module.replace(".", "/") + ".lean")
            output = root / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
            if (source.is_file() and output.is_file()
                    and digest(source) == record["source_sha256"]
                    and digest(output) == record["olean_sha256"]):
                candidates[module] = {"exit_code": 0, "freshly_compiled": False,
                    "reused_hash_checked_object": True, "reused_from": name,
                    "source_sha256": record["source_sha256"],
                    "olean_sha256": record["olean_sha256"]}
    accepted = {}
    for module in order:
        if module in candidates and all(dep in accepted for dep in direct[module]):
            accepted[module] = candidates[module]
    return accepted


def verify(args: argparse.Namespace, root: Path = ROOT) -> int:
    logs = root / "verification_logs/first_row"
    logs.mkdir(parents=True, exist_ok=True)
    receipt_path = root / "first_row_verification_receipt.json"
    receipt = {
        "first_row_status": FIRST_ROW_OPEN,
        "consumer_status": "OPEN",
        "scope": "Necessary actual-250-row raw/projected two-stage numerator consumer only; "
                 "no independent A03/A04 closure and no FullGoal proof.",
        "full_goal_status": "OPEN",
        "target_type": TARGET,
        "required_witness": WITNESS,
        "historical_receipts_used": False,
        "baseline_full_replay": False,
        "reused_own_modules": False,
        "kernel_checked": False,
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "modules": {},
    }

    def save():
        receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")

    try:
        paths = own_paths(root)
        receipt.update(source_checks(paths))
        receipt.update(source_boundary_checks(root))
        selected = candidate_modules(paths, root, args.candidate_module)
        witnesses = witness_modules(paths, root)
        # A consumer-only check certifies precisely its own import closure;
        # broader independent A03/A04 claims keep their existing open status.
        selected = list(dict.fromkeys(
            [TARGET_MODULE, *args.candidate_module, *witnesses] if args.consumer_only
            else [*selected, *witnesses]))
        order, direct, sources = extension_graph(paths, selected, root)
        receipt.update({"candidate_modules": selected, "own_import_closure": order,
                        "lean_toolchain": (root / "lean-toolchain").read_text().strip()})
        if args.check_sources:
            receipt["consumer_status"] = "OPEN; SOURCE_CHECK_ONLY"
            receipt["witness_declaration_present"] = bool(witnesses)
            save()
            print("Source scan: PASS. Consumer and first row: OPEN; no Lean kernel check.")
            return 2
        if not witnesses:
            receipt["reason"] = "No declaration of the prescribed consumer witness exists."
            save()
            print(f"Consumer: OPEN; missing {WITNESS}. First row: OPEN.")
            return 2

        wrapper = os.environ.get("SECHSTMOMENT_TOOLCHAIN_WRAPPER")
        lake = ([wrapper] if wrapper else []) + ["lake"]
        if args.prepare:
            subprocess.run(lake + ["exe", "cache", "get"], cwd=root, check=True)
        version = subprocess.run(lake + ["env", "lean", "--version"], cwd=root,
                                 check=True, capture_output=True, text=True)
        receipt["lean_version_output"] = version.stdout.strip()
        reusable = hash_checked_reuse(root, order, direct, getattr(args, "reuse_receipt", []))
        receipt["reused_own_modules"] = bool(reusable)
        receipt["reused_hash_checked_object_count"] = len(reusable)
        receipt["freshly_compiled_module_count"] = len(order) - len(reusable)
        print(f"Consumer import closure: {len(order)} modules; "
              f"{len(reusable)} current hash-checked objects reused.", flush=True)

        def compile_module(module):
            if module in reusable:
                return module, reusable[module]
            source = sources[module]
            output = root / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            log = logs / (module + ".log")
            source_hash = digest(source)
            with log.open("w") as file:
                process = subprocess.run(lake + ["env", "lean", "-j1", "-M2000",
                    "-DwarningAsError=true", source.relative_to(root).as_posix(), "-o", str(output)],
                    cwd=root, stdout=file, stderr=subprocess.STDOUT)
            if process.returncode:
                raise RuntimeError(f"Lean rejected {module}; read {log}")
            if digest(source) != source_hash:
                raise ValueError(f"Source changed during compilation: {module}")
            return module, {"exit_code": 0, "freshly_compiled": True,
                            "source_sha256": source_hash, "olean_sha256": digest(output)}

        def record(result):
            module, outcome = result
            receipt["modules"][module] = outcome
            save()
            if not outcome.get("reused_hash_checked_object"):
                print(f"PASS {len(receipt['modules'])}/{len(order)}: {module}", flush=True)

        compile_modules(order, direct, compile_module, record, args.workers)
        validate_recorded_modules(root, receipt["modules"])
        with tempfile.TemporaryDirectory(prefix="first_row_audit_", dir=root) as temporary:
            audit = Path(temporary) / "FirstRowAudit.lean"
            audit.write_text(exact_audit_source(selected))
            receipt["audit_source_sha256"] = digest(audit)
            process = subprocess.run(lake + ["env", "lean", "-j1", "-M2000",
                "-DwarningAsError=true", audit.relative_to(root).as_posix()],
                cwd=root, capture_output=True, text=True)
            audit_output = process.stdout + process.stderr
            (logs / "FirstRowAudit.log").write_text(audit_output)
            if process.returncode:
                raise RuntimeError("Lean rejected the prescribed consumer type; "
                                   f"read {logs / 'FirstRowAudit.log'}")
            summary = audit_axioms(audit_output, [WITNESS])
        validate_recorded_modules(root, receipt["modules"])
        (logs / "axiom_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        receipt["kernel_checked"] = True
        receipt["consumer_status"] = "PASS"
        receipt["axiom_audit"] = summary
        save()
        print("Necessary actual-250-row consumer: PASS (fresh exact type and axiom audit).")
        print("First row: OPEN; quantitative A03 and complete A04 not independently certified.")
        return 0 if args.consumer_only else 2
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        receipt["consumer_status"] = "FAIL"
        receipt["error"] = str(error)
        save()
        print(f"First-row verification failed: {error}", file=sys.stderr)
        return 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-sources", action="store_true", help="Static scan only; always exits 2 / OPEN")
    parser.add_argument("--consumer-only", action="store_true", help="Allow exit 0 for the necessary consumer only")
    parser.add_argument("--candidate-module", action="append", default=[], help="Additional own module to import freshly")
    parser.add_argument("--reuse-receipt", action="append", default=[],
                        help="Reuse strict current-day PASS objects after source, object and dependency checks")
    parser.add_argument("--prepare", action="store_true", help="Download the pinned mathlib cache")
    parser.add_argument("--workers", type=int, default=4, help="Independent module workers, 1 through 8")
    args = parser.parse_args()
    if not 1 <= args.workers <= 8:
        parser.error("--workers must be between 1 and 8")
    return verify(args, ROOT)


if __name__ == "__main__":
    sys.exit(main())
