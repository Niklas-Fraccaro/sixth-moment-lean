#!/usr/bin/env python3
"""Recheck the auxiliary formalization; never equate it with FullGoal."""
from __future__ import annotations
import argparse
import csv
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path

ROOT = Path(__file__).resolve().parent
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# User-confirmed final scope: prove the actual conclusion from the quoted
# literature, without proving the external papers themselves.  Keep a literal
# annotation independent of the named goal definition, so weakening that
# definition or adding an own target-asymptotic premise cannot satisfy the gate.
EXACT_FULL_PROOF_TYPE = """DivisorProof.Sechstmoment.Arithmetic.Watt →
Sechstmoment.FullGoal"""
FULL_GOAL_BOUNDARY_DIGESTS = {
    "Sechstmoment/MainGoal.lean": "785e5ef3b34157d83c0c5af8724974269d5acfad13cd60bafe88ee4139d70358",
    "Sechstmoment/AnalyticMoments.lean": "fbfddaecdb18ee2c23476d0573bf7777fa6ceb2de2dd415290db6c30feae25e9",
}


def production_paths(root: Path) -> list[Path]:
    """Every retained project module, including independent reusable results."""
    return ([root / "Sechstmoment.lean"]
            + sorted((root / "Sechstmoment").rglob("*.lean"))
            + sorted((root / "Salt").rglob("*.lean")))


def full_proof_gate_source() -> str:
    return ("import Sechstmoment\n"
            "example : Sechstmoment.LiteratureRelativeGoal := Sechstmoment.fullProof\n"
            f"example : ({EXACT_FULL_PROOF_TYPE}) := Sechstmoment.fullProof\n"
            "#print axioms Sechstmoment.fullProof\n")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def full_goal_boundary_checks(root: Path) -> dict:
    # Local import avoids coupling the ordinary auxiliary replay to the
    # first-row command.  A full proof keeps its actual goal and paper inputs.
    from verify_first_row import source_boundary_checks
    result = source_boundary_checks(root)
    actual = {name: digest(root / name) for name in FULL_GOAL_BOUNDARY_DIGESTS}
    if actual != FULL_GOAL_BOUNDARY_DIGESTS:
        raise ValueError("Original mathematical goal or actual moment definitions changed")
    result["original_full_goal_boundary_sha256"] = actual
    return result


def validate_recorded_modules(root: Path, modules: dict) -> None:
    """Detect changes after a recorded compilation, before claiming PASS."""
    for module, outcome in modules.items():
        source = root / (module.replace(".", "/") + ".lean")
        output = root / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        if (digest(source) != outcome["source_sha256"]
                or digest(output) != outcome["olean_sha256"]):
            raise RuntimeError(f"Recorded module changed before final audit: {module}")


def lean_code(text: str) -> str:
    """Discard strings and nested Lean comments, preserving line breaks."""
    result = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    result.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean comment")
    return "".join(result)


def source_checks(paths: list[Path]) -> dict:
    banned = re.compile(
        r"\b(?:sorry|admit|axiom|native_decide|unsafe|ofReduceBool)\b"
        r"|decide\s*\+\s*native|debug\.skipKernelTC|implemented_by|\bextern\b"
    )
    for path in paths:
        match = banned.search(lean_code(path.read_text()))
        if match:
            raise ValueError(f"Forbidden construct {match.group()!r}: {path}")
    data = (ROOT / "Sechstmoment/Certificate/Data.lean").read_text()
    rows = re.findall(
        r"⟨(\d+),\s*\.([UV]),\s*(\d+),\s*(\d+),\s*(\d+),\s*(-?\d+)⟩", data
    )
    with (ROOT / "certificate_250.tsv").open(newline="") as file:
        tsv = list(csv.DictReader(file, delimiter="\t"))
    expected = [tuple(row[k] for k in ("j", "type", "A", "B", "r", "c")) for row in tsv]
    if len(expected) != 250 or rows != expected:
        raise ValueError("Lean data does not reproduce the 250 TSV rows exactly")
    return {
        "source_scan": "PASS; no own axioms or proof holes",
        "transcription": "PASS; 250 ordered rows equal the supplied TSV",
        "input_tsv_sha256": digest(ROOT / "certificate_250.tsv"),
        "source_sha256": {p.relative_to(ROOT).as_posix(): digest(p) for p in paths},
    }


def dependency_order(paths: list[Path]) -> list[str]:
    modules = {p.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."): p for p in paths}
    result, active, done = [], set(), set()

    def visit(module):
        if module in done:
            return
        if module in active:
            raise ValueError(f"Cyclic own imports: {module}")
        active.add(module)
        for dependency in re.findall(r"^import\s+(\S+)", lean_code(modules[module].read_text()), re.M):
            if dependency in modules:
                visit(dependency)
        active.remove(module)
        done.add(module)
        result.append(module)

    for module in sorted(modules):
        visit(module)
    return result


def audit_axioms(text: str, expected_theorems: list[str]) -> dict:
    if (not isinstance(expected_theorems, list) or not expected_theorems or
            any(not isinstance(name, str) or not name for name in expected_theorems)):
        raise ValueError("The axiom audit manifest must contain theorem names")
    if len(expected_theorems) != len(set(expected_theorems)):
        raise ValueError("Duplicate theorem names in the axiom audit manifest")
    entries = re.findall(
        r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", text
    )
    names = [name for name, _ in entries]
    if len(names) != len(set(names)):
        raise ValueError("Duplicate theorem entries in the axiom audit output")
    missing = set(expected_theorems) - set(names)
    unexpected = set(names) - set(expected_theorems)
    if missing or unexpected:
        raise ValueError("Incomplete or unexpected axiom audit output: "
                         f"missing={sorted(missing)}, unexpected={sorted(unexpected)}")
    dependencies = {}
    for name, axioms in entries:
        used = {x.strip() for x in axioms.split(",") if x.strip()}
        unknown = used - STANDARD_AXIOMS
        if unknown:
            raise ValueError(f"Unexpected transitive axioms in {name}: {sorted(unknown)}")
        dependencies[name] = sorted(used)
    return {"result": "PASS", "allowed_foundational_axioms": sorted(STANDARD_AXIOMS),
            "theorems": dependencies}


def compile_modules(order: list[str], direct_imports: dict[str, list[str]],
                    compile_module, record, workers: int, initial_done=()) -> None:
    """Compile independent modules concurrently, after recording their imports.

    A failed compilation never enables its consumers. Only the main thread
    records results and changes the dependency state or verification receipt.
    """
    if workers < 1:
        raise ValueError("workers must be positive")
    done = set(initial_done)
    pending, running = [module for module in order if module not in done], {}
    with ThreadPoolExecutor(max_workers=workers) as executor:
        while pending or running:
            ready = [module for module in pending
                     if set(direct_imports[module]) <= done]
            for module in ready[:workers-len(running)]:
                running[executor.submit(compile_module, module)] = module
                pending.remove(module)
            if not running:
                raise ValueError("Own-module dependencies cannot be satisfied: "
                                 + ", ".join(pending))
            completed, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in completed:
                result = future.result()
                record(result)
                done.add(running.pop(future))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true", help="Download the pinned mathlib cache")
    parser.add_argument("--workers", type=int, default=4, help="Independent module compilations; default 4")
    parser.add_argument("--reuse", action="store_true", help="Reuse current local .olean files")
    parser.add_argument("--require-full", action="store_true",
                        help="Require the complete FullGoal proof from Watt 4.1")
    args = parser.parse_args()
    if args.workers < 1 or args.workers > 8:
        parser.error("--workers must be between 1 and 8")
    wrapper = os.environ.get("SECHSTMOMENT_TOOLCHAIN_WRAPPER")
    lake = ([wrapper] if wrapper else []) + ["lake"]
    logs = ROOT / "verification_logs"
    logs.mkdir(exist_ok=True)
    paths = production_paths(ROOT)
    receipt = source_checks(paths)
    receipt.update({"full_goal_status": "OPEN", "full_goal_type": "Sechstmoment.LiteratureRelativeGoal",
                    "mathematical_conclusion": "Sechstmoment.FullGoal",
                    "exact_full_proof_type": EXACT_FULL_PROOF_TYPE,
                    "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
                    "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "modules": {}})
    if args.require_full:
        receipt.update(full_goal_boundary_checks(ROOT))
    if args.prepare:
        subprocess.run(lake + ["exe", "cache", "get"], cwd=ROOT, check=True)
    version = subprocess.run(lake + ["env", "lean", "--version"], cwd=ROOT,
                             check=True, capture_output=True, text=True)
    receipt["lean_version_output"] = version.stdout.strip()
    order = dependency_order(paths)
    own_modules = set(order)
    direct_imports = {
        module: [name for name in re.findall(r"^import\s+([A-Za-z0-9_.]+)",
            lean_code((ROOT / (module.replace(".", "/") + ".lean")).read_text()), re.M)
            if name in own_modules]
        for module in order
    }

    def compile_module(module):
        source = ROOT / (module.replace(".", "/") + ".lean")
        output = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        log = logs / (module + ".log")
        output.parent.mkdir(parents=True, exist_ok=True)
        dependency_outputs = [ROOT / ".lake/build/lib/lean" /
            (name.replace(".", "/") + ".olean") for name in direct_imports[module]]
        if (args.reuse and output.exists()
                and all(path.exists() for path in dependency_outputs)
                and output.stat().st_mtime >= max(path.stat().st_mtime
                    for path in [source] + dependency_outputs)):
            return module, {"exit_code": 0, "reused_local_proof": True,
                "source_sha256": digest(source), "olean_sha256": digest(output)}
        started = time.monotonic()
        source_hash = digest(source)
        with log.open("w") as file:
            command = lake + ["env", "lean", "-j1", "-M2000", "-DwarningAsError=true",
                              source.relative_to(ROOT).as_posix(), "-o", str(output)]
            process = subprocess.run(command, cwd=ROOT, stdout=file, stderr=subprocess.STDOUT)
        if process.returncode:
            raise RuntimeError(f"Lean rejected {module}; read {log}")
        if digest(source) != source_hash:
            raise RuntimeError(f"Source changed during compilation: {module}")
        return module, {"exit_code": 0, "seconds": round(time.monotonic()-started, 2),
                        "source_sha256": source_hash, "olean_sha256": digest(output)}

    def record(result):
        module, outcome = result
        receipt["modules"][module] = outcome
        print(f"PASS {len(receipt['modules'])}/{len(order)}: {module}", flush=True)

    gram = [m for m in order if m.startswith("Sechstmoment.Certificate.GramBlocks.")]
    compile_modules(order, direct_imports, compile_module, record, args.workers)
    validate_recorded_modules(ROOT, receipt["modules"])
    expected_theorems = json.loads((ROOT / "audited_theorems.json").read_text())
    import tempfile
    audit_source = "import Sechstmoment\n" + "".join(
        f"#print axioms {name}\n" for name in expected_theorems)
    with tempfile.TemporaryDirectory(prefix="sechstmoment-axioms-") as temporary:
        gate = Path(temporary) / "AxiomInventory.lean"
        gate.write_text(audit_source, encoding="utf-8")
        run = subprocess.run(lake + ["env", "lean", "-j1", str(gate)],
                             cwd=ROOT, capture_output=True, text=True)
        (logs / "axiom_inventory.log").write_text(run.stdout + run.stderr)
        if run.returncode:
            raise RuntimeError("Lean rejected the full axiom inventory")
        axiom_result = audit_axioms(run.stdout + run.stderr, expected_theorems)
    (logs / "axiom_summary.json").write_text(json.dumps(axiom_result, indent=2))
    receipt["axiom_audit"] = {"result": "PASS", "checked_theorems": len(axiom_result["theorems"])}
    receipt["checked_parts_status"] = "PASS"
    receipt["gram_blocks"] = len(gram)
    receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    if args.require_full:
        gate = ROOT / "FullVerificationGate.lean"
        gate.write_text(full_proof_gate_source())
        try:
            run = subprocess.run(lake + ["env", "lean", "-j1", gate.relative_to(ROOT).as_posix()],
                                 cwd=ROOT, capture_output=True, text=True)
            (logs / "full_goal_gate.log").write_text(run.stdout + run.stderr)
            if run.returncode:
                receipt["full_goal_gate"] = "FAIL: no complete FullGoal proof from the cited literature inputs"
            else:
                receipt["full_proof_axiom_audit"] = audit_axioms(
                    run.stdout + run.stderr, ["Sechstmoment.fullProof"])
                receipt["full_goal_status"] = "PROVED"
                receipt["full_goal_gate"] = "PASS"
        finally:
            gate.unlink(missing_ok=True)
    (ROOT / "verification_receipt.json").write_text(json.dumps(receipt, indent=2))
    print("Checked auxiliary formalization: PASS.")
    if receipt["full_goal_status"] == "OPEN":
        print("Complete theorem from the cited literature inputs: OPEN; not Lean-verified.")
        return 2 if args.require_full else 0
    print("FullGoal from Watt 4.1: PROVED.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)
