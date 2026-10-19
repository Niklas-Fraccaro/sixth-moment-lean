#!/usr/bin/env python3
"""Verify the extension closure, or the exact original FullGoal with --require-full."""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from verify_project import (ROOT, audit_axioms, compile_modules, digest, lean_code,
                            source_checks, production_paths, validate_recorded_modules)


def read_name_manifest(path: Path) -> list[str]:
    names = json.loads(path.read_text())
    if (not isinstance(names, list) or not names or
            any(not isinstance(name, str) or not re.fullmatch(r"[\w.]+", name)
                for name in names)):
        raise ValueError(f"Expected a nonempty list of qualified names: {path.name}")
    if len(names) != len(set(names)):
        raise ValueError(f"Duplicate names in {path.name}")
    return names


def extension_graph(paths: list[Path], selected: list[str], root: Path = ROOT):
    """Return every transitive own dependency, including multi-module imports."""
    sources = {path.relative_to(root).with_suffix("").as_posix().replace("/", "."): path
               for path in paths}
    missing = set(selected) - sources.keys()
    if missing:
        raise ValueError(f"Extension modules have no source files: {sorted(missing)}")
    direct = {}
    for module, path in sources.items():
        imports = []
        for line in re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)",
                               lean_code(path.read_text()), re.M):
            for name in line.split():
                if name in sources or name == "Sechstmoment" or name.startswith(("Sechstmoment.", "Salt.")):
                    if name not in sources:
                        raise ValueError(f"Missing own import {name} in {module}")
                    imports.append(name)
        direct[module] = imports
    order, active, done = [], set(), set()

    def visit(module):
        if module in done:
            return
        if module in active:
            raise ValueError(f"Cyclic own imports: {module}")
        active.add(module)
        for dependency in direct[module]:
            visit(dependency)
        active.remove(module)
        done.add(module)
        order.append(module)

    for module in selected:
        visit(module)
    return order, {module: direct[module] for module in order}, sources


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true", help="Download the pinned mathlib cache")
    parser.add_argument("--workers", type=int, default=4, help="Parallel independent modules")
    parser.add_argument("--continue-current-run", action="store_true",
                        help="Continue a recorded fresh replay after validating all compiled source/object hashes")
    parser.add_argument("--require-full", action="store_true", help="Run the strict original FullGoal type and axiom gate")
    args = parser.parse_args()
    if not 1 <= args.workers <= 8:
        parser.error("--workers must be between 1 and 8")
    if args.require_full:
        command = ["lake", "env", sys.executable, "verify_full_goal.py", "--workers", str(args.workers)]
        if args.prepare:
            subprocess.run(["lake", "exe", "cache", "get"], cwd=ROOT, check=True)
        return subprocess.run(command, cwd=ROOT).returncode

    logs = ROOT / "verification_logs/extensions"
    logs.mkdir(parents=True, exist_ok=True)
    receipt_path = ROOT / "extension_verification_receipt.json"
    prior_text = receipt_path.read_text() if receipt_path.exists() else None
    prior = None
    if prior_text is not None:
        # Retain evidence even when a later source scan or continuation guard fails.
        history = ROOT / "history/current_replay_continuations"
        history.mkdir(parents=True, exist_ok=True)
        stamp = str(time.time_ns())
        prior = history / f"receipt_{stamp}.json"
        prior.write_text(prior_text)
        shutil.copytree(logs, history / f"logs_{stamp}")
    receipt = {
        "status": "PARTIAL_FORMALIZATION; FULL_GOAL_OPEN",
        "full_goal_status": "OPEN",
        "extension_status": "RUNNING",
        "scope": "All own sources scanned; only selected extensions and their complete own import closure freshly compiled.",
        "baseline_full_replay": False,
        "reused_own_modules": False,
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "modules": {},
    }

    def save_receipt():
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")

    save_receipt()
    try:
        paths = production_paths(ROOT)
        receipt.update(source_checks(paths))
        selected = read_name_manifest(ROOT / "extension_modules.json")
        theorems = read_name_manifest(ROOT / "extension_theorems.json")
        order, direct, sources = extension_graph(paths, selected, root=ROOT)
        receipt.update({
            "extension_modules": selected,
            "own_import_closure": order,
            "extension_modules_manifest_sha256": digest(ROOT / "extension_modules.json"),
            "extension_theorems_manifest_sha256": digest(ROOT / "extension_theorems.json"),
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        })
        if args.continue_current_run:
            seed = json.loads(prior_text) if prior_text else None
            if not seed or seed.get("reused_own_modules") is not False:
                raise ValueError("Continuation requires a recorded fresh replay")
            if seed.get("lean_toolchain") != receipt["lean_toolchain"]:
                raise ValueError("Toolchain changed during the recorded replay")
            confirmed = seed.get("modules", {})
            if not set(confirmed) <= set(order):
                raise ValueError("Previously compiled modules left the import closure")
            for module, outcome in confirmed.items():
                source = sources[module]
                output = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
                if (outcome.get("freshly_compiled") is not True or outcome.get("exit_code") != 0
                        or digest(source) != outcome.get("source_sha256")
                        or not output.exists() or digest(output) != outcome.get("olean_sha256")
                        or not set(direct[module]) <= set(confirmed)):
                    raise ValueError(f"Recorded fresh dependency changed: {module}")
            receipt["modules"] = confirmed
            receipt["fresh_replay_continuations"] = seed.get("fresh_replay_continuations", []) + [{
                "prior_receipt": prior.relative_to(ROOT).as_posix(),
                "prior_receipt_sha256": digest(prior),
                "hash_verified_current_run_modules": len(confirmed),
                "started_utc": receipt["started_utc"],
            }]
            receipt["isolated_replay_started_utc"] = seed.get(
                "isolated_replay_started_utc", seed["started_utc"])
            receipt["scope"] = ("Fresh recorded replay and explicit continuations; every retained "
                                "current-run source/object hash checked, no earlier checkpoint objects used.")
            save_receipt()
        wrapper = os.environ.get("SECHSTMOMENT_TOOLCHAIN_WRAPPER")
        lake = ([wrapper] if wrapper else []) + ["lake"]
        if args.prepare:
            subprocess.run(lake + ["exe", "cache", "get"], cwd=ROOT, check=True)
        version = subprocess.run(lake + ["env", "lean", "--version"], cwd=ROOT,
                                 check=True, capture_output=True, text=True)
        receipt["lean_version_output"] = version.stdout.strip()

        def compile_module(module):
            source = sources[module]
            output = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            log = logs / (module + ".log")
            started = time.monotonic()
            source_hash = digest(source)
            with log.open("w") as file:
                process = subprocess.run(lake + ["env", "lean", "-j1", "-M2000",
                    "-DwarningAsError=true", source.relative_to(ROOT).as_posix(), "-o", str(output)],
                    cwd=ROOT, stdout=file, stderr=subprocess.STDOUT)
            if process.returncode:
                raise RuntimeError(f"Lean rejected {module}; read {log}")
            if digest(source) != source_hash:
                raise RuntimeError(f"Source changed during compilation: {module}")
            return module, {"exit_code": 0, "freshly_compiled": True,
                            "seconds": round(time.monotonic() - started, 2),
                            "source_sha256": source_hash, "olean_sha256": digest(output)}

        def record(result):
            module, outcome = result
            receipt["modules"][module] = outcome
            save_receipt()
            print(f"PASS {len(receipt['modules'])}/{len(order)}: {module}", flush=True)

        compile_modules(order, direct, compile_module, record, args.workers,
                        initial_done=receipt["modules"])
        validate_recorded_modules(ROOT, receipt["modules"])
        with tempfile.TemporaryDirectory(prefix="extension_audit_", dir=ROOT) as temporary:
            audit = Path(temporary) / "ExtensionAudit.lean"
            audit.write_text("".join(f"import {module}\n" for module in selected) + "\n" +
                             "".join(f"#print axioms {name}\n" for name in theorems))
            receipt["audit_source_sha256"] = digest(audit)
            process = subprocess.run(lake + ["env", "lean", "-j1", "-M2000",
                "-DwarningAsError=true", audit.relative_to(ROOT).as_posix()],
                cwd=ROOT, capture_output=True, text=True)
            audit_output = process.stdout + process.stderr
            (logs / "ExtensionAudit.log").write_text(audit_output)
            if process.returncode:
                raise RuntimeError(f"Lean rejected ExtensionAudit; read {logs / 'ExtensionAudit.log'}")
            summary = audit_axioms(audit_output, theorems)
        validate_recorded_modules(ROOT, receipt["modules"])
        (logs / "axiom_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        receipt["axiom_audit"] = {"result": "PASS", "checked_theorems": len(summary["theorems"])}
        receipt["extension_status"] = "PASS"
        receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        save_receipt()
        print("Extension import closure and exact theorem audit: PASS.")
        print("FullGoal: OPEN; no full baseline replay or complete analytic proof is claimed.")
        return 0
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        receipt["extension_status"] = "FAIL"
        receipt["error"] = str(error)
        receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        save_receipt()
        print(f"Extension verification failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
