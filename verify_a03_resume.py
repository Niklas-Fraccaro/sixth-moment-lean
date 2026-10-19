#!/usr/bin/env python3
"""Strict, hash-recorded Lean replay of selected A03 import closures.

Only objects produced in this replay and with unchanged sources are reused.
Historical receipts and uncompiled drafts are never treated as proofs.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalized_records(receipt: dict) -> dict[str, dict]:
    """Read the independently recorded strict-compile receipts of this task."""
    records = receipt.get("modules", {})
    if isinstance(records, list):
        pairs = [(x["module"], x) for x in records]
    elif isinstance(records, dict):
        pairs = list(records.items())
    else:
        raise ValueError("Invalid receipt module inventory")
    if "module" in receipt:
        pairs.append((receipt["module"], receipt))
    result = {}
    for module, record in pairs:
        if not module.startswith(("Sechstmoment.", "Salt.")):
            module = "Sechstmoment." + module
        code = record.get("exit_code", record.get("compile_exit_code"))
        if code != 0 and record.get("status") not in {"PASS", "STRICT_PASS"}:
            continue
        source_hash = record.get("source_sha256")
        output_hash = record.get("olean_sha256", record.get("object_sha256"))
        if not source_hash or not output_hash:
            continue
        result[module] = dict(record, source_sha256=source_hash, olean_sha256=output_hash,
                              log=record.get("log", record.get("strict_compile_log",
                                            record.get("compile_log"))))
    return result


def closure(targets: list[str]) -> dict[str, list[str]]:
    dependencies: dict[str, list[str]] = {}
    active: set[str] = set()

    def visit(module: str) -> None:
        if module in active:
            raise ValueError(f"Import cycle at {module}")
        if module in dependencies:
            return
        source = ROOT / (module.replace(".", "/") + ".lean")
        if not source.is_file():
            raise FileNotFoundError(source)
        active.add(module)
        imports = [x for x in re.findall(r"^import\s+(\S+)", source.read_text(), re.M)
                   if x.startswith(("Sechstmoment.", "Salt."))]
        for imported in imports:
            visit(imported)
        active.remove(module)
        dependencies[module] = imports

    for target in targets:
        visit(target)
    return dependencies


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="+")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--state", default="verification_logs/resume")
    parser.add_argument("--reuse-receipt", action="append", default=[],
                        help="Reuse hash-valid objects from another receipt of this task")
    parser.add_argument("--dependencies-only", action="store_true")
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("workers must be positive")
    targets = [x if x.startswith("Sechstmoment.") else "Sechstmoment." + x
               for x in args.targets]
    deps = closure(targets)
    if args.dependencies_only:
        deps = {k: v for k, v in deps.items() if k not in targets}
    state = ROOT / args.state
    state.mkdir(parents=True, exist_ok=True)
    receipt_path = state / "receipt.json"
    receipt = json.loads(receipt_path.read_text()) if receipt_path.exists() else {
        "date": time.strftime("%Y-%m-%d", time.gmtime()), "modules": {}, "failures": {}}
    for name in args.reuse_receipt:
        reused = json.loads((ROOT / name).read_text())
        if reused.get("date") != time.strftime("%Y-%m-%d", time.gmtime()):
            raise ValueError("Only receipts of this dated replay may be reused")
        for module, record in normalized_records(reused).items():
            if module not in deps:
                continue
            source = ROOT / (module.replace(".", "/") + ".lean")
            output = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
            if (output.is_file() and record["source_sha256"] == sha(source)
                    and record["olean_sha256"] == sha(output)):
                receipt["modules"][module] = dict(record, reused_from=name)
    done: set[str] = set()
    for module in deps:
        record = receipt["modules"].get(module)
        source = ROOT / (module.replace(".", "/") + ".lean")
        output = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        if (record and output.is_file() and record["source_sha256"] == sha(source)
                and record["olean_sha256"] == sha(output)
                and all(x in done for x in deps[module])):
            done.add(module)
    receipt.update({"targets": targets, "own_import_closure_count": len(deps),
                    "status": "RUNNING", "strict_args": ["-j1", "-M2000", "-DwarningAsError=true"],
                    "full_project_replay": False})

    def save() -> None:
        temp = receipt_path.with_suffix(".tmp")
        temp.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n")
        temp.replace(receipt_path)

    def compile_module(module: str) -> tuple[str, dict, bool]:
        source = ROOT / (module.replace(".", "/") + ".lean")
        output = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        source_hash = sha(source)
        log = state / (module + ".log")
        started = time.monotonic()
        with log.open("w") as stream:
            completed = subprocess.run([args.lake, "env", "lean", "-j1", "-M2000",
                "-DwarningAsError=true", "-o", str(output), str(source)],
                cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, check=False)
        record = {"source_sha256": source_hash, "exit_code": completed.returncode,
                  "seconds": round(time.monotonic()-started, 2), "log": log.relative_to(ROOT).as_posix()}
        ok = completed.returncode == 0 and output.is_file() and sha(source) == source_hash
        if ok:
            record["olean_sha256"] = sha(output)
        else:
            record["source_changed_during_compile"] = sha(source) != source_hash
        return module, record, ok

    save()
    pending = [x for x in deps if x not in done]
    running = {}
    failed: set[str] = set()
    print(f"Own closure {len(deps)}; valid same-replay objects {len(done)}", flush=True)
    last_print = 0.0
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        while pending or running:
            ready = [x for x in pending if all(y in done for y in deps[x])]
            for module in ready[:args.workers-len(running)]:
                pending.remove(module)
                running[pool.submit(compile_module, module)] = module
            if not running:
                break
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                running.pop(future)
                module, record, ok = future.result()
                if ok:
                    done.add(module)
                    receipt["modules"][module] = record
                    receipt["failures"].pop(module, None)
                else:
                    failed.add(module)
                    receipt["failures"][module] = record
                    print(f"FAIL {module}: {record['log']}", flush=True)
            save()
            if time.monotonic()-last_print >= 30:
                print(f"PASS {len(done)}/{len(deps)}; failures {len(failed)}; active "
                      + ", ".join(running.values()), flush=True)
                last_print = time.monotonic()
    receipt["blocked_modules"] = pending
    receipt["status"] = "PASS" if len(done) == len(deps) else "FAILED_OR_BLOCKED"
    save()
    print(receipt["status"], flush=True)
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
