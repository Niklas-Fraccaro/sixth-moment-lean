"""Small CI infrastructure check; never builds the full theorem."""

import hashlib
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import sys
import tarfile
import threading
import time
import urllib.request


ROOT = Path.cwd()
OUT = Path(os.environ["RUNNER_TEMP"]) / "lean-mini"
OUT.mkdir(parents=True, exist_ok=True)
SCALE = Path(".lake/build/lib/lean/SixthMoment/Certificate/Scale.olean")
BOUNDS = Path(".lake/build/lib/lean/SixthMoment/Certificate/Bounds.olean")
ELAN_VERSION = "v4.2.4"
ELAN_SHA256 = "42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63"


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(label, args, timeout=600, allow_failure=False, ready_file=None):
    """Capture output and terminate the entire process group on timeout."""
    print(f"$ {shlex.join(map(str, args))}", flush=True)
    with (OUT / f"{label}.log").open("w", encoding="utf-8") as log:
        process = subprocess.Popen(
            list(map(str, args)), stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding="utf-8", errors="replace", start_new_session=True,
        )
        def terminate_group():
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                return
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()

        def copy_output():
            for line in process.stdout:
                log.write(line)
                log.flush()
                print(line, end="", flush=True)

        reader = threading.Thread(target=copy_output, daemon=True)
        reader.start()
        try:
            if ready_file:
                deadline = time.monotonic() + 120
                while not ready_file.is_file():
                    if process.poll() is not None:
                        break
                    if time.monotonic() > deadline:
                        raise RuntimeError(f"{label}: readiness marker was not received")
                    time.sleep(0.1)
            code = process.wait(timeout=timeout)
        except BaseException:
            terminate_group()
            raise
        finally:
            reader.join(timeout=10)
            if reader.is_alive():
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                raise RuntimeError(f"{label}: a child process kept the output pipe open")
            process.stdout.close()
    if code and not allow_failure:
        raise RuntimeError(f"{label} failed with exit code {code}")
    return code


def identity():
    tracked = subprocess.check_output(["git", "ls-files", "-z"]).decode().split("\0")
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], check=True)
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    if commit != os.environ["GITHUB_SHA"]:
        raise RuntimeError("checkout does not match the workflow commit")
    return {
        "commit": commit,
        "run": os.environ["GITHUB_RUN_ID"],
        "attempt": os.environ["GITHUB_RUN_ATTEMPT"],
        "sources": {name: sha256(name) for name in tracked if name},
        "lean": subprocess.check_output(["lean", "--version"], text=True).strip(),
    }


def setup():
    archive = OUT / "elan.tar.gz"
    url = (f"https://github.com/leanprover/elan/releases/download/{ELAN_VERSION}/"
           "elan-x86_64-unknown-linux-gnu.tar.gz")
    urllib.request.urlretrieve(url, archive)
    if sha256(archive) != ELAN_SHA256:
        raise RuntimeError("elan download checksum mismatch")
    with tarfile.open(archive) as bundle:
        bundle.extractall(OUT / "elan", filter="data")
    run("elan-install", [OUT / "elan/elan-init", "-y", "--no-modify-path",
                         "--default-toolchain", "none"])
    bin_dir = str(Path.home() / ".elan/bin")
    os.environ["PATH"] = bin_dir + os.pathsep + os.environ["PATH"]
    with open(os.environ["GITHUB_PATH"], "a", encoding="utf-8") as output:
        output.write(bin_dir + "\n")
    run("toolchain", ["elan", "toolchain", "install",
                      Path("lean-toolchain").read_text().strip()])
    run("version", ["lean", "--version"])
    run("mathlib-cache", ["lake", "exe", "cache", "get", "Mathlib.Data.Int.Basic",
                          "Mathlib.Data.Rat.Cast.Order", "Mathlib.Tactic.NormNum"])
    identity()
    if SCALE.exists() or BOUNDS.exists():
        raise RuntimeError("setup unexpectedly restored project modules")


def checkpoint():
    before = identity()
    if SCALE.exists() or BOUNDS.exists():
        raise RuntimeError("mini build must start without project artifacts")
    run("build-first", ["lake", "--no-cache", "--no-ansi", "build",
                        "+SixthMoment.Certificate.Scale"])
    if not SCALE.is_file() or BOUNDS.exists():
        raise RuntimeError("unexpected first-stage module inventory")

    bad = OUT / "ExpectedError.lean"
    bad.write_text("example : False := by decide\n", encoding="utf-8")
    code = run("expected-error", ["lake", "env", "lean", "-j1", "-M0",
                                 "-DwarningAsError=true", bad], allow_failure=True)
    if code != 1 or "error:" not in (OUT / "expected-error.log").read_text():
        raise RuntimeError("negative control did not detect the intended Lean error")

    slow = OUT / "ExpectedTimeout.lean"
    ready = OUT / "timeout-ready"
    ready.unlink(missing_ok=True)
    slow.write_text(f'#eval do\n  IO.FS.writeFile {json.dumps(str(ready))} "ready"\n'
                    '  IO.sleep 60000\n', encoding="utf-8")
    try:
        run("expected-timeout", ["lake", "env", "lean", "-j1", "-M0", slow],
            timeout=2, ready_file=ready)
    except subprocess.TimeoutExpired:
        if not ready.is_file() or ready.read_text() != "ready":
            raise RuntimeError("timeout happened before the Lean control started")
        print("PASS: a running Lean process was stopped by the timeout", flush=True)
    else:
        raise RuntimeError("timeout control unexpectedly completed")

    if identity() != before:
        raise RuntimeError("sources or environment changed during the mini build")
    files = sorted(p for p in Path(".lake/build").rglob("*") if p.is_file())
    manifest = {"identity": before, "files": {p.as_posix(): sha256(p) for p in files}}
    manifest_file = OUT / "manifest.json"
    manifest_file.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    archive = OUT / "checkpoint.tar.gz"
    with tarfile.open(archive, "w:gz") as bundle:
        for path in files:
            if path.is_symlink():
                raise RuntimeError("unexpected symlink in build outputs")
            bundle.add(path, arcname=path.as_posix(), recursive=False)
        bundle.add(manifest_file, arcname="mini-manifest.json")
    if archive.stat().st_size > 25 * 1024 * 1024:
        raise RuntimeError("mini checkpoint exceeded its 25 MiB size limit")
    digest = sha256(archive)
    with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as output:
        output.write(f"sha256={digest}\n")
    print(f"PASS: checkpoint prepared, SHA256 {digest}", flush=True)


def restore(archive, expected_digest, current):
    if sha256(archive) != expected_digest:
        raise ValueError("checkpoint archive checksum mismatch")
    with tarfile.open(archive) as bundle:
        manifest = json.load(bundle.extractfile("mini-manifest.json"))
        if manifest["identity"] != current:
            raise ValueError("checkpoint commit, run, sources, or toolchain mismatch")
        expected = set(manifest["files"]) | {"mini-manifest.json"}
        names = [member.name for member in bundle.getmembers()]
        if len(names) != len(set(names)) or set(names) != expected:
            raise ValueError("checkpoint file inventory mismatch")
        for member in bundle.getmembers():
            name = member.name
            if not member.isfile() or ".." in Path(name).parts:
                raise ValueError("unexpected checkpoint member")
            if name != "mini-manifest.json":
                if not name.startswith(".lake/build/"):
                    raise ValueError("checkpoint path outside build directory")
                digest = hashlib.sha256(bundle.extractfile(member).read()).hexdigest()
                if digest != manifest["files"][name]:
                    raise ValueError("checkpoint file checksum mismatch")
        for member in bundle.getmembers():
            if member.name != "mini-manifest.json":
                bundle.extract(member, ROOT, filter="data")
    return manifest


def resume():
    current = identity()
    if SCALE.exists() or BOUNDS.exists():
        raise RuntimeError("resume must start on a fresh runner")
    archive = OUT / "checkpoint.tar.gz"
    digest = os.environ["CHECKPOINT_SHA256"]
    wrong = dict(current, commit="0" * 40)
    for expected_digest, expected_identity in [("0" * 64, current), (digest, wrong)]:
        try:
            restore(archive, expected_digest, expected_identity)
        except ValueError:
            pass
        else:
            raise RuntimeError("invalid checkpoint was accepted")
    print("PASS: wrong checksum and wrong commit were rejected", flush=True)
    manifest = restore(archive, digest, current)
    for path, expected in manifest["files"].items():
        if sha256(path) != expected:
            raise RuntimeError(f"restored file differs: {path}")
    stamp = (sha256(SCALE), SCALE.stat().st_mtime_ns)
    run("reuse-first", ["lake", "--no-cache", "--no-ansi", "--verbose", "build",
                       "+SixthMoment.Certificate.Scale"])
    if (sha256(SCALE), SCALE.stat().st_mtime_ns) != stamp:
        raise RuntimeError("restored first module was rebuilt")
    run("build-second", ["lake", "--no-cache", "--no-ansi", "build",
                         "+SixthMoment.Certificate.Bounds"])
    if not BOUNDS.is_file():
        raise RuntimeError("second module was not built")
    check = OUT / "MiniVerify.lean"
    check.write_text("import SixthMoment.Certificate.Bounds\n"
                     "example := SixthMoment.declaredBound_gt_41007\n"
                     "#print axioms SixthMoment.declaredBound_gt_41007\n", encoding="utf-8")
    run("verify-second", ["lake", "env", "lean", "-j1", "-M0",
                          "-DwarningAsError=true", check])
    if identity() != current:
        raise RuntimeError("sources or environment changed during resume")
    report = ("Mini infrastructure test passed.\n\n"
              f"Commit: `{current['commit']}`\n\n"
              "Built: `SixthMoment.Certificate.Scale` and `SixthMoment.Certificate.Bounds`.\n\n"
              "Passed: expected Lean error, running-process timeout, checkpoint SHA256, "
              "commit binding, cross-job restore, reuse without recompiling, final mini check.\n\n"
              "This is a two-module infrastructure test; the full theorem was not built.\n")
    (OUT / "result.log").write_text(report, encoding="utf-8")
    with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as output:
        output.write(report)
    print(report, flush=True)


if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in {"setup", "checkpoint", "resume"}:
        raise SystemExit("usage: lean-mini.py setup|checkpoint|resume")
    {"setup": setup, "checkpoint": checkpoint, "resume": resume}[sys.argv[1]]()
