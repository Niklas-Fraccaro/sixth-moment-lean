"""Sequential hosted-runner build with commit-bound, checked checkpoints."""

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shlex
import shutil
import signal
import subprocess
import sys
import tarfile
import threading
import time
import urllib.request


ROOT = Path.cwd()
OUT = Path(os.environ["RUNNER_TEMP"]) / "lean-full"
OUT.mkdir(parents=True, exist_ok=True)
MODE = os.environ.get("BUILD_MODE", "full")
STAGE = int(os.environ.get("BUILD_STAGE", "1"))
LIMIT = 900 * 1024 * 1024
SCALE = Path(".lake/build/lib/lean/SixthMoment/Certificate/Scale.olean")
BOUNDS = Path(".lake/build/lib/lean/SixthMoment/Certificate/Bounds.olean")


def digest(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def output(**values):
    with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as stream:
        for key, value in values.items():
            stream.write(f"{key}={value}\n")


def identity():
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], check=True)
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    if commit != os.environ["GITHUB_SHA"]:
        raise RuntimeError("checkout differs from workflow commit")
    tracked = subprocess.check_output(["git", "ls-files", "-z"]).decode().split("\0")
    return {
        "commit": commit,
        "run": os.environ["GITHUB_RUN_ID"],
        "mode": MODE,
        "sources": {name: digest(name) for name in tracked if name},
        "lean": subprocess.check_output(["lean", "--version"], text=True).strip(),
        "compiler_sha256": json.loads((OUT / "compiler.json").read_text())["original_sha256"],
    }


def own_modules():
    names = subprocess.check_output(["git", "ls-files", "-z"], text=True).split("\0")
    return sorted(name[:-5] for name in names if name.endswith(".lean") and (
        name in {"SixthMoment.lean", "Salt.lean"} or
        name.startswith(("SixthMoment/", "Salt/"))))


def built_modules():
    base = Path(".lake/build/lib/lean")
    return [name for name in own_modules() if
            (base / (name + ".olean")).is_file() and
            (base / (name + ".trace")).is_file()]


def run(label, args, timeout=900, build_deadline=None, expected_error=False, stop_file=None):
    """A timed boundary stops the whole group, including waiting compilers."""
    print(f"$ {shlex.join(map(str, args))}", flush=True)
    started = time.monotonic()
    stopped = False
    failure = OUT / "compiler-failed"
    with (OUT / f"{label}.log").open("w", encoding="utf-8") as log:
        process = subprocess.Popen(list(map(str, args)), stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True,
                                   encoding="utf-8", errors="replace", start_new_session=True)

        def reader():
            for line in process.stdout:
                log.write(line)
                log.flush()
                print(line, end="", flush=True)

        thread = threading.Thread(target=reader, daemon=True)
        thread.start()
        next_report = time.monotonic() + 60
        try:
            while process.poll() is None:
                now = time.monotonic()
                if now >= next_report:
                    print(f"Progress: {len(built_modules())}/{len(own_modules())} modules; "
                          f"free disk {shutil.disk_usage(ROOT).free // (1024**2)} MiB",
                          flush=True)
                    next_report = now + 300
                if ((build_deadline is not None and time.time() >= build_deadline) or
                        (stop_file is not None and stop_file.exists())):
                    stopped = True
                    break
                if now - started > timeout:
                    raise TimeoutError(f"{label} exceeded {timeout}s")
                if build_deadline is not None and failure.exists():
                    # Let Lake flush the real error before terminating other work.
                    time.sleep(2)
                    raise RuntimeError("a Lean compiler failed; see build and compiler logs")
                time.sleep(0.25)
        finally:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            thread.join(timeout=10)
            if thread.is_alive():
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                thread.join(timeout=5)
                if thread.is_alive():
                    raise RuntimeError("a child process kept the output pipe open")
            process.stdout.close()
    if stopped:
        print("Time boundary reached; preserving completed work.", flush=True)
        return "paused"
    if process.returncode and not expected_error:
        raise RuntimeError(f"{label} failed with exit code {process.returncode}")
    return process.returncode


def install_wrapper(sysroot):
    """Wrap only this job's isolated toolchain; proof/compiler arguments stay intact."""
    binary = Path(sysroot) / "bin/lean"
    real = binary.with_name("lean-real")
    if real.exists():
        raise RuntimeError("compiler was already wrapped")
    original = digest(binary)
    binary.rename(real)
    wrapper = f"""#!/usr/bin/env bash
set -u
compile=0
for arg in "$@"; do
  if [[ "$arg" == "-o" ]]; then compile=1; fi
done
if [[ "$compile" == 0 ]]; then exec {shlex.quote(str(real))} "$@"; fi
exec 9>{shlex.quote(str(OUT / 'compiler.lock'))}
flock -x 9
if [[ -f {shlex.quote(str(OUT / 'compiler-failed'))} ]]; then exit 99; fi
printf 'START %s %s\\n' "$(date -u +%FT%TZ)" "$*" >> {shlex.quote(str(OUT / 'compiler.log'))}
{shlex.quote(str(real))} "$@"
result=$?
printf 'END %s %s\\n' "$(date -u +%FT%TZ)" "$result" >> {shlex.quote(str(OUT / 'compiler.log'))}
if [[ "$result" != 0 ]]; then printf '%s\\n' "$result" > {shlex.quote(str(OUT / 'compiler-failed'))}; fi
exit "$result"
"""
    binary.write_text(wrapper, encoding="utf-8")
    binary.chmod(0o755)
    write_json(OUT / "compiler.json", {"original_sha256": original,
                                      "wrapper_sha256": digest(binary),
                                      "maximum_simultaneous_compilers": 1})


def setup():
    if os.environ["GITHUB_REPOSITORY"] != "Niklas-Fraccaro/sixth-moment-lean":
        raise RuntimeError("this workflow is restricted to the authorized organization copy")
    archive = OUT / "elan.tar.gz"
    urllib.request.urlretrieve(
        "https://github.com/leanprover/elan/releases/download/v4.2.4/"
        "elan-x86_64-unknown-linux-gnu.tar.gz", archive)
    if digest(archive) != "42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63":
        raise RuntimeError("elan checksum mismatch")
    with tarfile.open(archive) as bundle:
        bundle.extractall(OUT / "installer", filter="data")
    elan_home = str(OUT / "elan-home")
    os.environ["ELAN_HOME"] = elan_home
    os.environ["PATH"] = elan_home + "/bin:" + os.environ["PATH"]
    with open(os.environ["GITHUB_ENV"], "a", encoding="utf-8") as stream:
        stream.write(f"ELAN_HOME={elan_home}\n")
    with open(os.environ["GITHUB_PATH"], "a", encoding="utf-8") as stream:
        stream.write(elan_home + "/bin\n")
    run("elan-install", [OUT / "installer/elan-init", "-y", "--no-modify-path",
                         "--default-toolchain", "none"])
    run("toolchain", ["elan", "toolchain", "install",
                      Path("lean-toolchain").read_text().strip()])
    sysroot = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    install_wrapper(sysroot)
    # Every external import is included; cache get recursively includes its imports.
    imports = set()
    for name in own_modules():
        for line in Path(name + ".lean").read_text(encoding="utf-8").splitlines():
            if line.startswith("import "):
                imports.update(x for x in line.split()[1:] if x.startswith("Mathlib"))
    if MODE == "smoke":
        imports = {"Mathlib.Data.Int.Basic", "Mathlib.Data.Rat.Cast.Order", "Mathlib.Tactic.NormNum"}
    run("mathlib-cache", ["lake", "exe", "cache", "get", *sorted(imports)], timeout=2100)
    (OUT / "compiler-failed").unlink(missing_ok=True)
    if built_modules():
        raise RuntimeError("setup unexpectedly restored project modules")
    write_json(OUT / "identity.json", identity())
    print(f"Fresh runner ready: {len(own_modules())} project modules, mode={MODE}", flush=True)


def snapshot(current, state):
    files = sorted(p for p in Path(".lake/build").rglob("*") if p.is_file())
    if any(p.is_symlink() for p in files):
        raise RuntimeError("unexpected symlink in build outputs")
    manifest = {"identity": current, "stage": STAGE, "state": state,
                "files": {p.as_posix(): digest(p) for p in files}}
    write_json(OUT / "checkpoint-manifest.json", manifest)
    tar_path = OUT / "checkpoint.tar"
    with tarfile.open(tar_path, "w") as bundle:
        for path in files:
            bundle.add(path, arcname=path.as_posix(), recursive=False)
        bundle.add(OUT / "checkpoint-manifest.json", arcname="checkpoint-manifest.json")
    archive = OUT / "checkpoint.tar.zst"
    run("compress", ["zstd", "-T2", "-3", "--rm", str(tar_path), "-o", str(archive)], timeout=900)
    if archive.stat().st_size > LIMIT:
        archive.unlink()
        raise RuntimeError("checkpoint exceeds 900 MiB safety limit; stopping before upload")
    output(sha256=digest(archive), state=state)
    print(f"Checkpoint: {archive.stat().st_size} bytes, {len(files)} files", flush=True)


def restore(current):
    archive = OUT / "checkpoint.tar.zst"
    if digest(archive) != os.environ["CHECKPOINT_SHA256"]:
        raise RuntimeError("checkpoint archive checksum mismatch")
    tar_path = OUT / "restore.tar"
    run("decompress", ["zstd", "-d", "--force", archive, "-o", tar_path], timeout=900)
    try:
        with tarfile.open(tar_path) as bundle:
            manifest = json.load(bundle.extractfile("checkpoint-manifest.json"))
            if manifest["identity"] != current:
                raise RuntimeError("checkpoint commit, run, sources, mode or toolchain mismatch")
            members = bundle.getmembers()
            names = [member.name for member in members]
            if len(names) != len(set(names)) or set(names) != set(manifest["files"]) | {"checkpoint-manifest.json"}:
                raise RuntimeError("checkpoint inventory mismatch")
            for member in members:
                path = PurePosixPath(member.name)
                if (not member.isfile() or path.is_absolute() or ".." in path.parts or
                        path.as_posix() != member.name):
                    raise RuntimeError("unsafe checkpoint member")
                if member.name == "checkpoint-manifest.json":
                    continue
                if not member.name.startswith(".lake/build/"):
                    raise RuntimeError("checkpoint member outside build directory")
                stream = bundle.extractfile(member)
                result = hashlib.sha256()
                for block in iter(lambda: stream.read(1024 * 1024), b""):
                    result.update(block)
                if result.hexdigest() != manifest["files"][member.name]:
                    raise RuntimeError("checkpoint file checksum mismatch")
            # Validation finishes before any build outputs are installed.
            for member in members:
                if member.name != "checkpoint-manifest.json":
                    bundle.extract(member, ROOT, filter="data")
    finally:
        tar_path.unlink(missing_ok=True)
    archive.unlink()
    print(f"Verified checkpoint restored: {len(built_modules())} completed project modules", flush=True)


def smoke(current):
    if STAGE == 1:
        run("build", ["lake", "--no-cache", "--no-ansi", "build", "+SixthMoment.Certificate.Scale"])
        if not SCALE.exists() or BOUNDS.exists():
            raise RuntimeError("unexpected smoke inventory")
        if "SixthMoment/Certificate/Scale.lean" not in (OUT / "compiler.log").read_text():
            raise RuntimeError("project compilation bypassed the compiler wrapper")
        bad = OUT / "ExpectedError.lean"
        bad.write_text("example : False := by decide\n", encoding="utf-8")
        if run("expected-error", ["lake", "env", "lean", "-j1", bad], expected_error=True) != 1:
            raise RuntimeError("negative error control failed")
        slow = OUT / "ExpectedTimeout.lean"
        ready = OUT / "ready"
        slow.write_text(f'#eval do\n  IO.FS.writeFile {json.dumps(str(ready))} "ready"\n  IO.sleep 60000\n', encoding="utf-8")
        # A separate timer starts only once Lean actually executes the fixture.
        def deadline_after_ready():
            deadline = time.monotonic() + 120
            while not ready.exists() and time.monotonic() < deadline:
                time.sleep(0.1)
            if ready.exists():
                time.sleep(2)
                (OUT / "timeout-trigger").touch()
        thread = threading.Thread(target=deadline_after_ready, daemon=True)
        thread.start()
        # Run the real Lean timeout through the same process-group boundary code.
        timer = OUT / "timeout-trigger"
        result = run("expected-timeout", ["lake", "env", "lean", "-j1", slow],
                     timeout=150, stop_file=timer)
        if result != "paused" or not ready.exists():
            raise RuntimeError("running-process timeout control failed")
        return "paused"
    stamp = (digest(SCALE), SCALE.stat().st_mtime_ns)
    run("reuse", ["lake", "--no-cache", "--no-ansi", "build", "+SixthMoment.Certificate.Scale"])
    if stamp != (digest(SCALE), SCALE.stat().st_mtime_ns):
        raise RuntimeError("restored module was unnecessarily rebuilt")
    if STAGE == 2:
        run("build", ["lake", "--no-cache", "--no-ansi", "build", "+SixthMoment.Certificate.Bounds"])
        return "paused"
    check = OUT / "MiniVerify.lean"
    check.write_text("import SixthMoment.Certificate.Bounds\n"
                     "example := SixthMoment.declaredBound_gt_41007\n"
                     "#print axioms SixthMoment.declaredBound_gt_41007\n", encoding="utf-8")
    run("verification", ["lake", "env", "lean", "-j1", "-M0", "-DwarningAsError=true", check])
    return "complete"


def build():
    current = identity()
    if current != json.loads((OUT / "identity.json").read_text()):
        raise RuntimeError("setup identity changed")
    state = "failed"
    started = time.time()
    try:
        if STAGE > 1:
            restore(current)
        if MODE == "smoke":
            result_state = smoke(current)
        else:
            deadline = float(os.environ["JOB_STARTED"]) + 285 * 60
            if time.time() + 60 >= deadline:
                raise RuntimeError("setup consumed the build time allowance")
            status = run("build", ["lake", "--no-cache", "--no-ansi", "build"],
                         timeout=285 * 60, build_deadline=deadline)
            if status == "paused":
                result_state = "paused"
            else:
                modules = own_modules()
                completed = built_modules()
                if completed != modules:
                    raise RuntimeError(f"incomplete module inventory: {len(completed)}/{len(modules)}")
                run("verification", ["lake", "env", "lean", "-j1", "-M0", "-DwarningAsError=true",
                                     "SixthMoment/Verification/Final.lean"], timeout=1200)
                result_state = "complete"
        if identity() != current:
            raise RuntimeError("tracked files changed during build")
        if STAGE == 1 and not (OUT / "compiler.log").exists():
            raise RuntimeError("compiler wrapper was not exercised")
        state = result_state
    finally:
        report = {"identity": current, "stage": STAGE, "state": state,
                  "attempt": int(os.environ.get("GITHUB_RUN_ATTEMPT", "1")),
                  "modules": len(built_modules()), "total_modules": len(own_modules()),
                  "elapsed_seconds": round(time.time() - started, 1),
                  "compiler": json.loads((OUT / "compiler.json").read_text())}
        write_json(OUT / f"stage-{STAGE}.json", report)
        if identity() != current:
            raise RuntimeError("identity changed; refusing to save checkpoint")
        snapshot(current, state)
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as stream:
            stream.write(f"Stage {STAGE}: **{state}**, {report['modules']}/{report['total_modules']} modules.\n\n"
                         f"Commit: `{current['commit']}`. Mode: `{MODE}`.\n")


def prune():
    old = os.environ.get("PREVIOUS_ARTIFACT", "")
    if not old:
        return
    if not old.isdigit():
        raise RuntimeError("invalid previous artifact ID")
    url = f"https://api.github.com/repos/{os.environ['GITHUB_REPOSITORY']}/actions/artifacts/{old}"
    headers = {"Authorization": "Bearer " + os.environ["GH_TOKEN"],
               "Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28"}
    with urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=60) as response:
        artifact = json.load(response)
    expected = f"full-checkpoint-{os.environ['GITHUB_RUN_ID']}-"
    if not artifact["name"].startswith(expected) or str(artifact["workflow_run"]["id"]) != os.environ["GITHUB_RUN_ID"]:
        raise RuntimeError("refusing to delete an artifact outside this run")
    with urllib.request.urlopen(urllib.request.Request(url, headers=headers, method="DELETE"), timeout=60):
        pass
    print(f"Previous checkpoint {old} removed after successful replacement upload", flush=True)


def report():
    reports = sorted(OUT.rglob("stage-*.json"))
    latest = {}
    for path in reports:
        item = json.loads(path.read_text())
        old = latest.get(item["stage"])
        if old is None or item["attempt"] > old["attempt"]:
            latest[item["stage"]] = item
    stages = list(latest.values())
    states = json.loads(os.environ["JOB_RESULTS"])
    if not stages or any(x not in {"success", "skipped"} for x in states):
        raise RuntimeError("one or more build stages failed; see retained diagnostics/checkpoints")
    if len(stages) != states.count("success"):
        raise RuntimeError("missing stage evidence")
    if any(x["state"] == "failed" for x in stages) or not any(x["state"] == "complete" for x in stages):
        raise RuntimeError("time allowance exhausted or build incomplete; checkpoint retained")
    if any(x["identity"] != stages[0]["identity"] for x in stages):
        raise RuntimeError("inconsistent stage identities")
    final = max(stages, key=lambda x: x["stage"])
    if final["state"] != "complete":
        raise RuntimeError("last segment did not complete verification")
    text = (f"{'Infrastructure smoke test' if MODE == 'smoke' else 'Full project build'} passed.\n\n"
            f"Commit: `{final['identity']['commit']}`\n\n"
            f"Project modules: {final['modules']}/{final['total_modules']}. "
            f"Completed stages: {len(stages)}.\n\n")
    if MODE == "full":
        text += ("Started without project artifacts; only pinned dependency caches were fetched. "
                 "Checkpoints stayed within this run and were verified before restore. "
                 "Final.lean passed with warnings as errors and its axiom guard. "
                 "The final theorem assumes DivisorProof.Watt41; this run does not prove that assumption.\n")
    else:
        text += "Two-module infrastructure test only; the full theorem was not built.\n"
    (OUT / "result.md").write_text(text, encoding="utf-8")
    with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as stream:
        stream.write(text)
    print(text, flush=True)


if __name__ == "__main__":
    commands = {"setup": setup, "build": build, "prune": prune, "report": report}
    if len(sys.argv) != 2 or sys.argv[1] not in commands:
        raise SystemExit("usage: lean-full.py setup|build|prune|report")
    commands[sys.argv[1]]()
