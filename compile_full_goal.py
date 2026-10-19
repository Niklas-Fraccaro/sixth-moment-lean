#!/usr/bin/env python3
"""Strict stock-Lean replay of the F01/FullProof import closure.

Run in the pinned Lake environment:
  lake env python3 compile_full_goal.py Sechstmoment.Theorem
Independent compiler processes may run concurrently; all proof checking is
performed by the ordinary Lean kernel. No external proof worker is used.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse, hashlib, json, re, shutil, subprocess, sys, time

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from verify_project import lean_code

PINNED_LEAN_SHA256 = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
FLAGS = ['-j1', '-M2000', '-DwarningAsError=true']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory(targets):
    ordered, deps, seen = [], {}, set()
    def visit(module):
        if module in seen:
            return
        seen.add(module)
        source = ROOT / (module.replace('.', '/') + '.lean')
        if not source.is_file():
            raise FileNotFoundError(source)
        ds = [m for m in re.findall(r'^import\s+([A-Za-z0-9_.]+)',
              lean_code(source.read_text()), re.M)
              if (ROOT / (m.replace('.', '/') + '.lean')).is_file()]
        deps[module] = ds
        for dependency in ds:
            visit(dependency)
        ordered.append(module)
    for module in targets:
        visit(module)
    return ordered, deps

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('modules', nargs='+')
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--tag', default='strict_replay')
    ap.add_argument('--fresh', action='store_true')
    ap.add_argument('--memory-mb', type=int, default=2000,
                    help='Lean memory limit in MiB; 0 means no compiler memory limit')
    a = ap.parse_args()
    if not 0 <= a.memory_mb <= 65536:
        ap.error('--memory-mb must be between 0 and 65536')
    flags = [f'-M{a.memory_mb}' if flag.startswith('-M') else flag for flag in FLAGS]
    compiler = Path(shutil.which('lean') or '').resolve()
    if not compiler.is_file() or sha(compiler) != PINNED_LEAN_SHA256:
        raise RuntimeError('The official pinned Lean 4.34.0 compiler is required')
    version = subprocess.run([str(compiler), '--version'], check=True,
                             text=True, capture_output=True).stdout.strip()
    logdir = ROOT / 'verification_logs/full_goal' / a.tag
    logdir.mkdir(parents=True, exist_ok=True)
    objects = ROOT / '.lake/build/lib/lean'
    ordered, deps = inventory(a.modules)
    receipt = {'status': 'RUNNING', 'targets': a.modules, 'flags': flags,
               'fresh_requested': a.fresh,
               'compiler_version': version, 'compiler_sha256': sha(compiler),
               'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
               'own_import_closure': len(ordered), 'modules': {}}
    def save():
        p = logdir / 'receipt.json.tmp'
        p.write_text(json.dumps(receipt, indent=2) + '\n')
        p.replace(logdir / 'receipt.json')
    def compile_one(module):
        module_flags = flags + (["-Dlinter.style.haveILetI=false"]
                                if module.startswith("Salt.") else [])
        source = ROOT / (module.replace('.', '/') + '.lean')
        output = objects / (module.replace('.', '/') + '.olean')
        stamp = output.with_suffix('.f01-source.json')
        before = sha(source)
        hashes = {d: sha(objects / (d.replace('.', '/') + '.olean')) for d in deps[module]}
        expected = {'source_sha256': before, 'dependency_olean_sha256': hashes,
                    'compiler_sha256': PINNED_LEAN_SHA256, 'flags': module_flags}
        if not a.fresh and module not in a.modules and output.is_file() and stamp.is_file():
            previous = json.loads(stamp.read_text())
            if previous == {**expected, 'olean_sha256': sha(output)}:
                return module, {**previous, 'status': 'REUSED_CURRENT_RUN', 'exit_code': 0}
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(compiler), *module_flags, '-o', str(output), source.relative_to(ROOT).as_posix()]
        started = time.monotonic()
        proc = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        log = proc.stdout + proc.stderr
        (logdir / (module + '.log')).write_text(log)
        after = sha(source)
        ok = proc.returncode == 0 and before == after and output.is_file()
        result = {**expected, 'status': 'PASS' if ok else 'FAIL',
                  'exit_code': proc.returncode, 'source_unchanged': before == after,
                  'seconds': round(time.monotonic()-started, 3),
                  'compiler_output_sha256': hashlib.sha256(log.encode()).hexdigest()}
        if ok:
            result['olean_sha256'] = sha(output)
            stamp.write_text(json.dumps({**expected, 'olean_sha256': sha(output)}) + '\n')
        return module, result
    pending, running, done = list(ordered), {}, set()
    save()
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        while pending or running:
            ready = [m for m in pending if set(deps[m]) <= done]
            for m in ready[:a.workers-len(running)]:
                pending.remove(m)
                running[pool.submit(compile_one, m)] = m
            if not running:
                raise RuntimeError('Unresolved import dependencies')
            completed, _ = wait(running, return_when=FIRST_COMPLETED)
            failed = []
            for future in completed:
                module, result = future.result()
                running.pop(future)
                receipt['modules'][module] = result
                print(f"{len(receipt['modules'])}/{len(ordered)} {result['status']} {module}", flush=True)
                if result['status'] == 'FAIL':
                    failed.append(module)
                else:
                    done.add(module)
            save()
            if failed:
                receipt['status'] = 'FAIL'
                receipt['failed_modules'] = failed
                save()
                for module in failed:
                    print((logdir / (module + '.log')).read_text(), flush=True)
                return 1
    for module, result in receipt['modules'].items():
        source = ROOT / (module.replace('.', '/') + '.lean')
        output = objects / (module.replace('.', '/') + '.olean')
        if sha(source) != result['source_sha256'] or sha(output) != result['olean_sha256']:
            raise RuntimeError('Source or object changed after verification: ' + module)
    receipt['status'] = 'PASS'
    receipt['finished_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    save()
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
