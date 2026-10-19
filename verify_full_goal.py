#!/usr/bin/env python3
"""Verify the original F01/FullGoal witness and its complete import closure.

Usage with the pinned Lean/mathlib environment prepared:
  lake env python3 verify_full_goal.py --workers 4
Fresh source builds are recorded with hashes. Same-run reuse requires matching
source, dependency object, compiler and flag hashes; the final type/axiom gate
is always compiled again. This does not compile unrelated quantitative drafts.
"""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, sys
from verify_project import (audit_axioms, full_goal_boundary_checks, source_checks,
                            lean_code, production_paths, EXACT_FULL_PROOF_TYPE)

ROOT = Path(__file__).resolve().parent
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_declarations():
    """Stable public names audited after every structural reorganization."""
    names = json.loads((ROOT / 'full_goal_audited_names.json').read_text())
    if not names or len(names) != len(set(names)):
        raise ValueError('Invalid full-goal audit manifest')
    return names

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--fresh', action='store_true')
    ap.add_argument('--interfaces-only', action='store_true',
                    help='Check the changed Watt/source/certificate/final interfaces')
    ap.add_argument('--tag', default='verified_watt41')
    ap.add_argument('--memory-mb', type=int, default=2000,
                    help='Lean memory limit in MiB; 0 means no compiler memory limit')
    args = ap.parse_args()
    if not 1 <= args.workers <= 8:
        ap.error('--workers must be between 1 and 8')
    if not 0 <= args.memory_mb <= 65536:
        ap.error('--memory-mb must be between 0 and 65536')
    boundary = full_goal_boundary_checks(ROOT)
    scan = source_checks(production_paths(ROOT))
    target = 'Sechstmoment.Verification.Final'
    gate = ROOT / (target.replace('.', '/') + '.lean')
    if args.interfaces_only:
        names = audit_declarations()
    else:
        names = audit_declarations()
        declared = re.findall(r'^#print axioms (\S+)', lean_code(gate.read_text()), re.M)
        if names != declared:
            raise ValueError('The audit manifest does not match the source declaration inventory')
    command = [sys.executable, 'compile_full_goal.py', '--workers', str(args.workers),
               '--tag', args.tag, '--memory-mb', str(args.memory_mb)]
    if args.fresh:
        command.append('--fresh')
    command.append(target)
    subprocess.run(command, cwd=ROOT, check=True)
    logdir = ROOT / 'verification_logs/full_goal' / args.tag
    receipt = json.loads((logdir / 'receipt.json').read_text())
    if receipt['status'] != 'PASS':
        raise ValueError('The strict source replay is incomplete')
    if args.fresh and (not receipt.get('fresh_requested') or
            any(item['status'] != 'PASS' for item in receipt['modules'].values())):
        raise ValueError('Fresh verification requires recompiling every project module')
    auditlog = logdir / (target + '.log')
    audit = audit_axioms(auditlog.read_text(), names)
    result = {'status': 'PASS', 'F01_complete': True,
              'full_goal_complete_under_literature_inputs': True,
              'full_proof_term': 'Sechstmoment.fullProof',
              'exact_type': ' '.join(EXACT_FULL_PROOF_TYPE.split()),
              'literature_inputs': ['Watt 4.1'],
              'fixed_afe_proof': 'Sechstmoment.Source.bblrFixedAFE_proved',
              'fresh_source_replay': args.fresh,
              'interfaces_only': args.interfaces_only,
              'literal_type_gates': len(re.findall(r'^example\s*:', lean_code(gate.read_text()), re.M)), 'public_declarations': len(names),
              'own_import_closure': receipt['own_import_closure'],
              'strict_receipt': str((logdir / 'receipt.json').relative_to(ROOT)),
              'source_boundaries': boundary, 'source_scan': scan,
              'audit_source_sha256': digest(gate), 'audit_log_sha256': digest(auditlog),
              'axiom_audit': audit}
    (logdir / 'result.json').write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    print('F01 and FullGoal from Watt 4.1: PASS.')
    print(f"Explicit public-declaration axiom audit: PASS ({len(names)} declarations).")
    return 0

if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (RuntimeError, ValueError, OSError, subprocess.CalledProcessError) as error:
        print('FullGoal verification failed: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
