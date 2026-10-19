"""Continuation integrity checks; mocked compilers test orchestration only."""
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
from verify_project import digest


class ContinuationIntegrityTests(unittest.TestCase):
    def fixture(self, root):
        own = root / 'Sechstmoment'
        own.mkdir()
        (root / 'Sechstmoment.lean').write_text('')
        (own / 'Base.lean').write_text('')
        (own / 'New.lean').write_text('import Sechstmoment.Base\n')
        (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.0\n')
        (root / 'extension_modules.json').write_text(json.dumps(['Sechstmoment.New']))
        (root / 'extension_theorems.json').write_text(json.dumps(['Sechstmoment.new_theorem']))
        obj = root / '.lake/build/lib/lean/Sechstmoment/Base.olean'
        obj.parent.mkdir(parents=True)
        obj.write_bytes(b'mock current-run object; no mathematical validity claimed')
        seed = {
            'extension_status': 'FAIL', 'reused_own_modules': False,
            'lean_toolchain': 'leanprover/lean4:v4.34.0', 'started_utc': 'test',
            'modules': {'Sechstmoment.Base': {
                'freshly_compiled': True, 'exit_code': 0,
                'source_sha256': digest(own / 'Base.lean'), 'olean_sha256': digest(obj)
            }}
        }
        text = json.dumps(seed)
        (root / 'extension_verification_receipt.json').write_text(text)
        logs = root / 'verification_logs/extensions'
        logs.mkdir(parents=True)
        (logs / 'failure.log').write_text('preserve prior rejected proof')
        return text, obj

    def invoke(self, root, fake_run):
        with (patch.object(extension, 'ROOT', root),
              patch.object(extension, 'source_checks', return_value={'source_scan': 'PASS'}),
              patch.object(extension.subprocess, 'run', fake_run),
              patch.object(sys, 'argv', ['verify_extensions.py', '--continue-current-run']),
              contextlib.redirect_stdout(io.StringIO()),
              contextlib.redirect_stderr(io.StringIO())):
            return extension.main()

    def test_only_hash_verified_current_run_objects_are_retained(self):
        with tempfile.TemporaryDirectory(dir=extension.ROOT) as temporary:
            root = Path(temporary)
            prior, _ = self.fixture(root)
            built = []

            def fake_run(command, **kwargs):
                if '--version' in command:
                    return subprocess.CompletedProcess(command, 0, 'Lean mock\n', '')
                if '-o' in command:
                    built.append(command[command.index('-o') - 1])
                    Path(command[command.index('-o') + 1]).write_bytes(b'fresh mock object')
                    return subprocess.CompletedProcess(command, 0)
                return subprocess.CompletedProcess(command, 0,
                    "'Sechstmoment.new_theorem' depends on axioms: [propext]\n", '')

            self.assertEqual(self.invoke(root, fake_run), 0)
            self.assertEqual(built, ['Sechstmoment/New.lean'])
            receipt = json.loads((root / 'extension_verification_receipt.json').read_text())
            self.assertEqual(receipt['extension_status'], 'PASS')
            self.assertEqual(set(receipt['modules']), {'Sechstmoment.Base', 'Sechstmoment.New'})
            continuation = receipt['fresh_replay_continuations'][-1]
            self.assertEqual(continuation['hash_verified_current_run_modules'], 1)
            self.assertEqual((root / continuation['prior_receipt']).read_text(), prior)

    def test_changed_source_or_object_rejects_before_compilation_and_preserves_evidence(self):
        for change in ('source', 'object'):
            with self.subTest(change=change), tempfile.TemporaryDirectory(dir=extension.ROOT) as temporary:
                root = Path(temporary)
                prior, obj = self.fixture(root)
                target = root / 'Sechstmoment/Base.lean' if change == 'source' else obj
                target.write_bytes(b'changed')

                def forbidden_run(*args, **kwargs):
                    self.fail('Hash rejection must precede any compiler call')

                self.assertEqual(self.invoke(root, forbidden_run), 1)
                receipt = json.loads((root / 'extension_verification_receipt.json').read_text())
                self.assertIn('Recorded fresh dependency changed', receipt['error'])
                history = root / 'history/current_replay_continuations'
                self.assertEqual(next(history.glob('receipt_*.json')).read_text(), prior)
                self.assertEqual(next(history.glob('logs_*/failure.log')).read_text(),
                                 'preserve prior rejected proof')

    def test_edits_during_compilation_or_audit_cannot_yield_pass(self):
        for phase in ('compile', 'audit'):
            with self.subTest(phase=phase), tempfile.TemporaryDirectory(dir=extension.ROOT) as temporary:
                root = Path(temporary)
                self.fixture(root)

                def fake_run(command, **kwargs):
                    if '--version' in command:
                        return subprocess.CompletedProcess(command, 0, 'Lean mock\n', '')
                    if '-o' in command:
                        Path(command[command.index('-o') + 1]).write_bytes(b'mock output')
                        if phase == 'compile':
                            (root / 'Sechstmoment/New.lean').write_text('-- edited while compiler ran\n')
                        return subprocess.CompletedProcess(command, 0)
                    (root / 'Sechstmoment/Base.lean').write_text('-- edited while audit ran\n')
                    return subprocess.CompletedProcess(command, 0,
                        "'Sechstmoment.new_theorem' depends on axioms: [propext]\n", '')

                self.assertEqual(self.invoke(root, fake_run), 1)
                receipt = json.loads((root / 'extension_verification_receipt.json').read_text())
                self.assertEqual(receipt['extension_status'], 'FAIL')
                self.assertIn('changed', receipt['error'])


if __name__ == '__main__':
    unittest.main()
