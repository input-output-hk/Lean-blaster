#!/usr/bin/env python3
"""Check solver proxy protocol, timeout evidence and failure propagation."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

PROXY = Path(__file__).with_name('bounded_z3.py')


class BoundedZ3Tests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        real = self.root / 'real-z3'
        real.write_text('''#!/usr/bin/env python3
import os,sys,time
if '--version' in sys.argv:
    print('Z3 fixture version');sys.exit(0)
for line in sys.stdin:
    if 'check-sat' in line:
        if os.environ.get('FAKE_HANG'): time.sleep(30)
        print('sat',flush=True)
    elif '(exit)' in line: break
    else: print('success',flush=True)
sys.exit(int(os.environ.get('FAKE_EXIT','0')))
''')
        real.chmod(0o755)
        self.env = dict(os.environ, Z3_REAL_EXECUTABLE=str(real),
                        Z3_SOLVER_TIMEOUT_SECONDS='3',
                        Z3_QUERY_LOG_DIR=str(self.root / 'queries'))

    def run_proxy(self, *args, input=''):
        return subprocess.run(['python3', str(PROXY), *args], input=input, text=True,
                              capture_output=True, env=self.env, timeout=5)

    def test_protocol_and_exact_input_are_preserved(self):
        query = '(set-option :print-success true)\n(check-sat)\n(exit)\n'
        result = self.run_proxy('-in', '-smt2', input=query)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, 'success\nsat\n')
        self.assertEqual(next((self.root / 'queries').glob('*.smt2')).read_text(), query)
        report = json.loads(next((self.root / 'queries').glob('*.json')).read_text())
        self.assertFalse(report['timed_out'])

    def test_timeout_is_an_error_and_retains_query(self):
        self.env['FAKE_HANG'] = '1'
        self.env['Z3_SOLVER_TIMEOUT_SECONDS'] = '0.5'
        result = self.run_proxy('-in', input='(check-sat)\n')
        self.assertEqual(result.returncode, 124, result.stderr)
        self.assertIn('(error "CI Z3 wall deadline', result.stdout)
        self.assertNotIn('unknown', result.stdout)
        report = json.loads(next((self.root / 'queries').glob('*.json')).read_text())
        self.assertTrue(report['timed_out'])
        self.assertEqual(Path(report['input_file']).read_text(), '(check-sat)\n')

    def test_nonzero_exit_propagates(self):
        self.env['FAKE_EXIT'] = '37'
        self.assertEqual(self.run_proxy('-in', input='(exit)\n').returncode, 37)

    def test_version_is_transparent(self):
        result = self.run_proxy('--version')
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, 'Z3 fixture version\n')
        self.assertFalse((self.root / 'queries').exists())

    def test_invalid_limit_fails(self):
        for value in ['0','-1','nan','inf','invalid']:
            self.env['Z3_SOLVER_TIMEOUT_SECONDS'] = value
            self.assertNotEqual(self.run_proxy('-in').returncode, 0)


if __name__ == '__main__':
    unittest.main()
