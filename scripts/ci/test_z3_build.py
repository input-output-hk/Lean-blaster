"""Test SHA selection, exact checkout and propagation of compiler failures."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().with_name('build-z3.sh')
SHA = 'a' * 40


class Z3BuildTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        bins = self.root / 'bin'
        bins.mkdir()
        commands = {
            'git': '#!/usr/bin/env bash\n'
                   'if [[ $1 == -C ]]; then shift 2; fi\n'
                   'case $1 in\n'
                   'ls-remote) printf "%s\\trefs/heads/master\\n" "${REMOTE_SHA:-' + SHA + '}" ;;\n'
                   'rev-parse) echo "${CHECKOUT_SHA:-' + SHA + '}" ;;\n'
                   'fetch) exit "${FETCH_STATUS:-0}" ;;\n'
                   'esac\n',
            'cmake': '#!/usr/bin/env bash\n'
                     'if [[ $1 == -S ]]; then\n'
                     '  [[ ${CONFIG_STATUS:-0} != 0 ]] && exit "$CONFIG_STATUS"\n'
                     '  for arg in "$@"; do\n'
                     '    if [[ $arg == -DCMAKE_INSTALL_PREFIX=* ]]; then\n'
                     '      prefix=${arg#*=}; mkdir -p "$prefix/bin"\n'
                     '      printf \'#!/bin/sh\\necho "Z3 master fixture"\\n\' > "$prefix/bin/z3"\n'
                     '      chmod +x "$prefix/bin/z3"\n'
                     '    fi\n'
                     '  done\n'
                     'elif [[ $1 == --build ]]; then exit "${BUILD_STATUS:-0}"; fi\n',
        }
        for name, content in commands.items():
            path = bins / name
            path.write_text(content)
            path.chmod(0o755)
        self.env = dict(os.environ, PATH=str(bins) + ':' + os.environ['PATH'],
                        Z3_WORK_DIR=str(self.root / 'work'),
                        GITHUB_ENV=str(self.root / 'github-env'),
                        GITHUB_PATH=str(self.root / 'github-path'))
        self.env.pop('Z3_COMMIT', None)

    def run_build(self, **env):
        return subprocess.run(['bash', str(SCRIPT)], cwd=self.root,
                              env=dict(self.env, **env), capture_output=True, text=True)

    def test_resolved_master_is_recorded(self):
        result = self.run_build()
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        evidence = self.root / '.ci-results'
        self.assertEqual(json.loads((evidence / 'z3-source.json').read_text())['source_commit'], SHA)
        self.assertTrue((evidence / 'z3-bin-path.txt').exists())
        self.assertEqual((self.root / 'github-env').read_text(), 'Z3_COMMIT=' + SHA + '\n')
        self.assertIn(str(self.root), (self.root / 'github-path').read_text())

    def test_invalid_revision_and_mismatched_checkout_fail(self):
        for env in [{'Z3_COMMIT': 'master'}, {'CHECKOUT_SHA': 'b' * 40}]:
            with self.subTest(env=env):
                self.assertNotEqual(self.run_build(**env).returncode, 0)

    def test_fetch_configure_and_build_failure_are_not_hidden(self):
        for variable in ['FETCH_STATUS', 'CONFIG_STATUS', 'BUILD_STATUS']:
            with self.subTest(variable=variable):
                self.assertNotEqual(self.run_build(**{variable: '17'}).returncode, 0)
                self.assertTrue((self.root / '.ci-results/z3-source.json').exists())

    def test_exact_revision_replay_does_not_follow_master(self):
        self.assertEqual(self.run_build(Z3_COMMIT=SHA, REMOTE_SHA='b' * 40).returncode, 0)


if __name__ == '__main__':
    unittest.main()
