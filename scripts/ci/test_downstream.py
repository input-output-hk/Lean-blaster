import unittest
from prepare_downstream import full_sha, replace_dependency, verify_manifest

SHA = 'a' * 40


class DownstreamTests(unittest.TestCase):
    def test_exact_dependency_overlay(self):
        source = '  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "branch"\n'
        changed = replace_dependency(source, 'Blaster', 'input-output-hk/Lean-blaster', SHA)
        self.assertIn('@ "' + SHA + '"', changed)
        self.assertTrue(changed.startswith('  require'))

    def test_ambiguous_and_missing_dependencies_fail(self):
        line = 'require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "branch"\n'
        for source in ['', line + line, line.replace('Lean-blaster', 'another')]:
            with self.assertRaises(ValueError):
                replace_dependency(source, 'Blaster', 'input-output-hk/Lean-blaster', SHA)

    def test_invalid_inputs_are_rejected(self):
        for value in ['main', 'a' * 39, '$(id)', SHA + '\n']:
            with self.assertRaises(ValueError):
                full_sha(value)

    def test_resolved_manifest_must_match(self):
        verify_manifest({'packages': [{'name': 'Blaster', 'rev': SHA}]}, {'Blaster': SHA})
        for manifest in [{'packages': []}, {'packages': [{'name': 'Blaster', 'rev': 'b' * 40}]}]:
            with self.assertRaises(ValueError):
                verify_manifest(manifest, {'Blaster': SHA})


if __name__ == '__main__':
    unittest.main()
