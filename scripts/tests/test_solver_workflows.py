"""Protect solver-aware cache prefixes without a YAML dependency in the test suite."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).parents[2]


class SolverWorkflowTests(unittest.TestCase):
    def read(self, name):
        return (ROOT / ".github/workflows" / name).read_text()

    def test_weekly_pins_only_blasters_upgrade(self):
        text = self.read("benchmark.yml")
        versions = dict(re.findall(
            r'tool: (\w+),[^\n]*z3_version: "([^"]+)"', text))
        self.assertEqual(versions, {"blaster": "5.4.0", "smt": "4.15.2",
                                   "hammer": "4.15.2", "auto": "4.15.2",
                                   "aesop": "none", "baselines": "none"})
        self.assertIn("Z3_VERSION: ${{ matrix.z3_version }}", text)

    def test_pr_and_nightly_follow_supported_blasters_version(self):
        for name in ["pr-benchmark.yml", "ci-nightly-build.yaml"]:
            with self.subTest(workflow=name):
                text = self.read(name)
                self.assertIn('Z3_VERSION: "5.4.0"', text)
                self.assertIn('verify_benchmark_solver.py "$Z3_VERSION"', text)

    def test_selected_blasters_release_meets_its_declared_minimum(self):
        source = (ROOT / "Blaster/Smt/Env.lean").read_text()
        minimum = re.search(r'minZ3Version\s*:\s*String\s*:=\s*"([0-9.]+)"', source).group(1)
        selected = re.search(r'tool: blaster,[^\n]*z3_version: "([^"]+)"',
                             self.read("benchmark.yml")).group(1)
        self.assertGreaterEqual(tuple(map(int, selected.split("."))),
                                tuple(map(int, minimum.split("."))))

    def test_every_cache_key_and_restore_prefix_is_solver_scoped(self):
        identity = "${{ steps.solver.outputs.solver_id }}"
        for name in ["benchmark.yml", "pr-benchmark.yml"]:
            text = self.read(name)
            blocks = re.findall(r"uses: actions/cache@v4\n(.*?)(?=\n      - name:|\Z)",
                                text, re.S)
            self.assertEqual(len(blocks), 1, name)
            key = re.search(r"^          key: (.+)$", blocks[0], re.M).group(1)
            restores = re.search(r"restore-keys: \|\n(.*)", blocks[0], re.S).group(1)
            prefixes = [line.strip() for line in restores.splitlines() if line.strip()]
            self.assertEqual(len(prefixes), 1, name)
            self.assertIn(identity, key)
            self.assertIn(identity, prefixes[0])
            self.assertTrue(key.startswith(prefixes[0]))
            # GitHub prefix restore must never fall back to an old solverless key.
            current = key.replace(identity, "z3-5.4.0")
            prefix = prefixes[0].replace(identity, "z3-5.4.0")
            self.assertTrue(current.startswith(prefix))
            self.assertFalse(key.replace(identity, "z3-4.15.2").startswith(prefix))
            self.assertFalse(key.replace(identity + "-", "").startswith(prefix))

    def test_preflight_precedes_cache_restore_and_identity_reaches_harness(self):
        for name in ["benchmark.yml", "pr-benchmark.yml"]:
            text = self.read(name)
            self.assertLess(text.index("name: Verify selected solver version"),
                            text.index("uses: actions/cache@v4"))
            self.assertIn("BENCH_SOLVER_ID: ${{ steps.solver.outputs.solver_id }}", text)
            self.assertIn('verify_benchmark_solver.py "$Z3_VERSION" >> "$GITHUB_OUTPUT"', text)

    def test_no_legacy_actions_cache_prefix_remains(self):
        self.assertNotIn("bench-v4-", self.read("benchmark.yml"))
        self.assertNotIn("pr-benchmark-v5-", self.read("pr-benchmark.yml"))

    def test_weekly_retains_solver_provenance_artifact(self):
        self.assertIn("solver_environment.json", self.read("benchmark.yml"))


if __name__ == "__main__":
    unittest.main()
