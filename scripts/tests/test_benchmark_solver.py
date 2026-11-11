import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "solver", Path(__file__).parents[1] / "verify_benchmark_solver.py")
SOLVER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SOLVER)


class SolverPreflightTests(unittest.TestCase):
    def test_exact_version_produces_cache_identity(self):
        for version in ["5.4.0", "4.15.2"]:
            with self.subTest(version=version), patch.object(
                    SOLVER.subprocess, "run", return_value=subprocess.CompletedProcess(
                        [], 0, f"Z3 version {version} - 64 bit\n", "")) as run:
                self.assertEqual(SOLVER.solver_id(version), f"z3-{version}")
                self.assertEqual(run.call_args.args[0], ["z3", "--version"])
                self.assertTrue(run.call_args.kwargs["check"])

    def test_wrong_version_is_rejected(self):
        with patch.object(SOLVER.subprocess, "run", return_value=subprocess.CompletedProcess(
                [], 0, "Z3 version 4.15.2 - 64 bit\n", "")):
            with self.assertRaisesRegex(ValueError, "Expected Z3 5.4.0, found 4.15.2"):
                SOLVER.solver_id("5.4.0")

    def test_unknown_or_multiline_output_is_rejected(self):
        for output in ["", "version 5.4.0", "Z3 version 5.4.0\nsolver_id=other"]:
            with self.subTest(output=output), patch.object(
                    SOLVER.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, output, "")):
                with self.assertRaises(ValueError):
                    SOLVER.solver_id("5.4.0")

    def test_missing_failed_or_timed_out_binary_is_rejected(self):
        for error in [FileNotFoundError(), subprocess.CalledProcessError(1, "z3"),
                      subprocess.TimeoutExpired("z3", 15)]:
            with self.subTest(error=error), patch.object(SOLVER.subprocess, "run", side_effect=error):
                with self.assertRaises(type(error)):
                    SOLVER.solver_id("5.4.0")

    def test_non_solver_tools_do_not_probe_z3(self):
        with patch.object(SOLVER.subprocess, "run") as run:
            self.assertEqual(SOLVER.solver_id("none"), "none")
            run.assert_not_called()

    def test_invalid_expected_version_is_rejected_before_probe(self):
        for version in ["", "master", "5.4", "5.4.0\nother=value"]:
            with self.subTest(version=version), patch.object(SOLVER.subprocess, "run") as run:
                with self.assertRaises(ValueError):
                    SOLVER.solver_id(version)
                run.assert_not_called()

    def test_cli_emits_only_verified_identity(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp) / "z3"
            binary.write_text("#!/bin/sh\nprintf 'Z3 version 5.4.0 - 64 bit\\n'\n")
            binary.chmod(0o755)
            env = dict(os.environ, PATH=tmp)
            result = subprocess.run([sys.executable, SPEC.origin, "5.4.0"],
                                    env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, "solver_id=z3-5.4.0\n")
            result = subprocess.run([sys.executable, SPEC.origin, "4.15.2"],
                                    env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)
            self.assertEqual(result.stdout, "")
            self.assertIn("Expected Z3 4.15.2, found 5.4.0", result.stderr)

    def test_cli_none_works_without_z3(self):
        result = subprocess.run([sys.executable, SPEC.origin, "none"],
                                env=dict(os.environ, PATH=""), capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "solver_id=none\n")


if __name__ == "__main__":
    unittest.main()
