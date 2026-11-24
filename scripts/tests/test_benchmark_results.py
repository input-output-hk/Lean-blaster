import csv
import importlib.util
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest

SPEC = importlib.util.spec_from_file_location(
    "validation", Path(__file__).parents[1] / "validate_benchmark_results.py")
VALIDATION = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VALIDATION)


class BenchmarkValidationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.results = Path(self.temp.name)
        (self.results / "smt").mkdir()
        self.manifest = self.results / "manifest.tsv"
        self.row = ["smt", "leanprover/lean4:v4.24.0", "main", "abc123456",
                    "smt +model", "OK"]
        self.write_manifest()
        self.csv_path = self.results / "smt" / "Example_results.csv"
        self.fields = ["Benchmark", "Theorem", "Statement", "smt +model_time", "smt +model_status"]
        self.result = ["Example", "simple", "True", "10", "OK"]
        self.write_csv()

    def write_manifest(self, rows=None):
        with self.manifest.open("w", newline="") as target:
            writer = csv.writer(target, delimiter="\t")
            writer.writerow(VALIDATION.MANIFEST_FIELDS)
            writer.writerows([self.row] if rows is None else rows)

    def write_csv(self, rows=None):
        with self.csv_path.open("w", newline="") as target:
            writer = csv.writer(target)
            writer.writerow(self.fields)
            writer.writerows([self.result] if rows is None else rows)

    def validate(self, suites=None):
        return VALIDATION.validate_tool(self.results, "smt", self.manifest,
                                       ["Example"] if suites is None else suites)

    def run_cli(self):
        suites = self.results / "suites.txt"
        suites.write_text("Example\n")
        return subprocess.run([sys.executable, str(Path(SPEC.origin)),
                               str(self.results), "smt", "--manifest", str(self.manifest),
                               "--suites", str(suites)], capture_output=True, text=True)

    def test_cli_returns_nonzero_for_failed_build(self):
        self.row[-1] = "BUILD_FAIL"
        self.write_manifest()
        result = self.run_cli()
        self.assertEqual(result.returncode, 1)
        self.assertIn("BUILD_FAIL", result.stderr)

    def test_cli_returns_zero_for_valid_results(self):
        result = self.run_cli()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Validated smt", result.stdout)

    def test_success_and_cache(self):
        self.validate()
        self.row[-1] = "CACHED"
        self.write_manifest()
        self.validate()

    def test_tactic_failures_are_valid_benchmark_outcomes(self):
        for status in VALIDATION.STATUSES:
            self.result[-1] = status
            self.write_csv()
            self.validate()

    def test_build_failure_is_not_a_result(self):
        for status in ["BUILD_FAIL", "SCAFFOLD_FAIL", "BENCH_FAIL"]:
            self.row[-1] = status
            self.write_manifest()
            with self.assertRaisesRegex(ValueError, status):
                self.validate()

    def test_empty_manifest(self):
        self.write_manifest([])
        with self.assertRaises(ValueError):
            self.validate()

    def test_other_tool_manifest(self):
        self.row[0] = "hammer"
        self.write_manifest()
        with self.assertRaises(ValueError):
            self.validate()

    def test_unresolved_version(self):
        self.row[3] = "?"
        self.write_manifest()
        with self.assertRaises(ValueError):
            self.validate()

    def test_missing_suite(self):
        with self.assertRaises(FileNotFoundError):
            self.validate(["Example", "Missing"])

    def test_empty_suite(self):
        self.write_csv([])
        with self.assertRaisesRegex(ValueError, "empty result"):
            self.validate()

    def test_duplicate_theorem(self):
        self.write_csv([self.result, self.result])
        with self.assertRaisesRegex(ValueError, "duplicate theorem"):
            self.validate()

    def test_missing_tactic_column(self):
        self.fields[-1] = "wrong_status"
        self.write_csv()
        with self.assertRaisesRegex(ValueError, "missing CSV columns"):
            self.validate()

    def test_invalid_status(self):
        self.result[-1] = "UNKNOWN"
        self.write_csv()
        with self.assertRaisesRegex(ValueError, "invalid result"):
            self.validate()

    def test_malformed_manifest_row(self):
        for row in [self.row[:-1], self.row + ["extra"]]:
            self.write_manifest([row])
            with self.assertRaisesRegex(ValueError, "malformed manifest"):
                self.validate()

    def test_malformed_csv_row(self):
        for row in [self.result[:-1], self.result + ["extra"]]:
            self.write_csv([row])
            with self.assertRaisesRegex(ValueError, "malformed CSV"):
                self.validate()

    def test_duplicate_csv_column(self):
        self.fields.append(self.fields[-1])
        self.result.append(self.result[-1])
        self.write_csv()
        with self.assertRaises(ValueError):
            self.validate()

    def test_multiple_tactics(self):
        (self.results / "smt").rename(self.results / "blaster")
        self.csv_path = self.results / "blaster" / "Example_results.csv"
        self.row[0] = "blaster"
        self.row[-2] = "blaster"
        other = self.row.copy()
        other[-2] = "blaster (only-optimize: 1)"
        self.write_manifest([self.row, other])
        self.fields[-2:] = ["blaster_time", "blaster_status"]
        self.fields += [other[-2] + "_time", other[-2] + "_status"]
        self.result += ["", "TIMEOUT"]
        self.write_csv()
        VALIDATION.validate_tool(self.results, "blaster", self.manifest, ["Example"])
        self.write_manifest([self.row])
        with self.assertRaisesRegex(ValueError, "incomplete.*tactic"):
            VALIDATION.validate_tool(self.results, "blaster", self.manifest, ["Example"])

    def test_missing_or_duplicate_suite_definitions(self):
        for suites in [[], ["Example", "Example"]]:
            with self.assertRaises(ValueError):
                self.validate(suites)


if __name__ == "__main__":
    unittest.main()
