#!/usr/bin/env python3
"""Check installed commands outside the checkout and automatic Lake dependency discovery."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent


class InstalledCli(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="installed blaster ")
        cls.directory = Path(cls.temp.name)
        cls.prefix = cls.directory / "installation with spaces"
        subprocess.run([sys.executable, str(ROOT / "scripts/install_cli.py"),
                        "--skip-build", "--prefix", str(cls.prefix)], cwd=ROOT,
                       check=True, stdout=subprocess.DEVNULL)
        cls.command = cls.prefix / "bin/lean-blaster"
        cls.sysroot = Path(json.loads((cls.prefix / "install.json").read_text())["leanSysroot"])
        # No Lean/Lake/Z3 binaries or project paths are inherited from the developer's shell.
        cls.environment = {key: value for key, value in os.environ.items()
                           if not key.startswith(("LEAN", "LAKE", "ELAN"))}
        cls.environment["PATH"] = "/usr/bin:/bin"

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def run_report(self, *args, expected=0):
        result = subprocess.run([str(self.command), *map(str, args), "--json"],
                                cwd=self.directory, env=self.environment,
                                text=True, capture_output=True, timeout=60)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return json.loads(result.stdout)

    def test_installed_doctor_finds_private_resources(self):
        data = self.run_report("doctor")
        self.assertEqual(data["solver"]["source"], "bundled")
        self.assertIn("5.3.2", data["solver"]["version"])
        self.assertIn(str(self.prefix), data["solver"]["path"])

    def test_standalone_file_without_lake_env_or_checkout(self):
        source = self.directory / "Standalone.lean"
        source.write_text("import Blaster\n"
                          "theorem reflexive (n : Nat) : n = n := by blaster\n"
                          "#blaster [∀ a b c : Nat, a < b → b < c → a < c]\n")
        data = self.run_report("check", source)
        self.assertEqual(len(data["results"]), 2)
        self.assertTrue(all(r["status"] == "valid" for r in data["results"]))

    def test_project_dependencies_discovered_from_input_location(self):
        project = self.directory / "a separate project"
        project.mkdir()
        (project / "lakefile.toml").write_text('name = "example"\n[[lean_lib]]\nname = "App"\n')
        (project / "lean-toolchain").write_text("leanprover/lean4:v4.24.0\n")
        (project / "App.lean").write_text("def projectValue : Nat := 42\n")
        compiled = project / ".lake/build/lib/lean/App.olean"
        compiled.parent.mkdir(parents=True)
        subprocess.run([str(self.sysroot / "bin/lean"), "App.lean", "-o", str(compiled)],
                       cwd=project, env=self.environment, check=True, capture_output=True)
        source = project / "Properties.lean"
        source.write_text("import Blaster\nimport App\n"
                          "theorem fromProject : projectValue = 42 := by blaster\n")
        data = self.run_report("check", source)
        self.assertEqual(data["results"][0]["property"], "fromProject")
        self.assertEqual(data["results"][0]["status"], "valid")
        (project / "lean-toolchain").write_text("leanprover/lean4:v0.0.0\n")
        error = self.run_report("check", source, expected=4)
        self.assertTrue(any("built with Lean" in d["message"] for d in error["diagnostics"]))

    def test_installer_preserves_unrelated_command(self):
        binary_dir = self.directory / "unrelated bin"
        binary_dir.mkdir()
        existing = binary_dir / "lean-blaster"
        existing.write_text("keep this command")
        result = subprocess.run([sys.executable, str(ROOT / "scripts/install_cli.py"),
                                 "--skip-build", "--prefix", str(self.prefix),
                                 "--bin-dir", str(binary_dir)], cwd=ROOT,
                                text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(existing.read_text(), "keep this command")


if __name__ == "__main__":
    unittest.main(verbosity=2)
