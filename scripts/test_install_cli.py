#!/usr/bin/env python3
"""Check installed commands outside the checkout and automatic Lake dependency discovery."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
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
        self.assertFalse(compiled.exists())
        source = project / "Properties.lean"
        source.write_text("import Blaster\nimport App\n"
                          "theorem fromProject : projectValue = 42 := by blaster\n")
        missing = self.run_report("check", source, "--no-build", expected=4)
        self.assertTrue(any("--no-build" in d["message"] for d in missing["diagnostics"]))
        self.assertFalse(compiled.exists())
        data = self.run_report("check", source)
        self.assertTrue(compiled.exists())
        self.assertEqual(data["results"][0]["property"], "fromProject")
        self.assertEqual(data["results"][0]["status"], "valid")
        # A stale import is refreshed, while the selected source is elaborated only once.
        (project / "App.lean").write_text("def projectValue : Nat := 43\n")
        marker = project / "selected-runs"
        source.write_text("import Blaster\nimport App\n"
                          "#eval show IO Unit from do\n"
                          f"  let path : System.FilePath := {json.dumps(str(marker))}\n"
                          "  let previous ← if ← path.pathExists then IO.FS.readFile path else pure \"\"\n"
                          "  IO.FS.writeFile path (previous ++ \"checked\\n\")\n"
                          "theorem fromProject : projectValue = 43 := by blaster\n")
        refreshed = self.run_report("check", source)
        self.assertEqual(refreshed["results"][0]["status"], "valid")
        self.assertEqual(marker.read_text(), "checked\n")
        (project / "lean-toolchain").write_text("leanprover/lean4:v0.0.0\n")
        error = self.run_report("check", source, expected=4)
        self.assertTrue(any("built with Lean" in d["message"] for d in error["diagnostics"]))

    def test_dependency_build_failure_preserves_json_and_explains_recovery(self):
        project = self.directory / "broken dependency project"
        project.mkdir()
        (project / "lakefile.toml").write_text('name = "broken"\n[[lean_lib]]\nname = "App"\n')
        (project / "lean-toolchain").write_text("leanprover/lean4:v4.24.0\n")
        (project / "App.lean").write_text("def broken : Nat := true\n")
        source = project / "Properties.lean"
        source.write_text("import Blaster\nimport App\n#blaster [True]\n")
        data = self.run_report("check", source, expected=4)
        self.assertTrue(any("couldn't prepare this file's imports" in d["message"] for d in data["diagnostics"]))

    def test_import_only_umbrella_checks_sources_once_and_build_logs_stay_quiet(self):
        project = self.directory / "umbrella project"
        project.mkdir()
        (project / "lakefile.toml").write_text('name = "umbrella"\n[[lean_lib]]\nname = "App"\n')
        (project / "lean-toolchain").write_text("leanprover/lean4:v4.24.0\n")
        (project / "App").mkdir()
        (project / "App/One.lean").write_text(
            'import Blaster\n#eval ("dependency marker" : String)\n'
            'def projectValue : Nat := 42\n'
            'theorem reflexive (n : Nat) : n = n := by blaster\n'
            '#blaster [True]\n')
        (project / "App/Two.lean").write_text('import Blaster\n#blaster [False]\n')
        (project / "App/Bundle.lean").write_text("import App.One\n")
        umbrella = project / "Umbrella.lean"
        umbrella.write_text("import App.Bundle\nimport App.One\nimport App.Two\nimport Lean\n-- suite entry point\n")
        compiled = project / ".lake/build/lib/lean/App/One.olean"
        data = self.run_report("check", umbrella, expected=1)
        self.assertEqual([r["status"] for r in data["results"]],
                         ["valid", "valid", "falsified"])
        self.assertEqual([r["invocation"] for r in data["results"]],
                         ["tactic", "command", "command"])
        self.assertEqual({Path(r["location"]["file"]).name for r in data["results"]},
                         {"One.lean", "Two.lean"})
        self.assertEqual(sum("dependency marker" in d["message"] for d in data["diagnostics"]), 1)
        self.assertFalse(any("I didn't check those imports" in d["message"]
                             for d in data["diagnostics"]))
        self.assertFalse(compiled.exists(), "The umbrella must not compile a leaf before checking it")

        (project / "App/Helper.lean").write_text(
            '#eval ("build marker" : String)\ndef helperValue : Nat := 42\n')
        source = project / "Properties.lean"
        source.write_text("import Blaster\nimport App.Helper\n#blaster [helperValue = 42]\n")
        helperCompiled = project / ".lake/build/lib/lean/App/Helper.olean"
        process = subprocess.run([str(self.command), "check", str(source)],
                                 cwd=self.directory, env=self.environment,
                                 text=True, capture_output=True, timeout=60)
        self.assertEqual(process.returncode, 0, process.stdout + process.stderr)
        self.assertTrue(helperCompiled.exists())
        self.assertIn("Valid", process.stdout)
        self.assertNotIn("build marker", process.stdout + process.stderr)

    @unittest.skipIf(os.name == "nt", "Uses POSIX process-group cancellation")
    def test_interrupt_during_dependency_build(self):
        project = self.directory / "interrupted dependency project"
        project.mkdir()
        (project / "lakefile.toml").write_text('name = "interrupted"\n[[lean_lib]]\nname = "App"\n')
        (project / "lean-toolchain").write_text("leanprover/lean4:v4.24.0\n")
        ready = project / "compiler-pid"
        (project / "App.lean").write_text(
            "#eval show IO Unit from do\n"
            '  let child ← IO.Process.output { cmd := "/bin/sh", args := #["-c", "echo $PPID"] }\n'
            f"  IO.FS.writeFile {json.dumps(str(ready))} child.stdout\n"
            "  IO.sleep 45000\n"
            "def projectValue : Nat := 42\n")
        source = project / "Properties.lean"
        source.write_text("import Blaster\nimport App\n#blaster [True]\n")
        process = subprocess.Popen([str(self.command), "check", str(source), "--json"],
                                   cwd=self.directory, env=self.environment, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        compiler_pid = None
        try:
            deadline = time.monotonic() + 15
            while time.monotonic() < deadline and process.poll() is None and not ready.exists():
                time.sleep(0.02)
            self.assertTrue(ready.exists(), "The dependency compiler didn't reach the interruption point")
            compiler_pid = int(ready.read_text())
            process.send_signal(signal.SIGINT)
            stdout, stderr = process.communicate(timeout=5)
            self.assertEqual(process.returncode, 130, stdout + stderr)
            self.assertTrue(json.loads(stdout)["interrupted"])
            # Grandchildren are reaped by the OS, asynchronously on macOS. The CLI
            # directly reaps Lake; give the compiler's exiting state a bounded window.
            deadline = time.monotonic() + 3
            status = ""
            while time.monotonic() < deadline:
                status = subprocess.run(["/bin/ps", "-o", "stat=", "-p", str(compiler_pid)],
                                        text=True, capture_output=True).stdout.strip()
                if not status or status.startswith("Z"):
                    break
                time.sleep(0.02)
            self.assertTrue(not status or status.startswith("Z"), status)
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate(timeout=5)
            if compiler_pid:
                try:
                    os.kill(compiler_pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass

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
