#!/usr/bin/env python3
"""Exercise the built CLI with real Lean elaboration and Z3 (no third-party packages)."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / ".lake/build/bin/lean-blaster"


class CliIntegration(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="blaster-cli-")
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)

    def source(self, text, filename="Properties.lean"):
        file = self.directory / filename
        file.write_text("import Blaster\n" + text)
        return file

    def invoke(self, *args, env=None):
        return subprocess.run([str(BINARY), *map(str, args)], cwd=ROOT,
                              text=True, capture_output=True, timeout=60, env=env)

    def report(self, *args, expected=0):
        process = self.invoke(*args, "--json")
        self.assertEqual(process.returncode, expected, process.stdout + process.stderr)
        data = json.loads(process.stdout)
        self.assertEqual(data["schemaVersion"], 1)
        self.assertNotIn("\x1b", process.stdout)
        return data

    def test_command_and_tactic_are_both_captured_once(self):
        file = self.source("theorem reflexive (n : Nat) : n = n := by blaster\n"
                           "#blaster [∀ a b c : Nat, a < b → b < c → a < c]\n")
        data = self.report("check", file)
        self.assertEqual(len(data["results"]), 2)
        self.assertEqual({r["invocation"] for r in data["results"]}, {"tactic", "command"})
        self.assertEqual({r["origin"] for r in data["results"]}, {"optimization", "smt"})
        tactic = next(r for r in data["results"] if r["invocation"] == "tactic")
        self.assertEqual(tactic["property"], "reflexive")
        self.assertEqual(tactic["location"]["line"], 2)
        self.assertIn("n", tactic["goal"])
        self.assertTrue(all(r["status"] == "valid" for r in data["results"]))
        self.assertIn("blasterProven", data["trust"])

    def test_selected_tactic_is_not_rerun(self):
        file = self.source("namespace Demo\n"
                           "theorem reflexive (n : Nat) : n = n := by blaster\n"
                           "#blaster [False]\nend Demo\n")
        data = self.report("--color=never", "check", file, "--decl=Demo.reflexive")
        self.assertEqual(len(data["results"]), 1)
        self.assertEqual(data["results"][0]["invocation"], "tactic")
        self.assertEqual(data["results"][0]["property"], "Demo.reflexive")

    def test_unselected_broken_proof_still_fails_elaboration(self):
        file = self.source("theorem good (n : Nat) : n = n := by blaster\n"
                           "theorem bad (a b : Nat) : a - b + b = a := by blaster\n")
        data = self.report("check", file, "--decl", "good", expected=4)
        self.assertEqual(len(data["results"]), 1)
        self.assertTrue(any(d["severity"] == "error" for d in data["diagnostics"]))

    def test_selected_property_without_tactic(self):
        file = self.source("def commutative : Prop := ∀ a b : Nat, a + b = b + a\n")
        data = self.report("check", file, "--decl", "commutative", "--solver-timeout=2m", "--seed", "0")
        self.assertEqual(data["results"][0]["invocation"], "declaration")
        self.assertEqual(data["results"][0]["solverTimeoutSeconds"], 120)
        self.assertEqual(data["results"][0]["location"]["line"], 2)

    def test_falsified_returns_counterexample(self):
        file = self.source("#blaster [∀ a b : Nat, a - b + b = a]\n")
        data = self.report("check", file, expected=1)
        self.assertEqual(data["results"][0]["status"], "falsified")
        self.assertTrue(data["results"][0]["counterexample"])
        without = self.report("check", file, "--no-counterexample", expected=1)
        self.assertEqual(without["results"][0]["counterexample"], [])

    def test_falsified_tactic_is_not_an_infrastructure_error(self):
        file = self.source("theorem wrong (a b : Nat) : a - b + b = a := by blaster\n")
        data = self.report("check", file, expected=1)
        self.assertEqual(data["results"][0]["invocation"], "tactic")
        self.assertEqual(data["results"][0]["status"], "falsified")

    def test_unknown_is_never_reported_as_valid(self):
        file = self.source("#blaster (only-optimize: 1) [∀ a b c : Nat, a < b → b < c → a < c]\n")
        data = self.report("check", file, expected=3)
        self.assertEqual(data["results"][0]["status"], "undetermined")
        self.assertIn("optimization", data["results"][0]["reason"])

    def test_solver_unknown_and_explicit_solver_failure(self):
        solver = self.directory / "fake z3"
        solver.write_text('''#!/usr/bin/env python3
import sys
if "-version" in sys.argv:
    print("Z3 version test-protocol")
    raise SystemExit(0)
command = ""
depth = 0
for line in sys.stdin:
    command += line
    depth += line.count("(") - line.count(")")
    if depth != 0:
        continue
    if command.strip() == "(exit)":
        break
    if not command.strip() or command.strip().startswith("(set-simplifier "):
        command = ""
        continue
    print("unknown" if command.strip() == "(check-sat)" else "success", flush=True)
    command = ""
''')
        solver.chmod(0o755)
        file = self.source("#blaster [∀ a b c : Nat, a < b → b < c → a < c]\n")
        data = self.report("check", file, "--solver", solver, "--solver-timeout", "1s", expected=3)
        self.assertEqual(data["results"][0]["origin"], "smt")
        self.assertEqual(data["results"][0]["status"], "undetermined")
        self.assertNotIn("reached", data["results"][0]["reason"])
        self.report("check", file, "--solver", self.directory / "missing", expected=4)

    def test_many_checks_are_not_lost(self):
        file = self.source("\n".join(f"#blaster [{i} = {i}]" for i in range(40)))
        data = self.report("check", file)
        self.assertEqual(len(data["results"]), 40)
        self.assertEqual(len({r["location"]["line"] for r in data["results"]}), 40)
        lines = [r["location"]["line"] for r in data["results"]]
        self.assertEqual(lines, sorted(lines))

    def test_literal_filename_after_option_terminator(self):
        file = self.source("#blaster [True]\n", "--json")
        sysroot = subprocess.check_output(["lake", "env", "lean", "--print-prefix"], cwd=ROOT, text=True).strip()
        process = subprocess.run([str(BINARY), "--json", "check", "--", file.name],
                                 cwd=self.directory, env={**os.environ, "LEAN_SYSROOT": sysroot},
                                 text=True, capture_output=True, timeout=60)
        self.assertEqual(process.returncode, 0, process.stdout + process.stderr)
        data = json.loads(process.stdout)
        self.assertEqual(data["results"][0]["status"], "valid")

    def test_source_stdout_cannot_pollute_json(self):
        file = self.source('#eval IO.println "source output"\n#blaster [True]\n')
        self.report("check", file)

    def test_no_checks_and_lean_errors_fail(self):
        empty = self.source("def answer := 42\n", "Empty.lean")
        self.report("check", empty, expected=4)
        broken = self.source("def broken : Nat := true\n#blaster [True]\n", "Broken.lean")
        self.report("check", broken, expected=4)
        self.report("check", self.directory / "Missing.lean", expected=4)

    def test_flags_are_validated_before_work(self):
        for flags in [("--timout", "30s"), ("--solver-timeout", "fast"),
                      ("--solver-timeout", "0s"), ("--color", "rainbow"),
                      ("--json", "--color", "always")]:
            self.report("check", "Missing.lean", *flags, expected=2)
        self.assertIn("--solver-timeout", self.invoke("check", "Missing.lean", "--timout").stderr)

    def test_doctor_uses_pinned_bundle_and_honors_override(self):
        doctor = self.report("doctor")
        self.assertEqual(doctor["solver"]["source"], "bundled")
        self.assertIn("5.3.2", doctor["solver"]["version"])
        self.report("doctor", "--solver", str(self.directory / "missing-z3"), expected=4)

    def test_pipe_and_ascii_modes_are_clean(self):
        file = self.source("#blaster [True]\n")
        process = self.invoke("check", file, "--ascii", "--no-progress")
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertIn("+ Valid", process.stdout)
        self.assertNotIn("\x1b", process.stdout + process.stderr)
        forced = self.invoke("check", file, "--color", "always", env={**os.environ, "NO_COLOR": "1"})
        self.assertIn("\x1b[", forced.stdout)

    @unittest.skipIf(os.name == "nt", "PTY behavior is checked on Unix terminals")
    def test_terminal_progress_and_no_color(self):
        import pty
        import select

        file = self.source("#blaster [True]\n")
        for extra in [[], ["--no-progress"]]:
            master, slave = pty.openpty()
            process = subprocess.Popen([str(BINARY), "check", str(file), *extra],
                                       cwd=ROOT, stdout=slave, stderr=slave,
                                       env={**os.environ, "NO_COLOR": "1", "TERM": "xterm-256color"})
            os.close(slave)
            output = bytearray()
            deadline = time.monotonic() + 30
            try:
                while time.monotonic() < deadline:
                    if select.select([master], [], [], 0.1)[0]:
                        try:
                            chunk = os.read(master, 65536)
                        except OSError:
                            break
                        if not chunk:
                            break
                        output.extend(chunk)
                    elif process.poll() is not None:
                        break
                self.assertEqual(process.wait(timeout=5), 0, output.decode())
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()
                os.close(master)
            self.assertNotIn(b"\x1b[32m", output)
            if extra:
                self.assertNotIn(b"\x1b[", output)
            else:
                self.assertIn(b"\r\x1b[2K", output)


if __name__ == "__main__":
    unittest.main(verbosity=2)
