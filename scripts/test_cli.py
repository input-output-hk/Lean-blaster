#!/usr/bin/env python3
"""Exercise the built CLI with real Lean elaboration and Z3 (no third-party packages)."""

import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time
import unittest
import unicodedata


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

    def test_interpreted_source_can_call_native_lean_functions(self):
        file = self.source('#eval do\n'
                           '  let bytes ← IO.getRandomBytes 16\n'
                           '  unless bytes.size == 16 do\n'
                           '    throw (IO.userError "unexpected random byte count")\n'
                           '#blaster [True]\n')
        data = self.report("check", file)
        self.assertEqual(data["results"][0]["status"], "valid")
        self.assertFalse(any(d["severity"] == "error" for d in data["diagnostics"]))

    @unittest.skipIf(os.name == "nt", "Uses a POSIX subprocess")
    def test_source_subprocess_stdout_cannot_pollute_json(self):
        file = self.source('#eval do\n'
                           '  let child ← IO.Process.spawn { cmd := "/bin/sh", args := #["-c", "echo child-output"] }\n'
                           '  discard child.wait\n#blaster [True]\n')
        process = self.invoke("check", file, "--json")
        self.assertEqual(process.returncode, 0, process.stdout + process.stderr)
        self.assertEqual(json.loads(process.stdout)["results"][0]["status"], "valid")
        self.assertNotIn("child-output", process.stdout)
        self.assertIn("child-output", process.stderr)

    def test_failed_tactic_accounts_for_remaining_selections(self):
        file = self.source("theorem wrong : False := by blaster\n"
                           "def other : Prop := ∀ a b : Nat, a + b = b + a\n")
        data = self.report("check", file, "--decl", "wrong", "--decl", "other", expected=4)
        self.assertEqual([(r["property"], r["status"]) for r in data["results"]],
                         [("wrong", "falsified"), ("other", "skipped")])
        self.assertIn("earlier errors", data["results"][1]["reason"])
        missing = self.report("check", file, "--decl", "wrong", "--decl", "missing", expected=4)
        self.assertTrue(any("couldn't find declaration 'missing'" in d["message"] for d in missing["diagnostics"]))

    def test_help_is_contextual_and_theme_is_explicit(self):
        doctor = self.invoke("doctor", "--help")
        self.assertEqual(doctor.returncode, 0)
        self.assertIn("--solver PATH", doctor.stdout)
        self.assertNotIn("--decl", doctor.stdout)
        self.assertNotIn("check Properties.lean", doctor.stdout)
        self.assertLess(len(self.invoke().stdout), 700)
        file = self.source("#blaster [True]\n")
        for theme, identity in [("dark", "196;181;253"), ("light", "109;40;217")]:
            process = self.invoke("check", file, "--color=always", "--theme", theme)
            self.assertEqual(process.returncode, 0)
            self.assertIn("\x1b[38;2;" + identity + "m", process.stdout)
        for background, identity in [("0;15", "109;40;217"), ("15;0", "196;181;253")]:
            environment = {**os.environ, "COLORTERM": "truecolor", "COLORFGBG": background}
            process = self.invoke("check", file, "--color=always", env=environment)
            self.assertIn("\x1b[38;2;" + identity + "m", process.stdout)
        environment = {**os.environ, "COLORTERM": "truecolor", "COLORFGBG": "15;235"}
        fallback = self.invoke("check", file, "--color=always", env=environment)
        self.assertNotIn("\x1b[38;2;", fallback.stdout)
        self.report("check", file, "--theme", "invalid", expected=2)

    def slow_solver(self, seconds=45):
        solver = self.directory / "slow z3"
        ready = self.directory / "solver-ready"
        pidfile = self.directory / "solver-pid"
        solver.write_text('''#!/usr/bin/env python3
import os, signal, sys, time
from pathlib import Path
if "-version" in sys.argv:
    print("Z3 version slow-regression")
    raise SystemExit(0)
signal.signal(signal.SIGTERM, signal.SIG_IGN)
Path(PIDFILE).write_text(str(os.getpid()))
command = ""
depth = 0
for line in sys.stdin:
    command += line
    depth += line.count("(") - line.count(")")
    if depth:
        continue
    text = command.strip()
    command = ""
    if text == "(check-sat)":
        Path(READYFILE).touch()
        time.sleep(SECONDS)
        print("unsat", flush=True)
    elif text == "(exit)":
        break
    elif text and not text.startswith("(set-simplifier "):
        print("success", flush=True)
'''.replace("PIDFILE", repr(str(pidfile))).replace("READYFILE", repr(str(ready))).replace("SECONDS", str(seconds)))
        solver.chmod(0o755)
        return solver, ready, pidfile

    def wait_until_ready(self, process, ready):
        deadline = time.monotonic() + 15
        while time.monotonic() < deadline and process.poll() is None:
            if ready.exists():
                return
            time.sleep(0.02)
        self.fail("The command didn't reach the interruption point")

    @unittest.skipIf(os.name == "nt", "Uses POSIX signal delivery")
    def test_interrupt_preserves_completed_results_and_reaps_solver(self):
        solver, ready, pidfile = self.slow_solver()
        file = self.source("#blaster [True]\n"
                           "#blaster [∀ a b c : Nat, a < b → b < c → a < c]\n")
        for interrupt in [signal.SIGINT, signal.SIGTERM]:
            with self.subTest(signal=interrupt):
                ready.unlink(missing_ok=True)
                process = subprocess.Popen([str(BINARY), "check", str(file), "--solver", str(solver), "--json"],
                                           cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                           start_new_session=True)
                solver_pid = None
                try:
                    self.wait_until_ready(process, ready)
                    solver_pid = int(pidfile.read_text())
                    process.send_signal(interrupt)
                    stdout, stderr = process.communicate(timeout=5)
                    self.assertEqual(process.returncode, 128 + interrupt, stdout + stderr)
                    data = json.loads(stdout)
                    self.assertTrue(data["interrupted"])
                    self.assertEqual(data["signal"], interrupt)
                    self.assertEqual(len(data["results"]), 1)
                    self.assertEqual(data["results"][0]["status"], "valid")
                    with self.assertRaises(ProcessLookupError):
                        os.kill(solver_pid, 0)
                finally:
                    if process.poll() is None:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.communicate(timeout=5)
                    if solver_pid:
                        try:
                            os.kill(solver_pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass

    @unittest.skipIf(os.name == "nt", "Uses POSIX signal delivery")
    def test_interrupt_during_blocking_source_io(self):
        ready = self.directory / "source-ready"
        file = self.source("#blaster [True]\n#eval do\n"
                           f"  IO.FS.writeFile {json.dumps(str(ready))} \"ready\"\n"
                           "  IO.sleep 45000\n")
        process = subprocess.Popen([str(BINARY), "check", str(file), "--json"], cwd=ROOT,
                                   text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   start_new_session=True)
        try:
            self.wait_until_ready(process, ready)
            process.send_signal(signal.SIGINT)
            stdout, stderr = process.communicate(timeout=5)
            self.assertEqual(process.returncode, 130, stdout + stderr)
            data = json.loads(stdout)
            self.assertTrue(data["interrupted"])
            self.assertEqual(len(data["results"]), 1)
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate(timeout=5)

    @unittest.skipIf(os.name == "nt", "Uses Unix terminal size reporting")
    def test_progress_uses_actual_terminal_width_and_display_cells(self):
        import fcntl
        import pty
        import re
        import select
        import struct
        import termios

        solver, _, _ = self.slow_solver(seconds=0.6)
        file = self.source("def «界界界界界界界界界界界界界界界界界界界界界界界界» : Prop :=\n"
                           "  ∀ a b c : Nat, a < b → b < c → a < c\n"
                           "#blaster [«界界界界界界界界界界界界界界界界界界界界界界界界»]\n")
        master, slave = pty.openpty()
        fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 20, 0, 0))
        environment = {**os.environ, "NO_COLOR": "1", "TERM": "xterm-256color"}
        environment.pop("COLUMNS", None)
        process = subprocess.Popen([str(BINARY), "check", str(file), "--solver", str(solver)],
                                   cwd=ROOT, env=environment, stdout=slave, stderr=slave,
                                   start_new_session=True)
        os.close(slave)
        output = bytearray()
        try:
            deadline = time.monotonic() + 15
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
            self.assertEqual(process.wait(timeout=3), 0, output.decode())
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            os.close(master)
        frames = [frame for frame in re.findall(r"\x1b\[2K([^\r\n]*)", output.decode()) if frame.startswith("  ◌")]
        self.assertTrue(frames)
        self.assertTrue(any("界" in frame for frame in frames), frames)
        for frame in frames:
            width = sum(0 if unicodedata.combining(c) else 2 if unicodedata.east_asian_width(c) in "WF" else 1 for c in frame)
            self.assertLessEqual(width, 19, repr(frame))

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
