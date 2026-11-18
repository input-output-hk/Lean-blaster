#!/usr/bin/env python3
"""Exercise the trusted issue-fix data boundary using disposable local Git repos."""

import contextlib
import copy
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


SOURCE = Path(__file__).resolve().parents[1] / ".github/agent-fix/bot.py"
SPEC = importlib.util.spec_from_file_location("agent_fix_bot", SOURCE)
bot = importlib.util.module_from_spec(SPEC)
with patch.object(sys, "dont_write_bytecode", True):
    SPEC.loader.exec_module(bot)


def profile():
    """Return a small repository contract independent of the host checkout."""
    return {
        "version": 1,
        "regression_path": "Tests/FixedIssues/Issue{issue}.lean",
        "umbrella_path": "Tests/FixedIssues.lean",
        "umbrella_import": "import Tests.FixedIssues.Issue{issue}",
        "editable_paths": ["Blaster/", "Tests/"],
        "production_paths": ["Blaster/"],
        "source_extensions": [".lean"],
        "max_files": 12,
        "max_changed_lines": 600,
        "original_start": "-- BEGIN ORIGINAL REPRODUCER",
        "original_end": "-- END ORIGINAL REPRODUCER",
        "original_prelude": "import Tests.Utils\n",
    }


def report():
    """Return one well-formed model report; patch validity is checked separately."""
    return {
        "status": "fixed",
        "title": "Normalize the underlying operation",
        "summary": "The operation now preserves its invariant.",
        "root_cause": "The baseline used an invalid comparison.",
        "generality": "Normalization applies to every input of this operation.",
        "regression_path": "Tests/FixedIssues/Issue7.lean",
        "tests": [{"command": "check original", "result": "passed", "evidence": "Patched regression passed."}],
        "limitations": [],
        "patch": "",
    }


class GitFixture(unittest.TestCase):
    """Keep each patch exercise isolated from other tests and the real checkout."""

    def setUp(self):
        self.folder = tempfile.TemporaryDirectory(prefix="agent-fix-test-")
        self.previous = Path.cwd()
        os.chdir(self.folder.name)
        self.addCleanup(self.folder.cleanup)
        self.addCleanup(os.chdir, self.previous)
        self.git("init", "-q")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.invalid")
        self.write(".gitignore", ".agent-fix/\n")
        self.write("Blaster/Core.lean", "def value := 0\n")
        self.write("Tests/FixedIssues.lean", "import Tests.FixedIssues.Existing\n")
        self.git("add", ".")
        self.git("commit", "-qm", "baseline")
        self.base = self.git("rev-parse", "HEAD").strip()
        self.snapshot = {"base_sha": self.base, "number": 7, "base_branch": "main"}
        self.contract = profile()

    def git(self, *args):
        result = subprocess.run(["git", "-c", "core.hooksPath=/dev/null", *args],
                                text=True, capture_output=True, check=True)
        return result.stdout

    def write(self, name, text):
        path = Path(name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def valid_changes(self):
        self.write("Blaster/Core.lean", "def value := 1\n")
        self.write("Tests/FixedIssues.lean", "import Tests.FixedIssues.Existing\nimport Tests.FixedIssues.Issue7\n")
        self.write("Tests/FixedIssues/Issue7.lean",
                   "import Tests.Utils\n"
                   "-- BEGIN ORIGINAL REPRODUCER\n"
                   "example : 1 = 1 := rfl\n"
                   "-- END ORIGINAL REPRODUCER\n"
                   "example : 2 = 2 := rfl\n")

    def exported_patch(self):
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream):
            bot.export_patch()
        return stream.getvalue()

    def reset(self):
        self.git("reset", "--hard", self.base)
        self.git("clean", "-fd")

    def apply(self, patch_text, contract=None):
        self.reset()
        value = report()
        value["patch"] = patch_text
        return bot.apply_patch(value, self.snapshot, contract or self.contract)

    def test_export_includes_untracked_regression_without_staging(self):
        self.valid_changes()
        patch_text = self.exported_patch()
        self.assertIn("diff --git a/Tests/FixedIssues/Issue7.lean", patch_text)
        self.assertIn("+example : 1 = 1 := rfl", patch_text)
        self.assertEqual(self.git("diff", "--cached"), "")

    def test_valid_patch_applies_and_extracts_only_original(self):
        self.valid_changes()
        regression, original = self.apply(self.exported_patch())
        self.assertEqual(regression, "Tests/FixedIssues/Issue7.lean")
        self.assertEqual(original, "import Tests.Utils\nexample : 1 = 1 := rfl\n")
        self.assertEqual(Path("Blaster/Core.lean").read_text(), "def value := 1\n")
        self.assertIn("Tests/FixedIssues/Issue7.lean", self.git("diff", "--cached", "--name-only"))

    def test_missing_umbrella_import_is_rejected(self):
        self.valid_changes()
        self.write("Tests/FixedIssues.lean", "import Tests.FixedIssues.Existing\n")
        with self.assertRaisesRegex(ValueError, "umbrella import"):
            self.apply(self.exported_patch())

    def test_nullable_umbrella_supports_automatic_test_discovery(self):
        self.valid_changes()
        self.write("Tests/FixedIssues.lean", "import Tests.FixedIssues.Existing\n")
        self.contract.update(umbrella_path=None, umbrella_import=None)
        regression, original = self.apply(self.exported_patch())
        self.assertEqual(regression, "Tests/FixedIssues/Issue7.lean")
        self.assertIn("example : 1 = 1 := rfl", original)
        self.assertNotIn("Tests/FixedIssues.lean", self.git("diff", "--cached", "--name-only"))

    def test_missing_original_regression_is_rejected(self):
        self.valid_changes()
        Path("Tests/FixedIssues/Issue7.lean").unlink()
        with self.assertRaisesRegex(ValueError, "original reproducer"):
            self.apply(self.exported_patch())

    def test_test_only_patch_is_rejected(self):
        self.valid_changes()
        self.write("Blaster/Core.lean", "def value := 0\n")
        with self.assertRaisesRegex(ValueError, "production code"):
            self.apply(self.exported_patch())

    def test_unrelated_path_is_rejected(self):
        self.valid_changes()
        self.write(".github/workflows/unrelated.yml", "name: changed\n")
        with self.assertRaisesRegex(ValueError, "outside the bug-fix scope"):
            self.apply(self.exported_patch())

    def test_hidden_source_path_is_rejected(self):
        self.valid_changes()
        self.write("Blaster/.hidden/Extra.lean", "def hidden := 1\n")
        with self.assertRaisesRegex(ValueError, "configured source files"):
            self.apply(self.exported_patch())

    def test_unconfigured_source_extension_is_rejected(self):
        self.valid_changes()
        self.write("Blaster/Unexpected.py", "print('unexpected')\n")
        with self.assertRaisesRegex(ValueError, "configured source files"):
            self.apply(self.exported_patch())

    def test_symlink_is_rejected(self):
        self.valid_changes()
        Path("Blaster/Linked.lean").symlink_to("Core.lean")
        with self.assertRaisesRegex(ValueError, "regular nonexecutable"):
            self.apply(self.exported_patch())

    def test_binary_patch_is_rejected(self):
        self.valid_changes()
        Path("Blaster/Core.lean").write_bytes(b"\x00\x01\x02\n")
        with self.assertRaisesRegex(ValueError, "Binary patches"):
            self.apply(self.exported_patch())

    def test_rename_is_rejected(self):
        self.valid_changes()
        self.git("mv", "Blaster/Core.lean", "Blaster/Renamed.lean")
        with self.assertRaisesRegex(ValueError, "only add or modify"):
            self.apply(self.exported_patch())

    def test_deletion_is_rejected(self):
        self.valid_changes()
        Path("Blaster/Core.lean").unlink()
        with self.assertRaisesRegex(ValueError, "only add or modify"):
            self.apply(self.exported_patch())

    def test_changed_line_limit_is_enforced(self):
        self.valid_changes()
        self.write("Blaster/Core.lean", "".join(f"def value{i} := {i}\n" for i in range(650)))
        with self.assertRaisesRegex(ValueError, "too large"):
            self.apply(self.exported_patch())

    def test_file_limit_is_enforced(self):
        self.valid_changes()
        for index in range(10):
            self.write(f"Blaster/Extra{index}.lean", f"def extra{index} := {index}\n")
        with self.assertRaisesRegex(ValueError, "Too many files"):
            self.apply(self.exported_patch())

    def test_export_refuses_patch_above_byte_limit(self):
        self.valid_changes()
        self.write("Blaster/Core.lean", "x" * bot.MAX_PATCH)
        with self.assertRaisesRegex(ValueError, "size limit"):
            self.exported_patch()

    def test_artifact_directory_must_not_be_tracked(self):
        self.write(".agent-fix/issue.json", "branch-owned snapshot\n")
        self.git("add", "-f", ".agent-fix/issue.json")
        with self.assertRaisesRegex(ValueError, "must not track"):
            bot.ensure_artifacts()
        self.assertEqual(Path(".agent-fix/issue.json").read_text(), "branch-owned snapshot\n")

    def test_artifact_directory_symlink_preserves_policy_file(self):
        self.write("trusted-policy/setup.sh", "policy contents must stay unchanged\n")
        Path(".agent-fix").symlink_to(Path("trusted-policy").resolve(), target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "must not be a symlink"):
            bot.ensure_artifacts()
        self.assertEqual(Path("trusted-policy/setup.sh").read_text(), "policy contents must stay unchanged\n")

    def test_initialize_rejects_snapshot_symlink_before_overwriting_policy(self):
        self.write("trusted-policy/setup.sh", "policy contents must stay unchanged\n")
        Path(".agent-fix").mkdir()
        Path(".agent-fix/issue.json").symlink_to(Path("trusted-policy/setup.sh").resolve())
        snapshot = dict(self.snapshot, branch="codex/issue-7", title="$(untrusted issue text)")
        with patch.dict(os.environ, {"ISSUE_SNAPSHOT": json.dumps(snapshot)}), \
                self.assertRaisesRegex(ValueError, "without links"):
            bot.initialize()
        self.assertEqual(Path("trusted-policy/setup.sh").read_text(), "policy contents must stay unchanged\n")

    def test_artifact_special_file_is_rejected_without_opening_it(self):
        Path(".agent-fix").mkdir()
        os.mkfifo(".agent-fix/setup.log")
        with self.assertRaisesRegex(ValueError, "ordinary files"):
            bot.ensure_artifacts()

    def test_artifact_hardlink_is_rejected_without_truncating_policy(self):
        self.write("trusted-policy/setup.sh", "policy contents must stay unchanged\n")
        Path(".agent-fix").mkdir()
        os.link("trusted-policy/setup.sh", ".agent-fix/setup.log")
        with self.assertRaisesRegex(ValueError, "without links"):
            bot.write_artifact("setup.log", "replacement")
        self.assertEqual(Path("trusted-policy/setup.sh").read_text(), "policy contents must stay unchanged\n")

    def test_artifact_open_defends_against_links_appearing_after_directory_check(self):
        self.write("trusted-policy/setup.sh", "policy contents must stay unchanged\n")
        folder = bot.ensure_artifacts()
        artifact = folder / "issue.json"
        for kind in ("symlink", "hardlink"):
            with self.subTest(kind=kind):
                if kind == "symlink":
                    artifact.symlink_to(Path("trusted-policy/setup.sh").resolve())
                else:
                    os.link("trusted-policy/setup.sh", artifact)
                with patch.object(bot, "ensure_artifacts", return_value=folder), self.assertRaises((ValueError, OSError)):
                    bot.write_artifact("issue.json", "replacement")
                self.assertEqual(Path("trusted-policy/setup.sh").read_text(), "policy contents must stay unchanged\n")
                artifact.unlink()

    def test_setup_log_symlink_is_rejected_before_starting_command(self):
        self.write("trusted-policy/setup.sh", "policy contents must stay unchanged\n")
        Path(".agent-fix").mkdir()
        Path(".agent-fix/setup.log").symlink_to(Path("trusted-policy/setup.sh").resolve())
        with patch.object(bot, "git", return_value=subprocess.CompletedProcess([], 0, stdout="")), \
                patch.object(bot.subprocess, "Popen", side_effect=AssertionError("Command must not start")), \
                self.assertRaisesRegex(ValueError, "without links"):
            bot.run_check("setup", "this command must never execute", 1, trusted_setup=True)
        self.assertEqual(Path("trusted-policy/setup.sh").read_text(), "policy contents must stay unchanged\n")

    def test_export_excludes_artifacts_even_when_git_ignore_is_removed(self):
        self.valid_changes()
        self.write(".gitignore", "")
        self.write(".agent-fix/private.txt", "private artifact contents\n")
        self.assertIn(".agent-fix/private.txt", self.git("ls-files", "--others", "--exclude-standard"))
        patch_text = self.exported_patch()
        self.assertIn("+def value := 1", patch_text)
        self.assertNotIn("private artifact contents", patch_text)
        self.assertNotIn(".agent-fix/private.txt", patch_text)

    def test_validate_replays_original_and_reports_both_full_suite_failures(self):
        """Use Python in fixture sources to verify the pipeline without a Lean installation."""
        executable = shlex.quote(sys.executable)
        full_check = ("import runpy; value = runpy.run_path('Blaster/Core.lean')['value']; "
                      "print('baseline unrelated failure' if value == 0 else 'patched different failure'); "
                      "raise SystemExit(3)")
        self.contract.update({
            "original_start": "# BEGIN ORIGINAL REPRODUCER",
            "original_end": "# END ORIGINAL REPRODUCER",
            "original_prelude": "import runpy\n",
            "prepare_command": "true",
            "original_command": f"{executable} {{original}}",
            "regression_command": f"{executable} {{regression}}",
            "full_test_command": f"{executable} -c {shlex.quote(full_check)}",
            "command_timeout_seconds": 5,
        })
        self.write("Blaster/Core.lean", "value = 0\n")
        self.write(".github/agent-fix/config.json", json.dumps(self.contract))
        self.git("add", ".")
        self.git("commit", "-qm", "fixture runner contract")
        self.base = self.git("rev-parse", "HEAD").strip()
        self.snapshot.update(base_sha=self.base, branch="codex/issue-7")
        self.write("Blaster/Core.lean", "value = 1\n")
        self.write("Tests/FixedIssues.lean", "import Tests.FixedIssues.Existing\nimport Tests.FixedIssues.Issue7\n")
        self.write("Tests/FixedIssues/Issue7.lean",
                   "import runpy\n"
                   "# BEGIN ORIGINAL REPRODUCER\n"
                   "observed = runpy.run_path('Blaster/Core.lean')['value']\n"
                   "assert observed == 1, f'reported operation returned {observed}, expected 1'\n"
                   "# END ORIGINAL REPRODUCER\n"
                   "assert observed + 1 == 2, 'variant failed'\n")
        value = report()
        value["patch"] = self.exported_patch()
        value["tests"][0]["command"] = "touch .agent-fix/MODEL_COMMAND_EXECUTED"
        self.reset()
        environment = {
            "ISSUE_SNAPSHOT": json.dumps(self.snapshot),
            "MODEL_REPORT": json.dumps(value),
            "GITHUB_OUTPUT": str(Path.cwd() / ".agent-fix/job-output"),
            "AGENT_FIX_POLICY_ROOT": str(Path.cwd()),
        }
        with patch.dict(os.environ, environment), contextlib.redirect_stdout(io.StringIO()), \
                patch.object(bot, "api", side_effect=AssertionError("Validation cannot call GitHub")):
            bot.validate()
        output = Path(".agent-fix/job-output").read_text()
        self.assertTrue(output.startswith("checks="))
        checks = json.loads(output.removeprefix("checks="))
        self.assertEqual(checks["original_base"]["exit_code"], 1)
        self.assertIn("reported operation returned 0, expected 1", checks["original_base"]["tail"])
        self.assertEqual(checks["original_fixed"]["exit_code"], 0)
        self.assertEqual(checks["regression_fixed"]["exit_code"], 0)
        self.assertEqual(checks["full_base"]["exit_code"], 3)
        self.assertEqual(checks["full_fixed"]["exit_code"], 3)
        self.assertIn("baseline unrelated failure", checks["full_base"]["tail"])
        self.assertIn("patched different failure", checks["full_fixed"]["tail"])
        self.assertNotIn("variant failed", Path(".agent-fix/original.lean").read_text())
        self.assertFalse(Path(".agent-fix/MODEL_COMMAND_EXECUTED").exists())
        description = bot.render_pr(self.snapshot, value, checks, "https://example.invalid/run")
        self.assertIn("**Full validation failed.**", description)
        self.assertIn("baseline unrelated failure", description)
        self.assertIn("patched different failure", description)

    def publication_fixture(self):
        """Prepare local publication data; callers must mock the API and every push."""
        self.write(".github/agent-fix/config.json", json.dumps(self.contract))
        self.git("add", ".")
        self.git("commit", "-qm", "fixture publication contract")
        self.base = self.git("rev-parse", "HEAD").strip()
        issue = {"state": "open", "title": "Reported bug", "body": "A fenced reproducer.\n```lean\nexample\n```",
                 "labels": [{"name": "agent:fix"}]}
        self.snapshot.update(base_sha=self.base, branch="codex/issue-7", repository="example/project",
                             base_branch="release/fixes", fingerprint=bot.fingerprint(issue), label_triggered=True)
        self.valid_changes()
        value = report()
        value["patch"] = self.exported_patch()
        value["tests"][0]["command"] = "touch .agent-fix/REPORT_COMMAND_EXECUTED"
        self.reset()
        checks = {
            name: {"command": f"trusted {name}", "exit_code": code, "tail": "reported original failure" if code else "passed"}
            for name, code in (("original_base", 1), ("original_fixed", 0), ("regression_fixed", 0),
                               ("full_base", 0), ("full_fixed", 0))
        }
        environment = {
            "ISSUE_SNAPSHOT": json.dumps(self.snapshot), "MODEL_REPORT": json.dumps(value),
            "VALIDATION_CHECKS": json.dumps(checks), "GITHUB_ACTOR": "maintainer",
            "GITHUB_TRIGGERING_ACTOR": "maintainer", "GITHUB_RUN_ID": "1234", "GH_TOKEN": "fixture-only",
            "AGENT_FIX_POLICY_ROOT": str(Path.cwd()),
        }
        return issue, environment

    def test_publish_denied_actor_stops_before_issue_or_git_operations(self):
        _, environment = self.publication_fixture()
        with patch.dict(os.environ, environment), \
                patch.object(bot, "api", return_value={"permission": "read"}) as api_mock, \
                patch.object(bot, "git", side_effect=AssertionError("Denied actor must not reach Git")), \
                self.assertRaisesRegex(ValueError, "write permission"):
            bot.publish()
        self.assertEqual(api_mock.call_count, 1)
        self.assertEqual(api_mock.call_args.args[1], "collaborators/maintainer/permission")

    def test_publish_issue_drift_stops_before_patch_or_publication(self):
        issue, environment = self.publication_fixture()
        issue["body"] += "\nChanged after the snapshot."
        calls = []

        def fake_api(repository, endpoint, method="GET", data=None):
            calls.append((endpoint, method))
            if endpoint == "collaborators/maintainer/permission":
                return {"permission": "write"}
            if endpoint == "issues/7" and method == "GET":
                return issue
            self.fail(f"Issue drift reached unexpected API operation: {endpoint}")

        with patch.dict(os.environ, environment), patch.object(bot, "api", side_effect=fake_api), \
                patch.object(bot, "git", side_effect=AssertionError("Changed issue must not reach Git")), \
                self.assertRaisesRegex(ValueError, "Issue changed"):
            bot.publish()
        self.assertEqual(calls, [("collaborators/maintainer/permission", "GET"), ("issues/7", "GET")])

    def exercise_successful_publication(self, existing_branch=False):
        """Use real patch application/commit with a fake API and an intercepted push."""
        issue, environment = self.publication_fixture()
        calls, pushes = [], []
        real_git = bot.git

        def fake_git(*args, **kwargs):
            if args[0] == "push":
                pushes.append(args)
                return subprocess.CompletedProcess(args, 0, stdout="", stderr="")
            return real_git(*args, **kwargs)

        def fake_api(repository, endpoint, method="GET", data=None):
            self.assertEqual(repository, "example/project")
            calls.append((endpoint, method, data))
            if endpoint == "collaborators/maintainer/permission":
                return {"permission": "write"}
            if endpoint == "issues/7" and method == "GET":
                return issue
            if endpoint.startswith("pulls?"):
                return []
            if endpoint == "git/matching-refs/heads/codex/issue-7":
                return [{"ref": "refs/heads/codex/issue-7", "object": {"sha": "a" * 40}}] if existing_branch else []
            if endpoint == "git/commits/" + "a" * 40:
                return {"message": "Previous attempt\n\nagent-fix-run: 1234",
                        "tree": {"sha": self.git("rev-parse", "HEAD^{tree}").strip()}}
            if endpoint == "pulls" and method == "POST":
                return {"html_url": "https://example.invalid/pull/9"}
            if endpoint == "issues/7/comments" and method == "POST":
                return {}
            self.fail(f"Unexpected API operation: {method} {endpoint}")

        with patch.dict(os.environ, environment), patch.object(bot, "api", side_effect=fake_api), \
                patch.object(bot, "git", side_effect=fake_git), contextlib.redirect_stdout(io.StringIO()), \
                patch.object(bot, "run_check", side_effect=AssertionError("Publisher cannot run generated code")):
            bot.publish()
        self.assertFalse(Path(".agent-fix/REPORT_COMMAND_EXECUTED").exists())
        self.assertNotEqual(self.git("rev-parse", "HEAD").strip(), self.base)
        posts = [data for endpoint, method, data in calls if endpoint == "pulls" and method == "POST"]
        self.assertEqual(len(posts), 1)
        self.assertIs(posts[0]["draft"], True)
        self.assertEqual(posts[0]["base"], "release/fixes")
        self.assertEqual(posts[0]["head"], "codex/issue-7")
        return pushes

    def test_publish_creates_draft_on_selected_base_without_running_model_commands(self):
        pushes = self.exercise_successful_publication()
        self.assertEqual(pushes, [("push", "origin", "HEAD:refs/heads/codex/issue-7")])

    def test_publish_same_run_branch_retry_skips_push(self):
        self.assertEqual(self.exercise_successful_publication(existing_branch=True), [])


class ReportTests(unittest.TestCase):
    def validate(self, value, **kwargs):
        return bot.validate_report(json.dumps(value, **kwargs))

    def test_valid_report_is_preserved(self):
        value = report()
        self.assertEqual(self.validate(value), value)

    def test_total_report_byte_boundary(self):
        raw = json.dumps(report())
        raw += " " * (bot.MAX_REPORT - len(raw.encode()))
        self.assertEqual(len(raw.encode()), bot.MAX_REPORT)
        bot.validate_report(raw)
        with self.assertRaisesRegex(ValueError, "report exceeds"):
            bot.validate_report(raw + " ")

    def test_missing_or_extra_root_fields_are_rejected(self):
        for mutation in ("missing", "extra"):
            with self.subTest(mutation=mutation):
                value = report()
                if mutation == "missing":
                    del value["generality"]
                else:
                    value["merge"] = True
                with self.assertRaisesRegex(ValueError, "report fields"):
                    self.validate(value)

    def test_missing_or_extra_test_fields_are_rejected(self):
        for mutation in ("missing", "extra"):
            with self.subTest(mutation=mutation):
                value = report()
                if mutation == "missing":
                    del value["tests"][0]["evidence"]
                else:
                    value["tests"][0]["exit_code"] = 0
                with self.assertRaisesRegex(ValueError, "test fields"):
                    self.validate(value)

    def test_nonfixed_outcomes_require_empty_patch(self):
        for status in bot.STATUSES - {"fixed"}:
            with self.subTest(status=status):
                value = report()
                value.update(status=status, patch="diff --git a/a b/a\n", regression_path=None)
                with self.assertRaisesRegex(ValueError, "Non-fixed"):
                    self.validate(value)
                value["patch"] = ""
                self.assertEqual(self.validate(value)["status"], status)

    def test_field_length_limits_accept_boundary_and_reject_one_over(self):
        for field, limit in (("title", 160), ("summary", 3000), ("root_cause", 3000), ("generality", 3000)):
            with self.subTest(field=field):
                value = report()
                value[field] = "x" * limit
                self.validate(value)
                value[field] += "x"
                with self.assertRaisesRegex(ValueError, f"Invalid {field}"):
                    self.validate(value)

    def test_test_and_limitation_array_limits(self):
        value = report()
        value["tests"] *= 12
        self.validate(value)
        value["tests"].append(copy.deepcopy(value["tests"][0]))
        with self.assertRaisesRegex(ValueError, "test report"):
            self.validate(value)
        value = report()
        value["limitations"] = ["x" * 1000] * 10
        self.validate(value)
        value["limitations"].append("one more")
        with self.assertRaisesRegex(ValueError, "limitations"):
            self.validate(value)

    def test_patch_limit_counts_utf8_bytes(self):
        value = report()
        value["patch"] = "x" * bot.MAX_PATCH
        self.validate(value)
        value["patch"] += "x"
        with self.assertRaisesRegex(ValueError, "Patch exceeds"):
            self.validate(value)
        value["patch"] = "é" * (bot.MAX_PATCH // 2 + 1)
        with self.assertRaisesRegex(ValueError, "Patch exceeds"):
            self.validate(value, ensure_ascii=False)

    def test_report_limit_counts_utf8_bytes_and_serialization(self):
        value = report()
        value.update(summary="界" * 3000, root_cause="界" * 3000, generality="界" * 3000,
                     patch="界" * 18000, limitations=["界" * 1000] * 10)
        raw = json.dumps(value, ensure_ascii=False)
        self.assertLess(len(raw), bot.MAX_REPORT)
        self.assertGreater(len(raw.encode()), bot.MAX_REPORT)
        with self.assertRaisesRegex(ValueError, "report exceeds"):
            bot.validate_report(raw)
        value = report()
        value["patch"] = "\\" * (bot.MAX_PATCH - 1)
        with self.assertRaisesRegex(ValueError, "report exceeds"):
            self.validate(value)

    def test_snapshot_limit_counts_utf8_bytes(self):
        value = {"base_sha": "a" * 40, "number": 7, "branch": "codex/issue-7", "body": "界" * 12000}
        with patch.dict(os.environ, {"ISSUE_SNAPSHOT": json.dumps(value, ensure_ascii=False)}):
            with self.assertRaisesRegex(ValueError, "snapshot too large"):
                bot.read_snapshot()


class OriginalRegressionTests(unittest.TestCase):
    def test_extracts_block_with_prelude_and_no_variant_helpers(self):
        text = ("outside helper\n-- BEGIN ORIGINAL REPRODUCER\noriginal input\n"
                "-- END ORIGINAL REPRODUCER\nvariant helper\n")
        self.assertEqual(bot.extract_original(text, profile()), "import Tests.Utils\noriginal input\n")

    def test_missing_duplicate_reversed_and_empty_markers_are_rejected(self):
        cases = {
            "missing": "original input\n",
            "missing_end": "-- BEGIN ORIGINAL REPRODUCER\noriginal input\n",
            "duplicate_start": "-- BEGIN ORIGINAL REPRODUCER\n-- BEGIN ORIGINAL REPRODUCER\ninput\n-- END ORIGINAL REPRODUCER\n",
            "duplicate_end": "-- BEGIN ORIGINAL REPRODUCER\ninput\n-- END ORIGINAL REPRODUCER\n-- END ORIGINAL REPRODUCER\n",
            "reversed": "-- END ORIGINAL REPRODUCER\ninput\n-- BEGIN ORIGINAL REPRODUCER\n",
            "empty": "-- BEGIN ORIGINAL REPRODUCER\n \n-- END ORIGINAL REPRODUCER\n",
        }
        for name, text in cases.items():
            with self.subTest(name=name), self.assertRaises(ValueError):
                bot.extract_original(text, profile())


class TargetBranchTests(unittest.TestCase):
    def test_default_and_empty_form_values_select_default(self):
        for body in ("A report without a target.", "### Target Branch\n\n", "### Target Branch\n\n_No response_\n",
                     "### Target Branch\n\ndefault\n", "### Target Branch\n\n(default)\n"):
            with self.subTest(body=body):
                self.assertEqual(bot.resolve_target_branch(body, "main"), "main")

    def test_structured_field_selects_target_and_wins_over_legacy(self):
        body = "Branch: legacy\n\n### Target Branch\n\n`release/fixes`\n\n### Reproducer\n\ncode"
        self.assertEqual(bot.resolve_target_branch(body, "main"), "release/fixes")

    def test_maintainer_override_wins_even_when_issue_fields_are_ambiguous(self):
        body = "### Target Branch\n\none\n### Target Branch\n\ntwo\n"
        self.assertEqual(bot.resolve_target_branch(body, "main", " `release/override` "), "release/override")

    def test_unambiguous_legacy_statements_are_supported(self):
        for body in ("Branch: `release/fixes`", "Target branch: release/fixes", "On `release/fixes`, this fails.",
                     "On branch `release/fixes`, this fails.", "Branch: release/fixes\nOn `release/fixes`"):
            with self.subTest(body=body):
                self.assertEqual(bot.resolve_target_branch(body, "main"), "release/fixes")

    def test_code_and_html_comments_cannot_select_target(self):
        body = ("```lean\n### Target Branch\nmalicious\nBranch: also-malicious\n```\n"
                "<!--\n### Target Branch\nhidden\nOn `also-hidden`\n-->\nA normal report.")
        self.assertEqual(bot.resolve_target_branch(body, "main"), "main")

    def test_tilde_and_long_backtick_fences_cannot_select_target(self):
        for opening, interior, closing in (
                ("~~~text", "Branch: fake", "~~~"),
                ("~~~~~~text", "~~~\nBranch: fake", "~~~~~~"),
                ("````text", "```\nBranch: fake", "````"),
                ("`````text", "````\nOn `fake`", "``````"),
                ("```text", "~~~\nBranch: fake", "```"),
                ("   ~~~text", "   Branch: fake", "   ~~~   "),
        ):
            with self.subTest(opening=opening):
                body = f"{opening}\n{interior}\n{closing}\nBranch: release/fixes\n"
                self.assertEqual(bot.resolve_target_branch(body, "main"), "release/fixes")

    def test_unterminated_fence_hides_branch_hints_through_end_of_issue(self):
        for opening in ("~~~text", "````text"):
            with self.subTest(opening=opening):
                self.assertEqual(bot.resolve_target_branch(f"{opening}\nBranch: fake\n", "main"), "main")

    def test_ambiguous_fields_or_legacy_targets_are_rejected(self):
        for body in ("Branch: one\nBranch: two", "Branch: one\nOn `two`", "### Target Branch\none\n### Target Branch\ntwo"):
            with self.subTest(body=body), self.assertRaises(ValueError):
                bot.resolve_target_branch(body, "main")

    def test_invalid_target_values_and_utf8_byte_limit(self):
        for value in ("one two", "one\ntwo", "bad\x00name", "bad\x7fname", "x" * 256, "é" * 128):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "plain branch name"):
                bot.resolve_target_branch("", "main", value)
        self.assertEqual(bot.resolve_target_branch("", "main", "é" * 127), "é" * 127)


class PrepareTests(unittest.TestCase):
    def setUp(self):
        folder = tempfile.TemporaryDirectory(prefix="agent-fix-event-")
        self.addCleanup(folder.cleanup)
        event_path = Path(folder.name) / "event.json"
        event_path.write_text(json.dumps({"action": "labeled", "label": {"name": "agent:fix"}, "issue": {"number": 7}}))
        self.environment = {
            "GITHUB_EVENT_PATH": str(event_path), "GITHUB_EVENT_NAME": "issues", "GITHUB_ACTOR": "maintainer",
            "GITHUB_TRIGGERING_ACTOR": "maintainer", "GITHUB_REPOSITORY": "example/project",
            "GITHUB_REF": "refs/heads/main", "GITHUB_RUN_ID": "1234", "AUTOMATION_REF": "c" * 40,
            "TARGET_BRANCH": "",
        }

    def test_authorization_failure_stops_before_repository_or_model_work(self):
        with patch.dict(os.environ, self.environment), \
                patch.object(bot, "api", return_value={"permission": "read"}) as api_mock, \
                patch.object(bot, "output", side_effect=AssertionError("Unauthorized run cannot emit a snapshot")), \
                self.assertRaisesRegex(ValueError, "write permission"):
            bot.prepare()
        self.assertEqual(api_mock.call_count, 1)
        self.assertEqual(api_mock.call_args.args[1], "collaborators/maintainer/permission")

    def test_dispatching_untrusted_workflow_branch_stops_before_issue_read(self):
        self.environment["GITHUB_REF"] = "refs/heads/feature"
        calls = []

        def fake_api(repository, endpoint, method="GET", data=None):
            calls.append(endpoint)
            if endpoint == "collaborators/maintainer/permission":
                return {"permission": "write"}
            if endpoint == "":
                return {"default_branch": "main"}
            self.fail(f"Untrusted workflow reached unexpected API call: {endpoint}")

        with patch.dict(os.environ, self.environment), patch.object(bot, "api", side_effect=fake_api), \
                patch.object(bot, "output", side_effect=AssertionError("Untrusted workflow cannot emit a snapshot")), \
                self.assertRaisesRegex(ValueError, "default branch"):
            bot.prepare()
        self.assertEqual(calls, ["collaborators/maintainer/permission", ""])

    def test_target_branch_snapshot_separates_policy_commit_from_bug_commit(self):
        calls = []
        issue = {"state": "open", "title": "Reported bug", "body": "### Target Branch\n\nrelease/fixes\n\n"
                 "### Reproducer\n\n```lean\nexample\n```", "html_url": "https://example.invalid/issues/7",
                 "labels": [{"name": "agent:fix"}]}

        def fake_api(repository, endpoint, method="GET", data=None):
            calls.append(endpoint)
            if endpoint == "collaborators/maintainer/permission":
                return {"permission": "write"}
            if endpoint == "":
                return {"default_branch": "main"}
            if endpoint == "issues/7":
                return issue
            if endpoint.startswith("pulls?") or endpoint == "git/matching-refs/heads/codex/issue-7":
                return []
            if endpoint == "commits/main":
                return {"sha": "a" * 40}
            if endpoint == "branches/release%2Ffixes":
                return {"name": "release/fixes", "commit": {"sha": "b" * 40}}
            self.fail(f"Unexpected target-selection API operation: {endpoint}")

        with patch.dict(os.environ, self.environment), patch.object(bot, "api", side_effect=fake_api), \
                patch.object(bot, "output") as outputs:
            bot.prepare()
        values = dict(call.args for call in outputs.call_args_list)
        snapshot = json.loads(values["snapshot"])
        self.assertEqual(snapshot["policy_sha"], "a" * 40)
        self.assertEqual(snapshot["base_sha"], "b" * 40)
        self.assertEqual(snapshot["base_branch"], "release/fixes")
        self.assertEqual(values["policy_sha"], "a" * 40)
        self.assertEqual(values["base_sha"], "b" * 40)
        self.assertIn("branches/release%2Ffixes", calls)


class SetupToolchainReaderTests(unittest.TestCase):
    """Run only the actual embedded Python reader; never run setup.sh or installers."""

    @classmethod
    def setUpClass(cls):
        setup = SOURCE.with_name("setup.sh").read_text()
        match = re.search(r"^toolchain=\$\(python3 - [^\n]* <<'PY'\n(.*?)^PY$", setup, re.M | re.S)
        if match is None:
            raise AssertionError("Cannot locate the toolchain reader's Python heredoc")
        cls.reader = match[1]

    def setUp(self):
        folder = tempfile.TemporaryDirectory(prefix="agent-fix-toolchain-")
        self.addCleanup(folder.cleanup)
        self.path = Path(folder.name) / "lean-toolchain"

    def run_reader(self):
        return subprocess.run([sys.executable, "-c", self.reader, str(self.path)],
                              text=True, capture_output=True, timeout=2)

    def assert_rejected(self):
        result = self.run_reader()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Cannot read the selected branch's lean-toolchain safely:", result.stderr)

    def test_regular_ascii_toolchain_is_read_exactly(self):
        self.path.write_bytes(b"leanprover/lean4:v4.25.0-rc2\n")
        result = self.run_reader()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "leanprover/lean4:v4.25.0-rc2\n")

    def test_symlink_is_rejected_without_reading_target(self):
        target = self.path.with_name("outside-policy.txt")
        target.write_text("outside policy contents\n")
        self.path.symlink_to(target)
        self.assert_rejected()
        self.assertEqual(target.read_text(), "outside policy contents\n")

    def test_fifo_is_rejected_without_waiting_for_writer(self):
        os.mkfifo(self.path)
        self.assert_rejected()

    def test_directory_is_rejected(self):
        self.path.mkdir()
        self.assert_rejected()

    def test_oversize_file_is_rejected(self):
        self.path.write_bytes(b"x" * 257)
        self.assert_rejected()

    def test_nul_bytes_are_rejected(self):
        self.path.write_bytes(b"leanprover/lean4:v4.25.0\x00extra")
        self.assert_rejected()

    def test_non_ascii_bytes_are_rejected(self):
        self.path.write_bytes(b"leanprover/lean4:v4.25.0\xff")
        self.assert_rejected()


if __name__ == "__main__":
    unittest.main()
