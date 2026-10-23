#!/usr/bin/env python3
"""Trusted issue-fix runner. Model output is data; only repository config supplies commands."""

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import signal
import stat
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request


MAX_SNAPSHOT = 32 * 1024
MAX_REPORT = 96 * 1024
MAX_PATCH = 64 * 1024
STATUSES = {"fixed", "needs-information", "out-of-scope", "unable-to-fix"}
CONFIG = ".github/agent-fix/config.json"


def require(condition, message):
    """Stop the run before publication when an invariant is not satisfied."""
    if not condition:
        raise ValueError(message)


def command(args, cwd=None, env=None, check=True):
    """Execute an argv without shell expansion; return stdout or raise with stderr."""
    result = subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True)
    if check:
        require(result.returncode == 0, result.stderr.strip() or f"Command failed: {args[0]}")
    return result


def git(*args, cwd=None, **kwargs):
    """Run Git with hooks disabled; arguments must come from trusted code, not report commands."""
    return command(["git", "-c", "core.hooksPath=/dev/null", *args], cwd=cwd, **kwargs)


def api(repository, endpoint, method="GET", data=None):
    """Call this repository's GitHub API using the current job's scoped token."""
    require(re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository), "Invalid repository")
    token = os.environ.get("GH_TOKEN", "")
    require(token, "GH_TOKEN is required for GitHub operations")
    request = urllib.request.Request(
        f"{os.environ.get('GITHUB_API_URL', 'https://api.github.com')}/repos/{repository}/{endpoint}",
        data=None if data is None else json.dumps(data).encode(), method=method,
        headers={"Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json",
                 "Content-Type": "application/json", "X-GitHub-Api-Version": "2022-11-28"})
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            return json.load(response)
    except urllib.error.HTTPError as error:
        raise ValueError(f"GitHub API {method} {endpoint.split('?')[0]}: HTTP {error.code}") from error


def fingerprint(issue):
    """Hash only title/body; labels and bot status comments must not invalidate the snapshot."""
    return hashlib.sha256(json.dumps([issue["title"], issue.get("body") or ""],
                                    ensure_ascii=False).encode()).hexdigest()


def output(name, value):
    """Write a bounded single-line job output without evaluating its contents."""
    require("\n" not in value and "\r" not in value, "Job output must be a single line")
    with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as stream:
        stream.write(f"{name}={value}\n")


def authorize(repository, actors):
    """Require live write permission for both the initiator and the rerunning actor."""
    for actor in set(actors):
        require(re.fullmatch(r"[A-Za-z0-9_-]+(?:\[bot\])?", actor or ""), "Invalid actor")
        permission = api(repository, f"collaborators/{urllib.parse.quote(actor)}/permission")
        require(permission.get("permission") in {"admin", "maintain", "write"},
                f"{actor} must have repository write permission to run agent:fix")


def open_prs(repository, branch):
    """Find an existing PR for the deterministic bot branch, including completed drafts."""
    owner = repository.split("/")[0]
    query = urllib.parse.urlencode({"state": "all", "head": f"{owner}:{branch}"})
    return api(repository, f"pulls?{query}")


def strip_markdown_fences(text):
    """Remove fenced blocks, honoring marker type/length and unterminated blocks through EOF."""
    output = []
    marker = None
    length = 0
    for line in text.splitlines(keepends=True):
        content = line.rstrip("\r\n")
        if marker is not None:
            closing = re.fullmatch(r" {0,3}(`+|~+)[ \t]*", content)
            if closing and closing[1][0] == marker and len(closing[1]) >= length:
                marker = None
            output.append("\n" if line.endswith("\n") else "")
            continue
        opening = re.match(r"^ {0,3}(`{3,}|~{3,})(.*)$", content)
        if opening and not (opening[1][0] == "`" and "`" in opening[2]):
            marker, length = opening[1][0], len(opening[1])
            output.append("\n" if line.endswith("\n") else "")
        else:
            output.append(line)
    return "".join(output)


def resolve_target_branch(body, default_branch, override=""):
    """Select override, then Target Branch, then one legacy branch statement, then default.

    Ignore fenced code and HTML comments. Reject ambiguous fields/statements or a
    selected value that is not one bounded plain name; the caller verifies that
    name against the repository's branches API before freezing its commit.
    """
    if override.strip():
        selected = override.strip().strip("`")
    else:
        # Never interpret sample-code branches as a repository branch selector.
        prose = strip_markdown_fences(body)
        prose = re.sub(r"<!--.*?-->", "", prose, flags=re.S)
        fields = re.findall(r"^### Target Branch\s*\n(.*?)(?=^### |\Z)", prose, flags=re.M | re.S)
        require(len(fields) <= 1, "Multiple Target Branch fields; select one branch")
        field = fields[0].strip().strip("`") if fields else ""
        if field not in {"", "_No response_", "default", "(default)"}:
            selected = field
        else:
            mentions = re.findall(r"^\s*(?:Target branch|Branch):\s*`?([^\s`]+)`?\s*$", prose, flags=re.M | re.I)
            mentions += re.findall(r"^\s*On(?: branch)?\s+`([^`\n]+)`", prose, flags=re.M | re.I)
            require(len(set(mentions)) <= 1, "The issue names multiple branches; fill in Target Branch")
            selected = mentions[0] if mentions else default_branch
    require(bool(re.fullmatch(r"[^\s`]+", selected)) and len(selected.encode()) <= 255
            and not any(ord(char) < 32 or ord(char) == 127 for char in selected),
            "Target Branch must contain one plain branch name")
    return selected


def preflight_problem(repository, number, message):
    """Ask for missing issue metadata after authorization, before starting the model or any target code."""
    api(repository, f"issues/{number}/comments", "POST", {
        "body": f"Cannot start agent fix: {message}.\n\n"
                "Provide a fenced minimal reproducer and one explicit **Target Branch** "
                "(or leave it blank for the default branch), then start a new run."})
    raise ValueError(message)


def prepare():
    """Authorize an issue event and freeze its input and default-branch commit before spending API credits."""
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    name = os.environ["GITHUB_EVENT_NAME"]
    require(name in {"issues", "workflow_dispatch"}, "Unsupported trigger")
    if name == "issues":
        require(event.get("action") == "labeled" and event.get("label", {}).get("name") == "agent:fix",
                "Only the agent:fix label starts an issue run")
        number = event["issue"]["number"]
    else:
        require(re.fullmatch(r"[1-9][0-9]*", os.environ["ISSUE_NUMBER"]), "Use a canonical positive issue number")
        number = int(os.environ["ISSUE_NUMBER"])
    require(type(number) is int and number > 0, "Expected a positive issue number")
    repository = os.environ["GITHUB_REPOSITORY"]
    require(re.fullmatch(r"[0-9a-f]{40}", os.environ["AUTOMATION_REF"]), "Pin automation-ref to a full commit SHA")
    authorize(repository, [os.environ["GITHUB_ACTOR"], os.environ["GITHUB_TRIGGERING_ACTOR"]])
    metadata = api(repository, "")
    base_branch = metadata["default_branch"]
    require(os.environ["GITHUB_REF"] == f"refs/heads/{base_branch}", "Run the bot only from the default branch")
    issue = api(repository, f"issues/{number}")
    require("pull_request" not in issue and issue["state"] == "open", "Expected an open issue, not a PR")
    if name == "issues":
        require(any(label["name"] == "agent:fix" for label in issue["labels"]), "Label was withdrawn")
    if not re.search(r"```[^\n]*\n\s*\S", issue.get("body") or ""):
        preflight_problem(repository, number, "The issue needs a fenced minimal reproducer")
    branch = f"codex/issue-{number}"
    require(not open_prs(repository, branch), "A bot PR already exists for this issue; continue that PR")
    refs = api(repository, f"git/matching-refs/heads/{branch}")
    for ref in refs:
        if ref["ref"] == f"refs/heads/{branch}":
            commit = api(repository, f"git/commits/{ref['object']['sha']}")
            require(f"agent-fix-run: {os.environ['GITHUB_RUN_ID']}" in commit["message"],
                    "A different run already owns the bot branch; inspect it before retrying")
    policy_sha = api(repository, f"commits/{urllib.parse.quote(base_branch, safe='')}")["sha"]
    try:
        selected = resolve_target_branch(issue.get("body") or "", base_branch, os.environ.get("TARGET_BRANCH", ""))
        target = api(repository, f"branches/{urllib.parse.quote(selected, safe='')}")
        require(target["name"] == selected, "Branch lookup did not return the selected branch")
    except ValueError as error:
        preflight_problem(repository, number, f"Cannot resolve the target branch: {error}")
    base_branch = target["name"]
    base_sha = target["commit"]["sha"]
    snapshot = {"repository": repository, "number": number, "url": issue["html_url"],
                "title": issue["title"], "body": issue.get("body") or "",
                "fingerprint": fingerprint(issue), "base_sha": base_sha,
                "policy_sha": policy_sha, "base_branch": base_branch,
                "branch": branch, "label_triggered": name == "issues"}
    encoded = json.dumps(snapshot, ensure_ascii=False, separators=(",", ":"))
    require(len(encoded.encode()) <= MAX_SNAPSHOT, "Issue exceeds the 32 KiB small-issue input limit")
    output("snapshot", encoded)
    output("base_sha", base_sha)
    output("policy_sha", policy_sha)
    output("number", str(number))


def read_snapshot():
    """Read the prepare job's snapshot, never metadata invented by the model."""
    raw = os.environ["ISSUE_SNAPSHOT"]
    require(len(raw.encode()) <= MAX_SNAPSHOT, "Issue snapshot too large")
    snapshot = json.loads(raw)
    require(re.fullmatch(r"[0-9a-f]{40}", snapshot["base_sha"]), "Invalid base commit")
    require(type(snapshot["number"]) is int and snapshot["number"] > 0, "Invalid issue number")
    require(snapshot["branch"] == f"codex/issue-{snapshot['number']}", "Invalid bot branch")
    return snapshot


def config():
    """Load repository-owned paths and commands; the publisher reads this before applying any patch."""
    value = json.loads((Path(os.environ.get("AGENT_FIX_POLICY_ROOT", ".")) / CONFIG).read_text())
    require(value["version"] == 1, "Unsupported issue-fix profile")
    safe_path(value["regression_path"].replace("{issue}", "1"))
    require((value["umbrella_path"] is None) == (value["umbrella_import"] is None),
            "Set both umbrella fields or set both to null for automatic test discovery")
    if value["umbrella_path"] is not None:
        safe_path(value["umbrella_path"])
    require(1 <= value["max_files"] <= 30 and 1 <= value["max_changed_lines"] <= 2000,
            "Invalid small-fix limits")
    return value


def safe_path(value):
    """Accept ordinary repository-relative paths, excluding traversal, metadata, and control characters."""
    require(isinstance(value, str) and value and "\\" not in value,
            "Expected a repository-relative POSIX path")
    path = PurePosixPath(value)
    require(path.parts and not path.is_absolute() and all(part not in {"..", ".git"} for part in path.parts)
            and not any(ord(char) < 32 or ord(char) == 127 for char in value), "Unsafe patch path")
    return path


def validate_report(raw):
    """Check the schema's types and bounded fields without executing model-provided commands."""
    require(len(raw.encode()) <= MAX_REPORT, "Model report exceeds 96 KiB")
    report = json.loads(raw)
    fields = {"status", "title", "summary", "root_cause", "generality", "regression_path",
              "tests", "limitations", "patch"}
    require(isinstance(report, dict) and set(report) == fields, "Unexpected report fields")
    require(isinstance(report["status"], str) and report["status"] in STATUSES, "Invalid fix status")
    for name, limit in [("title", 160), ("summary", 3000), ("root_cause", 3000), ("generality", 3000)]:
        require(isinstance(report[name], str) and 0 < len(report[name]) <= limit, f"Invalid {name}")
    require(isinstance(report["patch"], str) and len(report["patch"].encode()) <= MAX_PATCH,
            "Patch exceeds 64 KiB")
    require(report["regression_path"] is None or
            (isinstance(report["regression_path"], str) and len(report["regression_path"]) <= 500),
            "Invalid regression path")
    require(isinstance(report["tests"], list) and len(report["tests"]) <= 12, "Invalid test report")
    for test in report["tests"]:
        require(isinstance(test, dict) and set(test) == {"command", "result", "evidence"}, "Invalid test fields")
        for key, limit in [("command", 500), ("result", 100), ("evidence", 1500)]:
            require(isinstance(test[key], str) and 0 < len(test[key]) <= limit, f"Invalid test {key}")
    require(isinstance(report["limitations"], list) and len(report["limitations"]) <= 10
            and all(isinstance(item, str) and len(item) <= 1000 for item in report["limitations"]),
            "Invalid limitations")
    require(report["status"] == "fixed" or not report["patch"], "Non-fixed outcomes cannot contain a patch")
    return report


def ensure_artifacts():
    """Reserve an untracked real directory; reject branch-owned files, links, and special files before I/O."""
    require(not git("ls-files", "--", ".agent-fix").stdout,
            "The target branch must not track the reserved .agent-fix path")
    folder = Path(".agent-fix")
    require(not folder.is_symlink(), "The reserved .agent-fix directory must not be a symlink")
    if folder.exists():
        require(folder.is_dir(), "The reserved .agent-fix path must be a directory")
        for child in folder.rglob("*"):
            info = child.lstat()
            require(stat.S_ISDIR(info.st_mode) or
                    (stat.S_ISREG(info.st_mode) and info.st_nlink == 1),
                    "Reserved artifacts must be ordinary files or directories without links")
    else:
        folder.mkdir(mode=0o700)
    return folder


def open_artifact(name):
    """Open one reserved regular file without following links, checking its type before truncation."""
    require(bool(re.fullmatch(r"[A-Za-z0-9_.-]+", name)), "Invalid artifact name")
    path = ensure_artifacts() / name
    descriptor = os.open(path, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    try:
        info = os.fstat(descriptor)
        require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                "Artifact must be a regular file without links")
        os.ftruncate(descriptor, 0)
        return os.fdopen(descriptor, "w+b")
    except BaseException:
        os.close(descriptor)
        raise


def write_artifact(name, text):
    """Write UTF-8 data to a guarded artifact file and return its repository-relative path."""
    with open_artifact(name) as stream:
        stream.write(text.encode())
    return str(Path(".agent-fix") / name)


def initialize():
    """Materialize input as data and ignore transient files; no issue text becomes shell source."""
    snapshot = read_snapshot()
    write_artifact("issue.json", json.dumps(snapshot, ensure_ascii=False, indent=2))
    exclude = Path(git("rev-parse", "--git-path", "info/exclude").stdout.strip())
    with exclude.open("a") as stream:
        stream.write("\n.agent-fix/\n")


def export_patch():
    """Export tracked and untracked edits without staging, including newly added regression files."""
    ensure_artifacts()
    patch = git("diff", "--binary", "HEAD").stdout
    paths = git("ls-files", "--others", "--exclude-standard", "-z").stdout.split("\0")
    for path in filter(None, paths):
        if PurePosixPath(path).parts[0] == ".agent-fix":
            continue
        safe_path(path)
        result = git("diff", "--no-index", "--binary", "--", "/dev/null", path, check=False)
        require(result.returncode in {0, 1}, "Cannot export untracked file")
        patch += result.stdout
    require(len(patch.encode()) <= MAX_PATCH, "Patch exceeds the small-fix size limit")
    print(patch, end="")


def apply_patch(report, snapshot, profile):
    """Require a clean frozen base, apply data, and reject patches outside the trusted profile.

    Accept only bounded regular source additions/modifications, a production
    change, and the required new issue regression/import. Return its path and
    standalone original block; never execute generated code in this phase.
    """
    require(report["status"] == "fixed" and report["patch"], "No fixed patch to apply")
    require(git("rev-parse", "HEAD").stdout.strip() == snapshot["base_sha"], "Checkout is not the trusted base")
    require(not git("status", "--porcelain", "--untracked-files=no").stdout, "Checkout must be clean")
    patch = report["patch"]
    require("GIT binary patch" not in patch and "Binary files " not in patch, "Binary patches are not supported")
    patch_file = write_artifact("fix.patch", patch)
    git("apply", "--check", "--index", patch_file)
    git("apply", "--index", patch_file)
    # Git validates traversal while applying; use NUL-delimited staged names, never a hand-written diff parser.
    entries = git("diff", "--cached", "--name-status", "--no-renames", "-z").stdout.split("\0")
    pairs = list(zip(entries[0:-1:2], entries[1:-1:2]))
    require(0 < len(pairs) <= profile["max_files"], "Too many files for a small fix")
    for status, path in pairs:
        safe_path(path)
        require(status in {"A", "M"}, "Small fixes may only add or modify files")
        require(any(path.startswith(prefix) if prefix.endswith("/") else path == prefix
                    for prefix in profile["editable_paths"]), f"Path is outside the bug-fix scope: {path}")
        require(PurePosixPath(path).suffix in profile["source_extensions"]
                and not any(part.startswith(".") for part in PurePosixPath(path).parts),
                f"Only configured source files are allowed: {path}")
        mode = git("ls-files", "--stage", "--", path).stdout.split()[0]
        require(mode == "100644", f"Only regular nonexecutable source files are allowed: {path}")
    stats = git("diff", "--cached", "--numstat", "--no-renames").stdout.splitlines()
    require(all(line.split("\t", 2)[0] != "-" for line in stats), "Binary change is not allowed")
    require(sum(int(part) for line in stats for part in line.split("\t", 2)[:2]) <= profile["max_changed_lines"],
            "Patch is too large for the small-issue workflow")
    regression = profile["regression_path"].format(issue=snapshot["number"])
    require(report["regression_path"] == regression and ("A", regression) in pairs,
            f"Add the original reproducer in {regression}")
    require(any(path.startswith(prefix) if prefix.endswith("/") else path == prefix
                for _, path in pairs for prefix in profile["production_paths"]),
            "A fixed outcome must change production code, not only tests")
    if profile["umbrella_path"] is not None:
        umbrella = profile["umbrella_import"].format(issue=snapshot["number"])
        require(umbrella in Path(profile["umbrella_path"]).read_text().splitlines(), "Missing regression umbrella import")
    original = extract_original(Path(regression).read_text(), profile)
    return regression, original


def extract_original(text, profile):
    """Extract one self-contained original regression, so variant tests cannot cause an unrelated base failure."""
    lines = text.splitlines(keepends=True)
    start = [i for i, line in enumerate(lines) if line.strip() == profile["original_start"]]
    end = [i for i, line in enumerate(lines) if line.strip() == profile["original_end"]]
    require(len(start) == len(end) == 1 and start[0] < end[0], "Mark exactly one original reproducer block")
    block = "".join(lines[start[0] + 1:end[0]])
    require(block.strip(), "The original reproducer cannot be empty")
    return profile["original_prelude"] + block


def run_check(name, script, timeout, trusted_setup=False, cwd=None):
    """Run a trusted profile command without GitHub credentials and retain bounded diagnostic evidence."""
    forbidden = {"GH_TOKEN", "GITHUB_TOKEN", "OPENAI_API_KEY", "MODEL_REPORT", "GITHUB_OUTPUT",
                 "GITHUB_ENV", "GITHUB_STATE", "GITHUB_STEP_SUMMARY", "GITHUB_PATH"}
    if trusted_setup:
        forbidden.remove("GITHUB_PATH")
    env = {key: value for key, value in os.environ.items()
           if key not in forbidden and not key.startswith("ACTIONS_")}
    with open_artifact(f"{name}.log") as stream:
        process = subprocess.Popen(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", script],
                                   cwd=cwd, env=env, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            code = 124
            stream.write(b"\nCommand exceeded the configured timeout.\n")
            stream.flush()
        stream.seek(0, 2)
        stream.seek(max(0, stream.tell() - 2000))
        tail = stream.read().decode(errors="replace")
    print(f"{name}: exit {code}\n{tail}")
    return {"command": script, "exit_code": code, "tail": tail}


def setup():
    """Provision the trusted base in its own workflow step, so GITHUB_PATH reaches subsequent steps."""
    profile = config()
    result = run_check("setup", profile["setup_command"], profile["command_timeout_seconds"], trusted_setup=True,
                       cwd=os.environ.get("AGENT_FIX_POLICY_ROOT", "."))
    require(result["exit_code"] == 0, "Repository setup failed")


def validate():
    """Independently replay the original red/green regression and full checks in a read-only job."""
    snapshot = read_snapshot()
    report = validate_report(os.environ["MODEL_REPORT"])
    profile = config()
    initialize()
    if report["status"] != "fixed":
        output("checks", "{}")
        return
    regression, original = apply_patch(report, snapshot, profile)
    git("reset", "--hard", snapshot["base_sha"])
    timeout = profile["command_timeout_seconds"]
    ready = run_check("prepare-base", profile["prepare_command"], timeout)
    require(ready["exit_code"] == 0, "Baseline preparation failed; no meaningful red/green comparison")
    base_full = run_check("full-base", profile["full_test_command"], timeout)
    # Full checks may clean build products, so prepare the standalone reproducer again.
    ready = run_check("prepare-original-base", profile["prepare_command"], timeout)
    require(ready["exit_code"] == 0, "Cannot prepare original baseline regression")
    original_name = "original" + PurePosixPath(regression).suffix
    original_file = write_artifact(original_name, original)
    original_command = profile["original_command"].format(original=original_file)
    base_original = run_check("original-base", original_command, timeout)
    require(base_original["exit_code"] not in {0, 124}, "Original reproducer must fail on base without timing out")
    apply_patch(report, snapshot, profile)
    ready = run_check("prepare-fixed", profile["prepare_command"], timeout)
    require(ready["exit_code"] == 0, "Patched preparation failed")
    write_artifact(original_name, original)
    fixed_original = run_check("original-fixed", original_command, timeout)
    require(fixed_original["exit_code"] == 0, "Original reproducer still fails")
    fixed_regression = run_check("regression-fixed", profile["regression_command"].format(regression=regression), timeout)
    require(fixed_regression["exit_code"] == 0, "Issue regression/variants fail")
    fixed_full = run_check("full-fixed", profile["full_test_command"], timeout)
    checks = {"original_base": base_original, "original_fixed": fixed_original,
              "regression_fixed": fixed_regression, "full_base": base_full, "full_fixed": fixed_full}
    output("checks", json.dumps(checks, separators=(",", ":")))


def publish():
    """Publish only validated data from clean trusted checkouts; never run tests or generated code here."""
    snapshot = read_snapshot()
    report = validate_report(os.environ["MODEL_REPORT"])
    profile = config()
    repository = snapshot["repository"]
    authorize(repository, [os.environ["GITHUB_ACTOR"], os.environ["GITHUB_TRIGGERING_ACTOR"]])
    current = api(repository, f"issues/{snapshot['number']}")
    require(current["state"] == "open" and fingerprint(current) == snapshot["fingerprint"],
            "Issue changed during the run; inspect it and start a new run")
    if snapshot["label_triggered"]:
        require(any(label["name"] == "agent:fix" for label in current["labels"]), "Label was withdrawn")
    run_url = f"https://github.com/{repository}/actions/runs/{os.environ['GITHUB_RUN_ID']}"
    if report["status"] != "fixed":
        api(repository, f"issues/{snapshot['number']}/comments", "POST", {
            "body": f"Agent fix: **{report['status']}**\n\n{report['summary']}\n\n"
                    + "\n".join(report["limitations"]) + f"\n\n[Run details]({run_url})"})
        return
    checks = json.loads(os.environ["VALIDATION_CHECKS"])
    require(checks["original_base"]["exit_code"] not in {0, 124}
            and checks["original_fixed"]["exit_code"] == 0
            and checks["regression_fixed"]["exit_code"] == 0, "Independent regression checks did not pass")
    initialize()
    apply_patch(report, snapshot, profile)
    branch = snapshot["branch"]
    existing = open_prs(repository, branch)
    if existing:
        require(any(f"agent-fix-run: {os.environ['GITHUB_RUN_ID']}" in (pr.get("body") or "") for pr in existing),
                "A PR already exists; refusing to overwrite it")
        print(existing[0]["html_url"])
        return
    marker = f"agent-fix-run: {os.environ['GITHUB_RUN_ID']}"
    git("-c", "user.name=github-actions[bot]", "-c",
        "user.email=41898282+github-actions[bot]@users.noreply.github.com", "commit", "-m",
        f"Fix issue #{snapshot['number']}: {report['title']}\n\n{marker}")
    # Recover a PR-creation retry without overwriting a different run's branch.
    refs = api(repository, f"git/matching-refs/heads/{branch}")
    exact = [ref for ref in refs if ref["ref"] == f"refs/heads/{branch}"]
    if exact:
        remote = api(repository, f"git/commits/{exact[0]['object']['sha']}")
        require(marker in remote["message"] and remote["tree"]["sha"] == git("rev-parse", "HEAD^{tree}").stdout.strip(),
                "Bot branch already exists with different work; refusing to overwrite it")
    else:
        auth = base64.b64encode(f"x-access-token:{os.environ['GH_TOKEN']}".encode()).decode()
        env = dict(os.environ, GIT_CONFIG_COUNT="1", GIT_CONFIG_KEY_0="http.https://github.com/.extraheader",
                   GIT_CONFIG_VALUE_0=f"AUTHORIZATION: basic {auth}")
        git("push", "origin", f"HEAD:refs/heads/{branch}", env=env)
    body = render_pr(snapshot, report, checks, run_url) + f"\n\n<!-- {marker} -->"
    pr = api(repository, "pulls", "POST", {"title": report["title"], "head": branch,
             "base": snapshot["base_branch"], "draft": True, "body": body})
    api(repository, f"issues/{snapshot['number']}/comments", "POST", {
        "body": f"Draft fix: {pr['html_url']}\n\n[Validation and run details]({run_url})"})
    print(pr["html_url"])


def render_pr(snapshot, report, checks, run_url):
    """Separate independently rerun checks from model evidence and surface unresolved full-suite failures."""
    parts = ["## Description", report["summary"], f"Fixes #{snapshot['number']}",
             "## Root cause", report["root_cause"], "## Why this fixes the general case", report["generality"],
             "## Original regression", f"`{report['regression_path']}` preserves the reported input; "
             "its marked standalone regression was rerun against both base and patched code.",
             "## Independent validation", f"Target: `{snapshot['base_branch']}` at `{snapshot['base_sha']}`. "
             f"[Validation diagnostics]({run_url})."]
    for name, check in checks.items():
        parts.append(f"- {name}: `{check['command']}` — exit {check['exit_code']}")
    parts.append("A nonzero base result alone does not prove the reported failure; review its diagnostic below.")
    parts.append("```text\n" + checks["original_base"]["tail"].replace("```", "` ` `") + "\n```")
    if checks["full_fixed"]["exit_code"] != 0:
        parts.append("**Full validation failed.** Equal nonzero exit codes do not establish that failures are "
                     "preexisting. Review the baseline and patched logs before accepting this draft.")
        for name in ["full_base", "full_fixed"]:
            parts.append(f"{name}:\n```text\n{checks[name]['tail'].replace('```', '` ` `')}\n```")
    parts.append("## Agent validation (reported, not independently verified)")
    parts.extend(f"- `{test['command']}`: {test['result']} — {test['evidence']}" for test in report["tests"])
    if report["limitations"]:
        parts.extend(["## Limitations", *report["limitations"]])
    parts.append("Draft for maintainer review; no automatic merge. No dependencies or toolchain changes are allowed by this runner.")
    return "\n\n".join(parts)


def main():
    """Dispatch one trusted pipeline phase; failures stop before a PR can be published."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["prepare", "initialize", "setup", "export", "validate", "publish"])
    phase = parser.parse_args().phase
    {"prepare": prepare, "initialize": initialize, "setup": setup, "export": export_patch,
     "validate": validate, "publish": publish}[phase]()


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, json.JSONDecodeError) as error:
        print(f"agent-fix: {error}", file=sys.stderr)
        sys.exit(1)
