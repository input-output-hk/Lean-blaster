#!/usr/bin/env python3
"""Acquire pinned solver inventories and run bounded, evidence-preserving probes."""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import resource
import selectors
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
import uuid
import zipfile

from check_manifest import ManifestError, fixture_path, validate_data, validate_manifest


class ProbeError(ValueError):
    """A categorized inventory or protocol failure."""


def fail(category: str, message: str) -> None:
    raise ProbeError(f"{category}: {message}")


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def check_checksum(path: Path, expected: str) -> None:
    regular_file(path)
    if digest(path) != expected:
        fail("checksum", f"SHA-256 mismatch: {path}")


def safe_path(path: Path) -> Path:
    """Reject symlink components rather than silently resolving them."""
    path = path.absolute()
    if ".." in path.parts:
        fail("artifact", f"parent traversal in path: {path}")
    for component in reversed((path, *path.parents)):
        try:
            mode = component.lstat().st_mode
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(mode):
            fail("artifact", f"symlink path component: {component}")
    return path


def regular_file(path: Path) -> None:
    safe_path(path)
    try:
        mode = path.lstat().st_mode
    except FileNotFoundError:
        fail("artifact", f"missing artifact: {path}")
    if not stat.S_ISREG(mode):
        fail("artifact", f"not a regular file: {path}")


def select_profile(manifest: dict, name: str) -> dict:
    if name not in manifest["profiles"]:
        fail("profile", f"unknown profile: {name}")
    return manifest["profiles"][name]


def select_platform(profile: dict, name: str) -> dict:
    if name not in profile["platforms"]:
        fail("platform", f"unknown platform: {name}")
    return profile["platforms"][name]


def host_platform(profile: dict) -> str:
    system = platform.system()
    machine = platform.machine().lower()
    machine = {"arm64": "aarch64", "amd64": "x86_64"}.get(machine, machine)
    matches = [name for name, value in profile["platforms"].items()
               if value["os"] == system and value["machine"] == machine]
    if len(matches) != 1:
        fail("platform", f"unsupported or ambiguous host: {system}/{machine}")
    return matches[0]


def identity(profile_name: str, profile: dict, platform_name: str) -> dict:
    # Qualification is an observation, not an input to a reproducible execution.
    bound = copy.deepcopy(profile)
    for target in bound["platforms"].values():
        target.pop("qualification", None)
    encoded = json.dumps(bound, sort_keys=True, separators=(",", ":")).encode()
    target = select_platform(profile, platform_name)
    return {
        "schema_version": 1, "profile": profile_name, "platform": platform_name,
        "profile_sha256": hashlib.sha256(encoded).hexdigest(),
        "source": profile["source"], "release": profile["release"],
        "archive_sha256": target["archive_sha256"],
        "executable_sha256": target["executable_sha256"],
        "expected_version": profile["expected_version"],
        "required_config": profile["required_config"], "argv": profile["argv"],
    }


def parse_sexpressions(data: bytes | str, max_bytes: int = 1048576,
                       max_depth: int = 128) -> list:
    """Parse SMT-LIB responses without executing or loosely splitting terms."""
    if isinstance(data, bytes):
        if len(data) > max_bytes:
            fail("oversized", "response exceeds byte limit")
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            fail("malformed", "response is not UTF-8")
    else:
        text = data
        if len(text.encode("utf-8")) > max_bytes:
            fail("oversized", "response exceeds byte limit")
    roots: list = []
    stack: list[list] = []
    i = 0
    while i < len(text):
        char = text[i]
        if char.isspace():
            i += 1
            continue
        if char == ";":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end + 1
            continue
        if char == "(":
            if len(stack) >= max_depth:
                fail("oversized", "S-expression depth limit exceeded")
            node: list = []
            (stack[-1] if stack else roots).append(node)
            stack.append(node)
            i += 1
            continue
        if char == ")":
            if not stack:
                fail("malformed", "unexpected closing parenthesis")
            stack.pop()
            i += 1
            continue
        start = i
        if char in ('"', '|'):
            quote = char
            i += 1
            while i < len(text):
                if text[i] == quote:
                    if quote == '"' and i + 1 < len(text) and text[i + 1] == '"':
                        i += 2
                        continue
                    i += 1
                    break
                if quote == '|' and text[i] == "\\":
                    fail("malformed", "backslash in quoted symbol")
                i += 1
            else:
                fail("truncated", "unterminated quoted token")
            if i < len(text) and not text[i].isspace() and text[i] not in "();":
                fail("malformed", "missing delimiter after quoted token")
        else:
            while i < len(text) and not text[i].isspace() and text[i] not in "();":
                if text[i] in ('"', '|') or ord(text[i]) < 32:
                    fail("malformed", "invalid atom character")
                i += 1
        (stack[-1] if stack else roots).append(text[start:i])
    if stack:
        fail("truncated", "unclosed S-expression")
    return roots


def decimal_value(value: str) -> int:
    # Stay below Python's decimal-conversion guard, even for hostile output.
    if len(value) > 4096:
        fail("oversized", "finite-field literal exceeds numeric length bound")
    return int(value)


def finite_field_value(actual: object) -> tuple[int, int] | None:
    if isinstance(actual, str):
        match = re.fullmatch(r"#f(-?[0-9]+)m([0-9]+)", actual)
        if match:
            return decimal_value(match[1]), decimal_value(match[2])
    if (isinstance(actual, list) and len(actual) == 3 and actual[0] == "as"
            and isinstance(actual[1], str) and isinstance(actual[2], list)
            and len(actual[2]) == 3 and actual[2][:2] == ["_", "FiniteField"]):
        value = re.fullmatch(r"ff(-?[0-9]+)", actual[1])
        modulus = actual[2][2]
        if value and isinstance(modulus, str) and re.fullmatch(r"[0-9]+", modulus):
            return decimal_value(value[1]), decimal_value(modulus)
    return None


def matches_expression(actual: object, expected: object) -> bool:
    if isinstance(expected, dict):
        field = expected.get("finite_field")
        value = finite_field_value(actual)
        return (field is not None and value is not None and value[1] > 0
                and value[1] == field["modulus"]
                and value[0] % value[1] == field["residue"])
    if isinstance(expected, list):
        return (isinstance(actual, list) and len(actual) == len(expected)
                and all(matches_expression(a, e) for a, e in zip(actual, expected)))
    return actual == expected


def validate_response(stdout: bytes | str, stderr: bytes | str, returncode: int,
                      case: dict, limits: dict) -> list:
    if returncode != case["expected_exit"]:
        fail("response", f"unexpected exit status: {returncode}")
    expected_stderr = case["expected_stderr"]
    if isinstance(stderr, bytes):
        if stderr != expected_stderr.encode():
            fail("response", "unexpected stderr")
    elif stderr != expected_stderr:
        fail("response", "unexpected stderr")
    expressions = parse_sexpressions(stdout, limits["output_bytes"], limits["sexpr_depth"])
    if any(isinstance(item, list) and item and item[0] == "error" for item in expressions):
        fail("response", "solver returned an error response")
    if not matches_expression(expressions, case["expected"]):
        fail("response", f"response mismatch: expected {case['expected']!r}, got {expressions!r}")
    return expressions


def reject_error_text(text: str) -> None:
    if re.search(r'\(\s*error(?:\s|\))|^\s*error(?:\s|:)', text, re.I | re.M):
        fail("response", "solver returned an error response")


def validate_version(stdout: bytes | str, expected: dict) -> None:
    text = stdout.decode("utf-8", errors="replace") if isinstance(stdout, bytes) else stdout
    reject_error_text(text)
    version = re.escape(expected["version"])
    revision = re.escape(expected["revision"])
    if not re.search(r"^(?:This is )?cvc5\s+(?:version\s+)?" + version + r"(?=\s|$)", text, re.I | re.M):
        fail("config", "solver version does not match pinned version")
    if not re.search(r"\[git\s+" + revision + r"[0-9a-f]*(?=\s|\])", text, re.I):
        fail("config", "solver revision does not match pinned source")


def validate_config(stdout: bytes | str, required: dict) -> None:
    text = stdout.decode("utf-8", errors="replace") if isinstance(stdout, bytes) else stdout
    reject_error_text(text)
    values: dict[str, str] = {}
    for line in text.splitlines():
        match = re.fullmatch(r"\s*([A-Za-z][A-Za-z0-9_-]*)\s*:\s*(.*?)\s*", line)
        if match:
            key, value = match[1].lower(), match[2].lower()
            if key in values:
                fail("config", f"duplicate configuration key: {key}")
            values[key] = value
    for key, expected in required.items():
        if values.get(key.lower()) != expected.lower():
            fail("config", f"{key}: expected {expected}, got {values.get(key.lower(), 'missing')}")


def archive_members(archive: zipfile.ZipFile, limits: dict) -> list[zipfile.ZipInfo]:
    members = archive.infolist()
    if len(members) > limits["archive_members"]:
        fail("oversized", "too many archive members")
    total = 0
    paths: dict[str, bool] = {}
    for member in members:
        name = member.filename
        if (not name or member.orig_filename != name or "\\" in name or "\x00" in name
                or name.startswith("/") or ":" in name
                or any(p in ("", ".", "..") for p in name.removesuffix("/").split("/"))):
            fail("archive", f"unsafe archive path: {name!r}")
        path = str(PurePosixPath(name))
        if path in paths:
            fail("archive", f"duplicate archive path: {path}")
        is_directory = member.is_dir()
        mode = member.external_attr >> 16
        kind = stat.S_IFMT(mode)
        if kind not in (0, stat.S_IFDIR if is_directory else stat.S_IFREG):
            fail("archive", f"nonregular archive member: {name}")
        if member.flag_bits & 1:
            fail("archive", f"encrypted archive member: {name}")
        paths[path] = is_directory
        total += member.file_size
        if total > limits["extracted_bytes"]:
            fail("oversized", "uncompressed archive exceeds byte limit")
    for path, is_directory in paths.items():
        for parent in PurePosixPath(path).parents:
            if str(parent) in paths and not paths[str(parent)]:
                fail("archive", f"archive file/directory conflict: {path}")
    return members


def inspect_archive(path: Path, limits: dict) -> None:
    regular_file(path)
    if path.stat().st_size > limits["archive_bytes"]:
        fail("oversized", "archive exceeds byte limit")
    try:
        with zipfile.ZipFile(path) as archive:
            archive_members(archive, limits)
    except (zipfile.BadZipFile, NotImplementedError, RuntimeError) as exc:
        fail("archive", str(exc))


def extract_archive(path: Path, destination: Path, limits: dict) -> None:
    try:
        with zipfile.ZipFile(path) as archive:
            members = archive_members(archive, limits)
            total = 0
            for member in members:
                target = destination.joinpath(*PurePosixPath(member.filename).parts)
                if member.is_dir():
                    target.mkdir(parents=True, exist_ok=True)
                    continue
                target.parent.mkdir(parents=True, exist_ok=True)
                written = 0
                with archive.open(member) as source, target.open("xb") as output:
                    while chunk := source.read(1024 * 1024):
                        total += len(chunk)
                        written += len(chunk)
                        if total > limits["extracted_bytes"] or written > member.file_size:
                            fail("oversized", "extracted archive exceeds declared limits")
                        output.write(chunk)
                if written != member.file_size:
                    fail("archive", f"truncated archive member: {member.filename}")
                target.chmod(0o644)
    except (zipfile.BadZipFile, NotImplementedError, RuntimeError) as exc:
        fail("archive", str(exc))


def fetch_archive(url: str, destination: Path, max_bytes: int) -> None:
    # Network-capable imports and operations live exclusively in acquisition.
    import urllib.request
    import urllib.parse

    allowed = {"github.com", "release-assets.githubusercontent.com", "objects.githubusercontent.com"}

    def check_url(value: str) -> None:
        parsed = urllib.parse.urlsplit(value)
        if (parsed.scheme != "https" or parsed.hostname not in allowed
                or parsed.username is not None or parsed.password is not None
                or parsed.port not in (None, 443) or parsed.fragment):
            fail("artifact", f"download URL is not allowed: {value}")

    class PinnedRedirect(urllib.request.HTTPRedirectHandler):
        def redirect_request(self, request, fp, code, message, headers, new_url):
            check_url(new_url)
            return super().redirect_request(request, fp, code, message, headers, new_url)

    check_url(url)
    opener = urllib.request.build_opener(PinnedRedirect())
    request = urllib.request.Request(url, headers={"User-Agent": "lean-blaster-pinned-probe"})
    deadline = time.monotonic() + 300
    with opener.open(request, timeout=30) as response, destination.open("xb") as output:
        check_url(response.geturl())
        length = response.headers.get("Content-Length")
        if length is not None and (not length.isdigit() or int(length) > max_bytes):
            fail("oversized", "download Content-Length exceeds archive bound")
        total = 0
        while chunk := response.read(min(1024 * 1024, max_bytes - total + 1)):
            total += len(chunk)
            if total > max_bytes:
                fail("oversized", "download exceeds archive bound")
            if time.monotonic() > deadline:
                fail("artifact", "download wall-time exceeded")
            output.write(chunk)


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def read_metadata(path: Path) -> dict:
    regular_file(path)
    if path.stat().st_size > 1048576:
        fail("oversized", "inventory metadata exceeds byte limit")

    def unique_pairs(pairs: list) -> dict:
        result = {}
        for key, value in pairs:
            if key in result:
                fail("artifact", f"duplicate metadata key: {key}")
            result[key] = value
        return result

    try:
        metadata = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_pairs)
    except (ValueError, UnicodeError, RecursionError) as exc:
        fail("artifact", f"invalid inventory metadata: {exc}")
    if not isinstance(metadata, dict):
        fail("artifact", "inventory metadata must be an object")
    return metadata


def acquire(manifest: dict, root: Path, profile_name: str, requested_platform: str | None) -> Path:
    profile = select_profile(manifest, profile_name)
    name = requested_platform or host_platform(profile)
    target = select_platform(profile, name)
    root = safe_path(root)
    root.mkdir(parents=True, exist_ok=True)
    final = root / profile_name
    if final.exists() or final.is_symlink():
        fail("artifact", f"destination already exists: {final}")
    # A root is one platform inventory, including profiles introduced later.
    for child in root.iterdir():
        if not child.is_dir() or child.is_symlink() or child.name.startswith("."):
            continue
        metadata_path = child / "metadata.json"
        existing = read_metadata(metadata_path)
        if existing.get("platform") != name:
            fail("platform", "alternate platforms require a separate artifact root")
    staging = profile["staging"]
    temporary = Path(tempfile.mkdtemp(prefix=f".{profile_name}-", dir=root))
    try:
        archive = temporary / staging["archive"]
        fetch_archive(target["archive_url"], archive, profile["limits"]["archive_bytes"])
        check_checksum(archive, target["archive_sha256"])
        inspect_archive(archive, profile["limits"])
        payload = temporary / staging["payload"]
        payload.mkdir()
        extract_archive(archive, payload, profile["limits"])
        original = payload / target["executable_member"]
        check_checksum(original, target["executable_sha256"])
        executable = temporary / staging["executable"]
        executable.parent.mkdir(parents=True)
        shutil.copyfile(original, executable)
        executable.chmod(0o755)
        check_checksum(executable, target["executable_sha256"])
        write_json(temporary / staging["metadata"], identity(profile_name, profile, name))
        (temporary / staging["evidence"]).mkdir()
        # An exclusive lock avoids replacement by another cooperating acquisition.
        lock = root / f".{profile_name}.lock"
        try:
            lock_fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
        except FileExistsError:
            fail("artifact", "another acquisition holds the profile lock")
        try:
            os.close(lock_fd)
            if final.exists() or final.is_symlink():
                fail("artifact", f"destination already exists: {final}")
            temporary.rename(final)
        finally:
            lock.unlink()
        return final
    finally:
        if temporary.exists():
            shutil.rmtree(temporary)


def prohibit_network() -> None:
    """Enforce no Python network access; this is not a child-process sandbox."""
    def deny(event: str, args: tuple) -> None:
        if event.startswith("socket.") or event in ("urllib.Request", "http.client.connect"):
            fail("network", f"offline mode forbids {event}")
    sys.addaudithook(deny)


def validate_metadata(metadata: dict, expected: dict) -> None:
    if metadata.get("profile") != expected["profile"]:
        fail("profile", "staged metadata names a different profile")
    if metadata.get("platform") != expected["platform"]:
        fail("platform", "staged metadata does not match the host platform")
    if metadata != expected:
        fail("artifact", "metadata does not match pinned identity/configuration")


def check_inventory(manifest: dict, root: Path, profile_name: str) -> tuple[dict, Path]:
    profile = select_profile(manifest, profile_name)
    name = host_platform(profile)
    target = select_platform(profile, name)
    directory = safe_path(root / profile_name)
    staging = profile["staging"]
    metadata_path = directory / staging["metadata"]
    metadata = read_metadata(metadata_path)
    validate_metadata(metadata, identity(profile_name, profile, name))
    archive = directory / staging["archive"]
    regular_file(archive)
    if archive.stat().st_size > profile["limits"]["archive_bytes"]:
        fail("oversized", "archive exceeds byte limit")
    check_checksum(archive, target["archive_sha256"])
    inspect_archive(archive, profile["limits"])
    original = directory / staging["payload"] / target["executable_member"]
    executable = directory / staging["executable"]
    check_checksum(original, target["executable_sha256"])
    check_checksum(executable, target["executable_sha256"])
    if not os.access(executable, os.X_OK):
        fail("artifact", "pinned executable is not executable")
    return profile, directory


def run_process(argv: list[str], stdin: bytes, evidence: Path, limits: dict) -> dict:
    """Keep raw evidence for every execution, including spawn and bounds failures."""
    evidence.mkdir()
    (evidence / "input.smt2").write_bytes(stdin)
    write_json(evidence / "argv.json", argv)
    (evidence / "argv.sh").write_text(shlex.join(argv) + "\n", encoding="utf-8")
    result = {"returncode": None, "failure": None, "truncated": False,
              "stdout_bytes": 0, "stderr_bytes": 0, "elapsed_seconds": 0.0}
    started = time.monotonic()

    def set_limits() -> None:
        resource.setrlimit(resource.RLIMIT_CPU, (limits["cpu_seconds"], limits["cpu_seconds"]))
        resource.setrlimit(resource.RLIMIT_AS, (limits["memory_bytes"], limits["memory_bytes"]))
        resource.setrlimit(resource.RLIMIT_FSIZE, (limits["output_bytes"], limits["output_bytes"]))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    process = None
    selector = selectors.DefaultSelector()
    with (evidence / "input.smt2").open("rb") as source, \
            (evidence / "stdout.bin").open("wb") as stdout, \
            (evidence / "stderr.bin").open("wb") as stderr:
        try:
            process = subprocess.Popen(argv, stdin=source, stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE, cwd=evidence,
                                       env={"LANG": "C", "LC_ALL": "C", "HOME": str(evidence)},
                                       start_new_session=True, preexec_fn=set_limits,
                                       close_fds=True)
            for stream, output, key in ((process.stdout, stdout, "stdout_bytes"),
                                        (process.stderr, stderr, "stderr_bytes")):
                os.set_blocking(stream.fileno(), False)
                selector.register(stream, selectors.EVENT_READ, (output, key))
            total = 0
            killed_at = None
            while selector.get_map() or process.poll() is None:
                now = time.monotonic()
                if result["failure"] is None and now - started >= limits["wall_seconds"]:
                    result["failure"] = "timeout: wall-time limit exceeded"
                    result["truncated"] = True
                if result["failure"] and killed_at is None:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    killed_at = now
                if killed_at is not None and now - killed_at > 2:
                    break
                for key, _ in selector.select(0.05):
                    stream = key.fileobj
                    chunk = os.read(stream.fileno(), 65536)
                    if not chunk:
                        selector.unregister(stream)
                        stream.close()
                        continue
                    output, count_key = key.data
                    room = max(0, limits["output_bytes"] - total)
                    retained = chunk[:room]
                    output.write(retained)
                    result[count_key] += len(retained)
                    total += len(retained)
                    if len(chunk) > room:
                        result["failure"] = "oversized: combined subprocess output exceeds byte limit"
                        result["truncated"] = True
            result["returncode"] = process.wait(timeout=2)
            if result["returncode"] != 0 and result["failure"] is None:
                result["failure"] = f"response: subprocess exited {result['returncode']} (possibly resource limit)"
        except (OSError, subprocess.SubprocessError) as exc:
            result["failure"] = f"execution: {exc}"
        finally:
            if process is not None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    result["failure"] = "timeout: process did not terminate after SIGKILL"
                result["returncode"] = process.returncode
                for stream in (process.stdout, process.stderr):
                    if stream is not None:
                        stream.close()
            selector.close()
            result["elapsed_seconds"] = round(time.monotonic() - started, 6)
            write_json(evidence / "status.json", result)
    return result


def execution_output(result: dict, evidence: Path) -> tuple[bytes, bytes]:
    if result["failure"]:
        raise ProbeError(result["failure"])
    return (evidence / "stdout.bin").read_bytes(), (evidence / "stderr.bin").read_bytes()


def offline_check(manifest: dict, manifest_path: Path, root: Path, profile_name: str) -> dict:
    profile, directory = check_inventory(manifest, root, profile_name)
    cases = profile["cases"]
    if not cases:
        fail("profile", "refusing to qualify zero cases")
    executable = str(directory / profile["staging"]["executable"])
    evidence_root = safe_path(directory / profile["staging"]["evidence"])
    evidence_root.mkdir(exist_ok=True)
    run = evidence_root / (time.strftime("run-%Y%m%dT%H%M%SZ", time.gmtime()) + "-" + uuid.uuid4().hex)
    run.mkdir()
    summary = {"profile": profile_name, "platform": host_platform(profile),
               "evidence": str(run), "configuration": {}, "cases": {}, "capabilities": {}, "passed": False}
    failures: list[str] = []
    for label, flag, validator, expectation in (
            ("version", "--version", validate_version, profile["expected_version"]),
            ("config", "--show-config", validate_config, profile["required_config"])):
        execution = run / label
        result = run_process([executable, flag], b"", execution, profile["limits"])
        try:
            stdout, stderr = execution_output(result, execution)
            if stderr:
                fail("config", f"{flag} emitted stderr")
            validator(stdout, expectation)
            summary["configuration"][label] = {"passed": True}
        except ProbeError as exc:
            summary["configuration"][label] = {"passed": False, "error": str(exc)}
            failures.append(str(exc))
    # Do not run solver inputs with a configuration that failed qualification.
    if not failures:
        for case in cases:
            execution = run / ("case-" + case["id"])
            source = fixture_path(manifest_path, case["input"]).read_bytes()
            result = run_process([executable, *profile["argv"]], source, execution, profile["limits"])
            try:
                stdout, stderr = execution_output(result, execution)
                validate_response(stdout, stderr, result["returncode"], case, profile["limits"])
                summary["cases"][case["id"]] = {"passed": True}
            except ProbeError as exc:
                summary["cases"][case["id"]] = {"passed": False, "error": str(exc)}
                failures.append(f"{case['id']}: {exc}")
    for capability, requirement in profile["capabilities"].items():
        case_ids = requirement.get("cases", [])
        passed = bool(case_ids) and all(summary["cases"].get(case_id, {}).get("passed", False)
                                        for case_id in case_ids)
        summary["capabilities"][capability] = {
            "required": requirement["required"], "passed": passed,
            "status": "passed" if passed else requirement.get("status", "failed"),
        }
        if requirement["required"] and not passed:
            failures.append(f"profile: required capability failed: {capability}")
    summary["passed"] = not failures and len(summary["cases"]) == len(cases)
    summary["failures"] = failures
    write_json(run / "summary.json", summary)
    if not summary["passed"]:
        fail("response", f"qualification failed; evidence: {run}; {'; '.join(failures)}")
    return summary


def negative_operation(entry: dict, manifest: dict, manifest_path: Path, temporary: Path) -> None:
    operation = entry["operation"]
    if operation == "manifest":
        candidate = copy.deepcopy(manifest)
        current = candidate
        for part in entry["path"][:-1]:
            current = current[part]
        current[entry["path"][-1]] = entry["value"]
        validate_data(candidate, manifest_path)
    elif operation == "profile":
        select_profile(manifest, entry["name"])
    elif operation == "platform":
        select_platform(next(iter(manifest["profiles"].values())), entry["name"])
    elif operation == "config":
        validate_config(entry["stdout"], entry["required"])
    elif operation == "version":
        validate_version(entry["stdout"], entry["expected"])
    elif operation == "metadata":
        name, profile = next(iter(manifest["profiles"].items()))
        expected = identity(name, profile, next(iter(profile["platforms"])))
        metadata = copy.deepcopy(expected)
        metadata[entry["field"]] = entry["value"]
        validate_metadata(metadata, expected)
    elif operation == "response":
        validate_response(entry["stdout"], entry.get("stderr", ""), entry.get("returncode", 0),
                          {"expected": entry["expected"], "expected_exit": 0, "expected_stderr": ""},
                          {"output_bytes": entry.get("max_bytes", 4096),
                           "sexpr_depth": entry.get("max_depth", 32)})
    elif operation == "archive":
        path = temporary / "unsafe.zip"
        with zipfile.ZipFile(path, "w") as archive:
            for member in entry["members"]:
                info = zipfile.ZipInfo(member["name"])
                info.create_system = 3
                info.external_attr = member.get("mode", stat.S_IFREG | 0o644) << 16
                archive.writestr(info, member.get("content", ""))
        inspect_archive(path, {"archive_members": 100, "archive_bytes": 100000,
                               "extracted_bytes": 100000})
    elif operation in ("checksum", "missing"):
        path = temporary / "artifact"
        if operation == "checksum":
            path.write_text(entry["content"], encoding="utf-8")
        check_checksum(path, entry["sha256"])
    else:
        fail("fixture", f"unknown negative operation: {operation}")


def run_negative(manifest: dict, manifest_path: Path, fixtures: Path | None = None) -> dict:
    path = fixtures or fixture_path(manifest_path, manifest["negative_fixtures"])
    try:
        entries = json.loads(path.read_text(encoding="utf-8"))
    except (ValueError, UnicodeError, OSError) as exc:
        fail("fixture", f"cannot load negative fixtures: {exc}")
    if not isinstance(entries, list) or not entries:
        fail("fixture", "negative fixtures must be a nonempty list")
    results = []
    for entry in entries:
        if (not isinstance(entry, dict) or not isinstance(entry.get("id"), str)
                or not isinstance(entry.get("expected_category"), str)):
            fail("fixture", "invalid negative fixture envelope")
        with tempfile.TemporaryDirectory(prefix="finite-fields-negative-") as directory:
            try:
                negative_operation(entry, manifest, manifest_path, Path(directory))
            except (ProbeError, ManifestError) as exc:
                category = str(exc).partition(":")[0]
                if category != entry["expected_category"]:
                    fail("fixture", f"{entry['id']}: expected {entry['expected_category']}, got {exc}")
                results.append({"id": entry["id"], "passed": True, "error": str(exc)})
            else:
                fail("fixture", f"{entry['id']}: invalid input was accepted")
    return {"passed": True, "negative_cases": results}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--artifact-root", type=Path)
    parser.add_argument("--profile")
    parser.add_argument("--platform", help="acquisition only; alternate platforms require separate roots")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--fetch-only", action="store_true")
    mode.add_argument("--check", action="store_true", help="offline check (the default)")
    mode.add_argument("--negative-fixtures", action="store_true")
    parser.add_argument("--offline", action="store_true", help="explicitly prohibit acquisition/network access")
    args = parser.parse_args(argv)
    if args.offline and args.fetch_only:
        parser.error("--offline and --fetch-only are mutually exclusive")
    if args.platform and not args.fetch_only:
        parser.error("--platform is allowed only with --fetch-only")
    if not args.negative_fixtures and (args.artifact_root is None or args.profile is None):
        parser.error("--artifact-root and --profile are required for acquisition/offline checks")
    if not args.fetch_only:
        prohibit_network()
    try:
        manifest_path = args.manifest.absolute()
        manifest = validate_manifest(manifest_path)
        if args.negative_fixtures:
            result = run_negative(manifest, manifest_path)
        elif args.fetch_only:
            path = acquire(manifest, args.artifact_root, args.profile, args.platform)
            result = {"staged": str(path), "qualified": False}
        else:
            result = offline_check(manifest, manifest_path, args.artifact_root, args.profile)
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    except (ProbeError, ManifestError, OSError, ValueError) as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
