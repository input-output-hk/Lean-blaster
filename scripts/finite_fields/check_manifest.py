#!/usr/bin/env python3
"""Validate pinned solver identities and local protocol fixtures (stdlib only).

This does not fetch or execute a solver and does not establish qualification.
Fixture paths are repository-relative to a manifest in docs/finite-fields/.
"""

import argparse
import json
import re
import sys
from pathlib import Path, PurePosixPath
from urllib.parse import urlsplit


class ManifestError(ValueError):
    """A categorized invalid manifest or fixture."""


FIXTURE_ROOT = "fixtures/finite-fields/protocol"
SAFE_COMPONENT = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*\Z")
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
PRODUCTION_PREFIX = [
    ["set-option", ":print-success", "true"],
    ["set-option", ":produce-models", "true"],
    ["set-option", ":produce-proofs", "true"],
    ["set-option", ":mbqi", "true"],
    ["set-option", ":macros-quant", "true"],
    ["set-logic", "ALL"],
    ["get-option", ":ff-field-polys"],
    ["get-option", ":ff-solver"],
]
PRODUCTION_ARGV = [
    "--lang", "smt2", "--incremental", "--parsing-mode=lenient", "--dt-nested-rec"
]
LIMIT_MAX = {
    "wall_seconds": 3600,
    "cpu_seconds": 3600,
    "memory_bytes": 64 * 1024**3,
    "output_bytes": 64 * 1024**2,
    "archive_bytes": 8 * 1024**3,
    "extracted_bytes": 32 * 1024**3,
    "archive_members": 1000000,
    "sexpr_depth": 256,
}


def fail(category, message):
    raise ManifestError(f"{category}: {message}")


def object_fields(value, required, where, optional=()):
    if not isinstance(value, dict):
        fail("schema", f"{where} must be an object")
    missing = set(required) - value.keys()
    extra = value.keys() - set(required) - set(optional)
    if missing or extra:
        fail("schema", f"{where}: missing {sorted(missing)}, unknown {sorted(extra)}")


def text(value, where):
    if not isinstance(value, str) or not value.strip() or "\x00" in value:
        fail("schema", f"{where} must be a nonempty string without NUL")


def component(value, where):
    text(value, where)
    if not SAFE_COMPONENT.fullmatch(value) or value in (".", ".."):
        fail("profile", f"{where} must be a safe single path component")


def integer(value, where, maximum=None):
    if type(value) is not int or value <= 0 or (maximum is not None and value > maximum):
        fail("schema", f"{where} must be a positive integer" + (f" <= {maximum}" if maximum else ""))


def https_url(value, where):
    text(value, where)
    try:
        parsed = urlsplit(value)
        valid = (parsed.scheme == "https" and parsed.hostname and not parsed.username
                 and not parsed.password and parsed.port in (None, 443)
                 and not parsed.query and not parsed.fragment)
    except ValueError:
        valid = False
    if not valid or any(c.isspace() for c in value):
        fail("profile", f"{where} must be an unambiguous HTTPS URL without credentials/query/fragment")
    return parsed


def fixture_path(manifest_path: Path, relative: str) -> Path:
    """Resolve a repository-relative fixture, rejecting traversal and symlinks."""
    text(relative, "fixture path")
    parts = relative.split("/")
    if ("\\" in relative or relative.startswith("/")
            or any(p in ("", ".", "..") for p in parts)
            or not relative.startswith(FIXTURE_ROOT + "/")):
        fail("fixture", f"unsafe fixture path {relative!r}")
    root = Path(manifest_path).absolute().parent.parent.parent.resolve()
    candidate = root
    for part in parts:
        candidate = candidate / part
        if candidate.is_symlink():
            fail("fixture", f"symlink forbidden in fixture path {relative!r}")
    if not candidate.resolve().is_relative_to(root):
        fail("fixture", f"fixture escapes repository: {relative!r}")
    if not candidate.is_file():
        fail("fixture", f"missing regular fixture file {relative!r}")
    return candidate


def _pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            fail("schema", f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def _constant(value):
    fail("schema", f"non-finite JSON number {value}")


def load_json(path, maximum=4 * 1024**2):
    try:
        with Path(path).open("rb") as stream:
            raw = stream.read(maximum + 1)
        if len(raw) > maximum:
            fail("oversized", f"JSON file {path} exceeds {maximum} bytes")
        return json.loads(raw.decode("utf-8"), object_pairs_hook=_pairs, parse_constant=_constant)
    except (OSError, UnicodeError, json.JSONDecodeError, RecursionError) as exc:
        fail("schema", f"cannot read JSON {path}: {exc}")


def _parse_fixture(path, depth_limit):
    """Read SMT-LIB commands, respecting comments, strings and quoted symbols."""
    try:
        with path.open("rb") as stream:
            raw = stream.read(1024**2 + 1)
        if len(raw) > 1024**2:
            fail("oversized", f"fixture {path} exceeds 1 MiB")
        source = raw.decode("utf-8")
    except (OSError, UnicodeError) as exc:
        fail("fixture", f"cannot read {path}: {exc}")
    roots = []
    stack = [roots]
    i = 0
    while i < len(source):
        ch = source[i]
        if ch.isspace():
            i += 1
        elif ch == ";":
            end = source.find("\n", i)
            i = len(source) if end < 0 else end + 1
        elif ch == "(":
            if len(stack) > depth_limit:
                fail("fixture", f"nesting exceeds sexpr_depth in {path}")
            node = []
            stack[-1].append(node)
            stack.append(node)
            i += 1
        elif ch == ")":
            if len(stack) == 1:
                fail("fixture", f"unmatched ')' in {path}")
            stack.pop()
            i += 1
        elif ch in ('"', '|'):
            start, quote = i, ch
            i += 1
            while i < len(source):
                if source[i] == quote:
                    if quote == '"' and i + 1 < len(source) and source[i + 1] == '"':
                        i += 2
                        continue
                    i += 1
                    break
                if source[i] == "\x00" or (quote == '|' and source[i] == "\\"):
                    fail("fixture", f"invalid quoted token in {path}")
                i += 1
            else:
                fail("fixture", f"unterminated quoted token in {path}")
            stack[-1].append(source[start:i])
        else:
            start = i
            while i < len(source) and not source[i].isspace() and source[i] not in '();"|':
                if source[i] == "\x00":
                    fail("fixture", f"NUL in {path}")
                i += 1
            stack[-1].append(source[start:i])
    if len(stack) != 1:
        fail("fixture", f"unclosed expression in {path}")
    if not roots or any(not isinstance(cmd, list) or not cmd or not isinstance(cmd[0], str) for cmd in roots):
        fail("fixture", f"{path} must contain nonempty SMT commands")
    return roots


def _expected_expression(value, where, limit, depth=0):
    if depth > limit:
        fail("schema", f"{where} exceeds sexpr_depth")
    if isinstance(value, str):
        text(value, where)
        if not (re.fullmatch(r'[^\s();"|]+', value)
                or re.fullmatch(r'"(?:[^"]|"")*"', value)
                or re.fullmatch(r'\|[^|\\]*\|', value)):
            fail("schema", f"{where}: an atom must be one SMT token, not a serialized expression")
    elif isinstance(value, list):
        for child in value:
            _expected_expression(child, where, limit, depth + 1)
    elif isinstance(value, dict):
        if depth == 0:
            fail("schema", f"{where}: finite_field matchers belong at term positions")
        object_fields(value, ("finite_field",), where)
        field = value["finite_field"]
        object_fields(field, ("residue", "modulus"), where + ".finite_field")
        integer(field["modulus"], where + ".modulus")
        if (field["modulus"] < 2 or type(field["residue"]) is not int
                or not 0 <= field["residue"] < field["modulus"]):
            fail("schema", f"{where}: finite-field residue must be canonical and modulus >= 2")
    else:
        fail("schema", f"{where} must contain string atoms, lists or finite_field matchers")


def _case(case, profile, manifest_path, deferred):
    object_fields(case, ("id", "input", "expected", "expected_exit", "expected_stderr"), "case")
    component(case["id"], "case.id")
    label = "case " + case["id"]
    path = fixture_path(manifest_path, case["input"])
    if path.suffix != ".smt2":
        fail("fixture", f"{label} input must be .smt2")
    if type(case["expected_exit"]) is not int or case["expected_exit"] != 0:
        fail("schema", f"{label}.expected_exit must be 0")
    if case["expected_stderr"] != "":
        fail("schema", f"{label}.expected_stderr must be empty")
    expected = case["expected"]
    if not isinstance(expected, list) or not expected:
        fail("schema", f"{label}.expected must be a nonempty response list")
    for expression in expected:
        _expected_expression(expression, label + ".expected", profile["limits"]["sexpr_depth"])
    commands = _parse_fixture(path, profile["limits"]["sexpr_depth"])
    if commands[:len(PRODUCTION_PREFIX)] != PRODUCTION_PREFIX:
        fail("fixture", f"{label} must begin with the full production handshake")
    if deferred and any(cmd[0] == "get-proof" for cmd in commands):
        fail("profile", f"{label} requests a proof although proof_export is deferred")
    if expected[:8] != ["success"] * 6 + ["false", "gb"]:
        fail("response", f"{label} must expect all eight production handshake responses")
    responses = 8
    checks = 0
    assertions = 0
    model = False
    result = None
    print_success = True
    declarations = {}
    success_commands = {"set-option", "set-info", "set-logic", "declare-fun", "declare-const",
                        "declare-sort", "define-fun", "define-fun-rec", "define-funs-rec",
                        "define-sort", "declare-datatype", "declare-datatypes", "assert", "push", "pop",
                        "reset", "reset-assertions"}
    for cmd in commands[8:]:
        op = cmd[0]
        if op == "set-option" and len(cmd) >= 2 and cmd[1] == ":ff-field-polys":
            if len(cmd) != 3 or cmd[2] != "false":
                fail("fixture", f"{label} must keep ff-field-polys disabled")
        if op == "set-option" and len(cmd) == 3 and cmd[1] == ":print-success":
            if cmd[2] not in ("true", "false"):
                fail("fixture", f"{label} has invalid print-success option")
            print_success = cmd[2] == "true"
        if op in ("declare-fun", "declare-const"):
            sort = cmd[-1]
            if isinstance(sort, list) and len(sort) == 3 and sort[:2] == ["_", "FiniteField"]:
                if not isinstance(sort[2], str) or not sort[2].isdigit() or int(sort[2]) < 2:
                    fail("fixture", f"{label} has invalid finite-field sort")
                if len(cmd) > 1 and isinstance(cmd[1], str):
                    declarations[cmd[1]] = int(sort[2])
        if op == "assert":
            assertions += 1
        if op == "exit" or (op in success_commands and not print_success):
            continue
        if responses >= len(expected):
            fail("response", f"{label} lacks expected response for {op}")
        response = expected[responses]
        responses += 1
        if op in success_commands:
            if response != "success":
                fail("response", f"{label} must expect success for {op}")
        elif op in ("check-sat", "check-sat-assuming"):
            checks += 1
            if response not in ("sat", "unsat"):
                fail("response", f"{label} must expect definitive sat or unsat")
            result = response
        elif op == "get-value":
            model = True
            if result != "sat" or len(cmd) != 2 or not isinstance(cmd[1], list) or not cmd[1]:
                fail("response", f"{label} get-value must follow sat and query nonempty terms")
            if not isinstance(response, list) or len(response) != len(cmd[1]):
                fail("response", f"{label} model must answer each queried term")
            for term, pair in zip(cmd[1], response):
                if not isinstance(pair, list) or len(pair) != 2 or pair[0] != term:
                    fail("response", f"{label} model term does not match get-value")
                if isinstance(term, str) and term in declarations:
                    if (not isinstance(pair[1], dict) or "finite_field" not in pair[1]
                            or pair[1]["finite_field"]["modulus"] != declarations[term]):
                        fail("response", f"{label} model must match declared finite-field modulus")
        elif op == "get-proof":
            if result != "unsat" or not isinstance(response, list) or not response:
                fail("response", f"{label} proof must follow unsat with a nonempty structured response")
        # Other queries deliberately use their manifest-described expression.
        # This permits future proof formats/options without changing this script.
    if responses != len(expected):
        fail("response", f"{label} has extra expected responses")
    if not checks or not assertions:
        fail("fixture", f"{label} must contain assertions and a satisfiability check")
    return {"setup": True, "solving": bool(checks), "model": model,
            "proof_export": any(cmd[0] == "get-proof" for cmd in commands)}


def _profile(name, profile, manifest_path):
    component(name, "profile name")
    object_fields(profile, ("purpose", "source", "release", "provenance", "license", "executable_name",
                           "staging", "expected_version", "required_config", "argv", "limits",
                           "capabilities", "platforms", "cases"), "profile " + name)
    for key in ("purpose", "provenance", "license"):
        text(profile[key], name + "." + key)
    source = profile["source"]
    object_fields(source, ("repository", "commit"), name + ".source")
    https_url(source["repository"], name + ".source.repository")
    if not isinstance(source["commit"], str) or not HEX40.fullmatch(source["commit"]):
        fail("profile", f"{name}.source.commit must pin a full lowercase 40-hex commit")
    release = profile["release"]
    object_fields(release, ("url", "api_id", "immutable"), name + ".release")
    https_url(release["url"], name + ".release.url")
    integer(release["api_id"], name + ".release.api_id")
    if type(release["immutable"]) is not bool:
        fail("schema", f"{name}.release.immutable must be boolean")
    release_prefix = source["repository"].rstrip("/") + "/releases/tag/"
    if not release["url"].startswith(release_prefix):
        fail("profile", f"{name}.release.url must identify a release tag of source.repository")
    tag = release["url"][len(release_prefix):]
    component(tag, name + ".release tag")
    executable = profile["executable_name"]
    component(executable, name + ".executable_name")
    staging = profile["staging"]
    required_staging = {"executable": "bin/" + executable, "archive": "archive.zip",
                        "metadata": "metadata.json", "payload": "payload", "evidence": "evidence"}
    object_fields(staging, required_staging, name + ".staging")
    if staging != required_staging:
        fail("profile", f"{name}.staging must use the fixed isolated artifact layout")
    version = profile["expected_version"]
    object_fields(version, ("version", "revision"), name + ".expected_version")
    if not isinstance(version["version"], str) or not re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+[A-Za-z0-9._@+-]*", version["version"]):
        fail("profile", f"{name}.expected_version.version must be an exact safe version token")
    if (not isinstance(version["revision"], str) or not re.fullmatch(r"[0-9a-f]{7,40}", version["revision"])
            or not source["commit"].startswith(version["revision"])):
        fail("profile", f"{name}.expected_version.revision must identify source.commit")
    config = profile["required_config"]
    if not isinstance(config, dict) or not {"cocoa", "poly", "cln", "glpk", "gmp", "assertions"} <= config.keys():
        fail("config", f"{name}.required_config must include cocoa/poly/cln/glpk/gmp/assertions")
    for key, value in config.items():
        component(key, name + ".required_config key")
        if value not in ("yes", "no"):
            fail("config", f"{name}.required_config.{key} must be yes or no")
    if config["cocoa"] != "yes" or config["poly"] != "yes":
        fail("config", f"{name} requires cocoa:yes and poly:yes for finite-field solving")
    argv = profile["argv"]
    if not isinstance(argv, list) or argv[:len(PRODUCTION_ARGV)] != PRODUCTION_ARGV:
        fail("profile", f"{name}.argv must begin with the production solver arguments")
    for arg in argv:
        text(arg, name + ".argv item")
    limits = profile["limits"]
    object_fields(limits, LIMIT_MAX, name + ".limits")
    for key, maximum in LIMIT_MAX.items():
        integer(limits[key], name + ".limits." + key, maximum)
    if limits["cpu_seconds"] > limits["wall_seconds"]:
        fail("profile", f"{name} CPU limit must not exceed wall limit")
    capabilities = profile["capabilities"]
    if not isinstance(capabilities, dict) or not {"setup", "solving", "model", "proof_export"} <= capabilities.keys():
        fail("schema", f"{name}.capabilities must declare setup/solving/model/proof_export")
    for capability, declaration in capabilities.items():
        component(capability, name + ".capability")
        object_fields(declaration, ("required",), name + ".capabilities." + capability, ("cases", "status"))
        if type(declaration["required"]) is not bool:
            fail("schema", f"{name}.{capability}.required must be boolean")
        if "status" in declaration:
            text(declaration["status"], name + "." + capability + ".status")
        if "cases" in declaration:
            refs = declaration["cases"]
            if not isinstance(refs, list) or any(not isinstance(ref, str) for ref in refs) or len(set(refs)) != len(refs):
                fail("schema", f"{name}.{capability}.cases must be unique case ID strings")
        if declaration["required"] and not declaration.get("cases"):
            fail("profile", f"{name}.{capability} requires nonempty case references")
        if not declaration["required"] and not declaration.get("status"):
            fail("profile", f"{name}.{capability} must explain its non-required status")
    proof = capabilities["proof_export"]
    deferred = proof.get("status", "").lower().startswith("deferred")
    if deferred and (proof["required"] or proof.get("cases")):
        fail("profile", f"{name}.proof_export cannot require deferred proof cases")
    platforms = profile["platforms"]
    if not isinstance(platforms, dict) or not platforms:
        fail("schema", f"{name}.platforms must be a nonempty map")
    for key, platform in platforms.items():
        component(key, name + ".platform")
        object_fields(platform, ("os", "machine", "archive_url", "asset_id", "archive_sha256",
                                 "executable_member", "executable_sha256", "qualification"), name + "." + key)
        machine = {"linux-arm64": "aarch64", "linux-x86_64": "x86_64"}.get(key)
        if machine is None or platform["os"] != "Linux" or platform["machine"] != machine:
            fail("platform", f"{name}.{key} must name its supported Linux host architecture")
        parsed = https_url(platform["archive_url"], name + "." + key + ".archive_url")
        download_prefix = source["repository"].rstrip("/") + "/releases/download/" + tag + "/"
        if not platform["archive_url"].startswith(download_prefix):
            fail("profile", f"{name}.{key}.archive_url must pin an asset of release.url")
        archive_name = platform["archive_url"][len(download_prefix):]
        component(archive_name, name + ".archive filename")
        if not parsed.path.endswith(".zip"):
            fail("profile", f"{name}.{key} archive must be a ZIP asset")
        integer(platform["asset_id"], name + "." + key + ".asset_id")
        for hash_key in ("archive_sha256", "executable_sha256"):
            if not isinstance(platform[hash_key], str) or not HEX64.fullmatch(platform[hash_key]):
                fail("checksum", f"{name}.{key}.{hash_key} must be lowercase SHA-256 hex")
        if platform["executable_member"] != str(PurePosixPath(archive_name[:-4]) / "bin" / executable):
            fail("profile", f"{name}.{key}.executable_member must be <zipstem>/bin/<executable_name>")
        qualification = platform["qualification"]
        object_fields(qualification, ("status", "scope", "capabilities"), name + ".qualification",
                      ("date", "evidence"))
        if qualification["status"] not in ("not run", "passed", "failed"):
            fail("schema", f"{name}.{key}.qualification.status must be not run, passed or failed")
        for qkey in qualification.keys() - {"capabilities"}:
            text(qualification[qkey], name + ".qualification." + qkey)
        recorded = qualification["capabilities"]
        object_fields(recorded, capabilities, name + ".qualification.capabilities")
        for capability, status in recorded.items():
            text(status, name + ".qualification.capabilities." + capability)
            if status not in ("passed", "failed", "not run") and not status.startswith("deferred"):
                fail("schema", f"{name}.{key}: invalid recorded capability status")
            if (qualification["status"] == "passed" and capabilities[capability]["required"]
                    and status != "passed"):
                fail("schema", f"{name}.{key}: passed qualification has an unpassed required capability")
        if qualification["status"] == "passed" and "evidence" not in qualification:
            fail("fixture", f"{name}.{key}: passed qualification requires retained evidence")
        if "evidence" in qualification:
            evidence = fixture_path(manifest_path, qualification["evidence"])
            if evidence.suffix != ".json" or not isinstance(load_json(evidence), dict):
                fail("fixture", f"{name}.{key}: qualification evidence must be a JSON object")
    cases = profile["cases"]
    if not isinstance(cases, list) or not cases:
        fail("schema", f"{name}.cases must be nonempty")
    observed = {}
    for case in cases:
        features = _case(case, profile, manifest_path, deferred)
        if case["id"] in observed:
            fail("profile", f"{name} has duplicate case {case['id']}")
        observed[case["id"]] = features
    required_cases = set()
    for capability, declaration in capabilities.items():
        for ref in declaration.get("cases", []):
            if ref not in observed:
                fail("profile", f"{name}.{capability} references nonexistent case {ref}")
            if capability in observed[ref] and not observed[ref][capability]:
                fail("profile", f"{name}.{capability} references case {ref} without that operation")
            if declaration["required"]:
                required_cases.add(ref)
    if required_cases != observed.keys():
        fail("profile", f"{name} must cover every case with a required capability")


def validate_data(data: dict, manifest_path: Path) -> None:
    """Validate manifest data and referenced fixtures; perform no network I/O."""
    object_fields(data, ("schema_version", "decision", "owner", "proof_production", "fixture_root",
                         "negative_fixtures", "profiles"), "manifest")
    if type(data["schema_version"]) is not int or data["schema_version"] != 1:
        fail("schema", "schema_version must be integer 1")
    for field in ("decision", "owner", "proof_production"):
        text(data[field], field)
    if data["owner"] != "Riley":
        fail("profile", "owner must identify accountable distribution owner Riley")
    if data["fixture_root"] != FIXTURE_ROOT:
        fail("fixture", f"fixture_root must be {FIXTURE_ROOT}")
    negative = fixture_path(manifest_path, data["negative_fixtures"])
    if negative.suffix != ".json":
        fail("fixture", "negative_fixtures must be JSON")
    negatives = load_json(negative)
    if not isinstance(negatives, list) or not negatives:
        fail("fixture", "negative_fixtures must contain a nonempty JSON list")
    profiles = data["profiles"]
    if not isinstance(profiles, dict) or not profiles:
        fail("schema", "profiles must be a nonempty map")
    for name, profile in profiles.items():
        _profile(name, profile, manifest_path)


def validate_manifest(path: Path) -> dict:
    """Load strict JSON, validate pinned identities/fixtures, and return data."""
    path = Path(path)
    data = load_json(path)
    validate_data(data, path)
    return data


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path, help="manifest JSON under docs/finite-fields")
    args = parser.parse_args(argv)
    try:
        data = validate_manifest(args.manifest)
    except ManifestError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    print(f"Manifest valid: {len(data['profiles'])} profile(s); local identities and fixtures only (no solver execution).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
