#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check committed corpus pins, then execute each distinct declared invocation once.

This is correctness validation, not a timing harness or a proof-rule probe.
Run from the repository root after the PROJECT checks build Lean dependencies.
"""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[3]
MANIFEST = ROOT / "docs/finite-fields/benchmark-corpus.json"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads(MANIFEST.read_text())
    for path, expected in manifest["input_pins"].items():
        if digest(ROOT / path) != expected:
            raise ValueError(f"Input hash mismatch: {path}")
    solver = shutil.which("cvc5")
    if solver is None or digest(Path(solver)) != manifest["solver"]["executable_sha256"]:
        raise ValueError("cvc5 must resolve to the manifest-pinned solving executable")
    print(f"Verified {len(manifest['input_pins'])} input hashes and cvc5 hash", flush=True)
    seen = {}
    catalogue_count = 0
    for entry in manifest["entries"]:
        if entry["status"] == "catalogue-only":
            if entry["invocation"] is not None or not entry["missing_reason"]:
                raise ValueError(f"Invalid catalogue-only entry: {entry['id']}")
            catalogue_count += 1
            continue
        if entry["status"] != "runnable":
            raise ValueError(f"Unknown status: {entry['status']}")
        for path in entry["input_files"]:
            if path not in manifest["input_pins"]:
                raise ValueError(f"Unpinned input: {path}")
        invocation = entry["invocation"]
        key = (invocation["cwd"], tuple(invocation["argv"]))
        if key not in seen:
            result = subprocess.run(
                invocation["argv"], cwd=ROOT / invocation["cwd"],
                text=True, capture_output=True, timeout=invocation["timeout_seconds"],
            )
            seen[key] = result
            print(json.dumps({"argv": invocation["argv"], "exit_code": result.returncode,
                              "stdout": result.stdout, "stderr": result.stderr}), flush=True)
        result = seen[key]
        expected = entry["expected"]
        for field, actual in (("exit_code", result.returncode),
                              ("stdout", result.stdout), ("stderr", result.stderr)):
            if field in expected and actual != expected[field]:
                raise ValueError(f"{entry['id']}: unexpected {field}: {actual!r}")
        print(f"PASS {entry['id']}", flush=True)
    print(f"PASS: {len(seen)} distinct invocations; {catalogue_count} non-runnable catalogue entries")


if __name__ == "__main__":
    main()
