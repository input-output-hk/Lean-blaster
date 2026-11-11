#!/usr/bin/env python3
"""Verify the selected external Z3 version before restoring benchmark results."""

import argparse
import re
import subprocess


def solver_id(expected: str) -> str:
    # Built-in tactics and aesop do not depend on an external SMT binary.
    if expected == "none":
        return "none"
    if not re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", expected):
        raise ValueError(f"Invalid expected Z3 version: {expected!r}")
    result = subprocess.run(["z3", "--version"], check=True, capture_output=True,
                            text=True, timeout=15)
    match = re.fullmatch(r"Z3 version ([0-9]+\.[0-9]+\.[0-9]+)(?: - [^\r\n]+)?",
                         result.stdout.strip())
    if not match:
        raise ValueError(f"Unrecognized Z3 version output: {result.stdout.strip()!r}")
    actual = match.group(1)
    if actual != expected:
        raise ValueError(f"Expected Z3 {expected}, found {actual}")
    return f"z3-{actual}"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("expected", help="Exact Z3 release version, or 'none'")
    args = parser.parse_args()
    try:
        identity = solver_id(args.expected)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        parser.exit(1, f"Solver preflight failed: {error}\n")
    # Safe to append directly to GITHUB_OUTPUT; identity is strictly validated.
    print(f"solver_id={identity}")


if __name__ == "__main__":
    main()
