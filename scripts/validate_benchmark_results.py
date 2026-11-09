#!/usr/bin/env python3
"""Reject incomplete benchmark artifacts before updating the published report."""

import argparse
import csv
from pathlib import Path

MANIFEST_FIELDS = ["tool", "toolchain", "branch", "resolved_commit", "tactic", "build_status"]
STATUSES = {"OK", "FAIL", "TIMEOUT", "ENV"}
TOOL_TACTICS = {
    "blaster": {"blaster", "blaster (only-optimize: 1)"},
    "smt": {"smt +model"},
    "hammer": {"hammer"},
    "auto": {"auto"},
    "aesop": {"aesop"},
    "baselines": {"omega", "grind", "simp"},
}


def validate_tool(results: Path, tool: str, manifest: Path, suites: list[str]) -> list[dict]:
    with manifest.open(newline="", encoding="utf-8") as source:
        reader = csv.DictReader(source, delimiter="\t")
        if reader.fieldnames != MANIFEST_FIELDS:
            raise ValueError(f"{tool}: invalid manifest header")
        rows = list(reader)
    if any(None in row or None in row.values() for row in rows):
        raise ValueError(f"{tool}: malformed manifest row")
    if not rows or any(row["tool"] != tool for row in rows):
        raise ValueError(f"{tool}: missing or unexpected manifest rows")
    tactics = [row["tactic"] for row in rows]
    if any(not tactic for tactic in tactics) or len(set(tactics)) != len(tactics):
        raise ValueError(f"{tool}: missing or duplicate tactics")
    if tool not in TOOL_TACTICS or set(tactics) != TOOL_TACTICS[tool]:
        raise ValueError(f"{tool}: incomplete or unexpected tactic comparison")
    for row in rows:
        if row["build_status"] not in {"OK", "CACHED"}:
            raise ValueError(f"{tool}: {row['tactic']} has {row['build_status']}")
        if not row["toolchain"] or not row["resolved_commit"] or row["resolved_commit"] == "?":
            raise ValueError(f"{tool}: unresolved tool version")
    if not suites or len(set(suites)) != len(suites):
        raise ValueError(f"{tool}: missing or duplicate suite definitions")
    for suite in suites:
        path = results / tool / f"{suite}_results.csv"
        with path.open(newline="", encoding="utf-8") as source:
            reader = csv.DictReader(source)
            fields = {"Benchmark", "Theorem", "Statement"}
            for tactic in tactics:
                fields.update({f"{tactic}_time", f"{tactic}_status"})
            if (len(reader.fieldnames or []) != len(set(reader.fieldnames or []))
                    or not fields.issubset(reader.fieldnames or [])):
                raise ValueError(f"{tool}/{suite}: missing CSV columns")
            seen = set()
            for row in reader:
                if None in row or None in row.values():
                    raise ValueError(f"{tool}/{suite}: malformed CSV row")
                theorem = row["Theorem"]
                if not theorem or theorem in seen or row["Benchmark"] != suite:
                    raise ValueError(f"{tool}/{suite}: invalid or duplicate theorem row")
                seen.add(theorem)
                for tactic in tactics:
                    if row[f"{tactic}_status"] not in STATUSES:
                        raise ValueError(f"{tool}/{suite}: invalid result status")
            if not seen:
                raise ValueError(f"{tool}/{suite}: empty result CSV")
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("results", type=Path)
    parser.add_argument("tool")
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--suites", required=True, type=Path)
    args = parser.parse_args()
    try:
        validate_tool(args.results, args.tool, args.manifest,
                      args.suites.read_text(encoding="utf-8").splitlines())
    except (OSError, ValueError, KeyError, csv.Error) as error:
        parser.exit(1, f"Incomplete benchmark: {error}\n")
    print(f"Validated {args.tool} benchmark results")


if __name__ == "__main__":
    main()
