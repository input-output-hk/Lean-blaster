#!/usr/bin/env python3
"""Discover, register-check, and freshly build solver-independent FF regressions.

Only this script's repository is used, irrespective of the working directory.
The runner launches Lake, never a solver; solver independence of the Lean
assertions is additionally exercised by running this gate without solver binaries.
Module paths use unquoted ASCII Lean identifier components. Cleanup is confined
to each discovered module's files in Lake's lib/lean and ir output directories.
"""

import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
MODULE_COMPONENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")
MODULE_PREFIX = "Tests.FiniteField."
SOLVER_OVERRIDES = (
    "BLASTER_SOLVER", "BLASTER_TIMEOUT", "BLASTER_STRICT_CVC5_RESULTS",
)
ANSI_ESCAPE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
BUILT_LINE = re.compile(
    r"^(?:[✔⚠ℹ]\ufe0f?\s+)?(?:\[\d+/\d+\]\s+)?"
    r"Built (?P<module>\S+) \([^()\r\n]+\)\s*$"
)


class PureTestError(ValueError):
    """A discovery, registration, cleanup, or fresh-coverage failure."""


def reject_symlink_components(root: Path, path: Path) -> None:
    """Do not follow source/output aliases outside the owned repository paths."""
    current = root
    for component in path.relative_to(root).parts:
        current = current / component
        if current.is_symlink():
            raise PureTestError(f"symlink is not an isolated module path: {current}")


def discover_modules(root: Path) -> list[str]:
    """Return sorted recursive modules, failing rather than hiding walk errors."""
    tree = root / "Tests" / "FiniteField"
    reject_symlink_components(root, tree)
    if not tree.is_dir():
        raise PureTestError(f"missing finite-field source directory: {tree}")

    def walk_error(error: OSError) -> None:
        raise error

    modules = set()
    sources = {}
    for directory, dirs, files in os.walk(tree, onerror=walk_error, followlinks=False):
        dirs.sort()
        parent = Path(directory)
        for name in dirs:
            reject_symlink_components(root, parent / name)
        for name in sorted(files):
            if not name.endswith(".lean"):
                continue
            source = parent / name
            reject_symlink_components(root, source)
            if not source.is_file():
                raise PureTestError(f"not a regular Lean source: {source}")
            parts = source.relative_to(root).with_suffix("").parts
            if any(not MODULE_COMPONENT.fullmatch(part) for part in parts):
                raise PureTestError(f"invalid unquoted module path: {source}")
            module = ".".join(parts)
            identity = source.stat()
            key = (identity.st_dev, identity.st_ino)
            if module in modules or key in sources:
                raise PureTestError(f"duplicate module/source mapping: {module} ({source})")
            modules.add(module)
            sources[key] = source
    if not modules:
        raise PureTestError(f"no .lean modules discovered under {tree}")
    return sorted(modules)


def without_comments(text: str) -> str:
    """Blank Lean line/nested-block comments, preserving line boundaries."""
    result = []
    depth = 0
    index = 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == "/-":
            depth += 1
            result.append("  ")
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            result.append("  ")
            index += 2
        elif not depth and pair == "--":
            end = text.find("\n", index)
            if end == -1:
                end = len(text)
            result.append(" " * (end - index))
            index = end
        else:
            char = text[index]
            result.append(char if not depth or char == "\n" else " ")
            index += 1
    if depth:
        raise PureTestError("unterminated block comment in Tests/FixedIssues.lean")
    return "".join(result)


def check_registrations(root: Path, modules: list[str]) -> None:
    """Require exactly one individual import per discovered module, no stale ones."""
    registration = root / "Tests" / "FixedIssues.lean"
    counts = Counter()
    for number, line in enumerate(without_comments(registration.read_text(encoding="utf-8")).splitlines(), 1):
        words = line.split()
        relevant = [word for word in words
                    if word == "Tests.FiniteField" or word.startswith(MODULE_PREFIX)]
        if not relevant:
            continue
        if len(words) != 2 or words[0] != "import" or not words[1].startswith(MODULE_PREFIX):
            raise PureTestError(f"{registration}:{number}: expected one direct finite-field import")
        module = words[1]
        if any(not MODULE_COMPONENT.fullmatch(part) for part in module.split(".")):
            raise PureTestError(f"{registration}:{number}: invalid module import {module!r}")
        counts[module] += 1
    expected = set(modules)
    missing = sorted(expected - counts.keys())
    duplicate = sorted(module for module, count in counts.items() if count != 1)
    stale = sorted(counts.keys() - expected)
    if missing or duplicate or stale:
        raise PureTestError(
            f"finite-field import registration mismatch: missing={missing}, "
            f"duplicate={duplicate}, stale={stale}"
        )


def clean_module_outputs(root: Path, modules: list[str]) -> int:
    """Remove only discovered modules' own outputs, never source-tree directories.

    Lake 4.24 stores Foo.olean/ilean/ir/trace (and hash/private/server
    sidecars) in lib/lean, and Foo.c/bc/setup.json/object sidecars in ir.
    A dot-free source basename gives these artifacts an unambiguous prefix;
    a nested module's directory and siblings' artifacts are left untouched.
    """
    removed = 0
    for output_tree in (root / ".lake/build/lib/lean", root / ".lake/build/ir"):
        for module in modules:
            parts = module.split(".")
            parent = output_tree.joinpath(*parts[:-1])
            reject_symlink_components(root, parent)
            if not parent.exists():
                continue
            prefix = parts[-1] + "."
            for artifact in sorted(parent.iterdir()):
                if not artifact.name.startswith(prefix):
                    continue
                if artifact.is_symlink() or artifact.is_file():
                    artifact.unlink()
                    removed += 1
    return removed


def build_environment(environ: dict[str, str]) -> dict[str, str]:
    """Use the existing pure lane's solver-free environment convention."""
    environment = environ.copy()
    for variable in SOLVER_OVERRIDES:
        environment.pop(variable, None)
    environment["LEAN_NUM_THREADS"] = "5"
    # Restoring artifacts would not execute the assertions in this invocation.
    environment["LAKE_ARTIFACT_CACHE"] = "false"
    return environment


def built_module(line: str) -> str | None:
    """Recognize fresh module jobs, not Replayed jobs, facets, or diagnostic text."""
    match = BUILT_LINE.fullmatch(ANSI_ESCAPE.sub("", line).strip())
    return match["module"] if match else None


def require_coverage(modules: list[str], built: set[str]) -> None:
    if not modules:
        raise PureTestError("cannot report coverage for an empty module set")
    missing = sorted(set(modules) - built)
    if missing:
        raise PureTestError("missing fresh Built <module> (...) evidence: " + ", ".join(missing))


def run_build(root: Path, modules: list[str]) -> int:
    """Stream a single clean explicit-target build and require complete evidence."""
    if not modules:
        raise PureTestError("refusing to invoke Lake with no finite-field targets")
    built = set()
    print(f"Building {len(modules)} solver-independent finite-field modules ...", flush=True)
    with subprocess.Popen(
        ["lake", "--no-cache", "build", *modules],
        cwd=root,
        env=build_environment(os.environ),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        errors="replace",
        bufsize=1,
    ) as process:
        assert process.stdout is not None
        for line in process.stdout:
            print(line, end="", flush=True)
            module = built_module(line)
            if module is not None:
                built.add(module)
        status = process.wait()
    if status:
        print(f"Finite-field pure compilation failed (Lake exit {status}).", file=sys.stderr)
        return status if status > 0 else 128 - status
    require_coverage(modules, built)
    for module in modules:
        print(f"  compiled: {module}")
    print(f"Finite-field pure coverage: {len(modules)}/{len(modules)} modules freshly compiled.")
    return 0


def main() -> int:
    try:
        modules = discover_modules(REPO_ROOT)
        check_registrations(REPO_ROOT, modules)
        removed = clean_module_outputs(REPO_ROOT, modules)
        print(f"Removed {removed} generated files for {len(modules)} discovered modules.", flush=True)
        return run_build(REPO_ROOT, modules)
    except (PureTestError, OSError, UnicodeError) as error:
        print(f"Finite-field pure runner: {error}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("Finite-field pure runner: interrupted", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
