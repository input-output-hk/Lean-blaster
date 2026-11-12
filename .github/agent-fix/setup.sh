#!/usr/bin/env bash
# Install the repository's Lean toolchain and the Z3 version used by stable CI.
# Requires a disposable Linux x86_64 runner; does not need sudo or API credentials.
set -euo pipefail

if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo "The CI setup script requires Linux x86_64; use your local Lean/Z3 installation locally." >&2
  exit 1
fi

if [[ ! -x "$HOME/.elan/bin/elan" ]]; then
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
# Read the selected branch's toolchain as data, never execute its setup scripts.
toolchain=$(python3 - "${AGENT_FIX_TARGET_ROOT:-.}/lean-toolchain" <<'PY'
import os
import stat
import sys

try:
    descriptor = os.open(sys.argv[1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as stream:
        if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
            raise ValueError("lean-toolchain must be a regular file")
        data = stream.read(257)
    if len(data) > 256 or b"\0" in data:
        raise ValueError("lean-toolchain must contain at most 256 bytes without NUL characters")
    print(data.decode("ascii"), end="")
except (OSError, UnicodeDecodeError, ValueError) as error:
    sys.exit(f"Cannot read the selected branch's lean-toolchain safely: {error}")
PY
)
if [[ ! "$toolchain" =~ ^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$ ]]; then
  echo "The bot requires an official versioned Lean toolchain; discuss custom/nightly setup first." >&2
  exit 1
fi
elan toolchain install "$toolchain"

solver_dir="${RUNNER_TEMP:-/tmp}/agent-fix-z3"
mkdir -p "$solver_dir"
if [[ ! -x "$solver_dir/z3-4.15.2-x64-glibc-2.39/bin/z3" ]]; then
  curl -fsSL \
    https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-x64-glibc-2.39.zip \
    -o "$solver_dir/z3.zip"
  unzip -qo "$solver_dir/z3.zip" -d "$solver_dir"
fi
export PATH="$solver_dir/z3-4.15.2-x64-glibc-2.39/bin:$PATH"
if [[ -n "${GITHUB_PATH:-}" ]]; then
  echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
  echo "$solver_dir/z3-4.15.2-x64-glibc-2.39/bin" >> "$GITHUB_PATH"
fi
elan run "$toolchain" lean --version
z3 --version
