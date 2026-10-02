#!/usr/bin/env bash
# Run on GitHub's ubuntu-24.04 runner. The repository owns the Lean version.
set -euo pipefail
: "${GITHUB_PATH:?This setup script runs inside GitHub Actions}"
: "${RUNNER_TEMP:?Missing runner temporary directory}"
toolchain=${LEAN_TOOLCHAIN:-$(tr -d '[:space:]' < lean-toolchain)}
if [[ ! "$toolchain" =~ ^[A-Za-z0-9:/._-]+$ ]]; then
  echo "Invalid Lean toolchain" >&2
  exit 2
fi
# Pin the installer source rather than following elan/master.
curl --fail --silent --show-error --location \
  https://raw.githubusercontent.com/leanprover/elan/0e36a07b9bbcc5381fa6250df109f9a4f94d7bac/elan-init.sh \
  -o "$RUNNER_TEMP/elan-init.sh"
sh "$RUNNER_TEMP/elan-init.sh" -y --default-toolchain "$toolchain"
export PATH="$HOME/.elan/bin:$PATH"
echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
if [[ -n "${LEAN_TOOLCHAIN:-}" ]]; then
  printf '%s\n' "$toolchain" > lean-toolchain
fi
elan toolchain install "$toolchain"

# Resolve and build Z3 master, retaining the source SHA and compiler log.
bash "$(dirname "$0")/build-z3.sh"
z3_bin=$(cat .ci-results/z3-bin-path.txt)
export PATH="$z3_bin:$PATH"
lean --version
lake --version
z3 --version

# Bound individual solver sessions and retain replayable SMT input. This proxy
# preserves ordinary responses and never converts a hard timeout to 'unknown'.
real_z3=$(command -v z3)
proxy="$PWD/.ci-results/solver-bin"
mkdir -p "$proxy"
cp "$(dirname "$0")/bounded_z3.py" "$proxy/z3"
chmod +x "$proxy/z3"
export Z3_REAL_EXECUTABLE="$real_z3"
if [[ -n "${GITHUB_ENV:-}" ]]; then
  echo "Z3_REAL_EXECUTABLE=$real_z3" >> "$GITHUB_ENV"
fi
echo "$proxy" >> "$GITHUB_PATH"
