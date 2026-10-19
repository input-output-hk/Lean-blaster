#!/usr/bin/env bash
# Build the solver revision used by the compiled-assurance conformance suite.
set -euo pipefail
prefix="${1:?Usage: build-assurance-z3.sh ABSOLUTE_INSTALL_DIRECTORY}"
case "$prefix" in /*) ;; *) echo 'Install directory must be absolute' >&2; exit 2;; esac
revision=ca39e58c525c5b03c2484f118ade2b92fae31215
source_dir="$prefix-source"
mkdir -p "$source_dir"
if [ ! -d "$source_dir/.git" ]; then
  git -C "$source_dir" init
fi
git -C "$source_dir" fetch --depth 1 https://github.com/RSoulatIOHK/z3.git "$revision"
git -C "$source_dir" checkout --detach "$revision"
cmake -S "$source_dir" -B "$source_dir/build" \
  -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$prefix" \
  -DZ3_BUILD_LIBZ3_SHARED=OFF -DZ3_BUILD_PYTHON_BINDINGS=OFF \
  -DZ3_BUILD_TEST_EXECUTABLES=OFF
cmake --build "$source_dir/build" --parallel "${ASSURANCE_BUILD_JOBS:-2}"
cmake --install "$source_dir/build"
result=$(printf '(set-simplifier recfun-finder)\n(check-sat)\n' | "$prefix/bin/z3" -in)
[ "$result" = sat ] || { echo "Solver capability probe failed: $result" >&2; exit 1; }
"$prefix/bin/z3" --version
