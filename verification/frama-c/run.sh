#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
if [[ -n "${Z3_INC_PATH:-}" ]]; then
  z3_include="$Z3_INC_PATH"
elif [[ -n "${Z3_ROOT:-}" ]]; then
  z3_include="$Z3_ROOT/include"
else
  z3_include="$(pkg-config --variable=includedir z3)"
fi
cd "$repo_root"
opam exec -- frama-c \
  -cpp-extra-args="-Iverification/frama-c/model -I${z3_include}" \
  "$@"
