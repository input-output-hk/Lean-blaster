#!/usr/bin/env bash
# Build the library and every source module, including modules not imported by its root.
set -euo pipefail

if [[ $# -ne 1 || ! -d "$1" ]]; then
  echo "usage: check_lean_project_compilation.sh <PROJECT NAME>" >&2
  exit 2
fi
project=$1
sources=()
while IFS= read -r -d '' source; do
  sources+=("$source")
done < <(find "$project" -type f -name '*.lean' -print0)
if (( ${#sources[@]} == 0 )); then
  echo "No Lean sources found in $project" >&2
  exit 1
fi

echo "Building Lean project $project (${#sources[@]} source modules) ..."
# Explicit source targets validate cached builds too; build messages alone
# omit up-to-date modules that have no diagnostics. pipefail preserves failures.
if ! lake build "$project" "${sources[@]}" 2>&1 | tee build.log; then
  exit 1
fi
rm -f build.log
