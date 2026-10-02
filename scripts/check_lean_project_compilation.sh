#!/usr/bin/env bash
# Build every selected source module, including modules absent from barrel imports.
# Lake handles fresh and cached builds; console progress is not a coverage API.
set -euo pipefail

if [[ $# -lt 1 || $# -gt 3 ]]; then
  echo "usage: $0 <Lake target> [source directory] [excluded subtree]" >&2
  exit 2
fi
script_dir="$(cd "$(dirname "$0")" && pwd)"
target=$1
source_dir=${2:-${target//./\/}}
exclude=${3:-}
source_dir=${source_dir#./}
source_dir=${source_dir%/}
exclude=${exclude#./}
exclude=${exclude%/}
if [[ ! -d "$source_dir" ]]; then
  echo "Source directory does not exist: $source_dir" >&2
  exit 2
fi

log_dir=${BUILD_LOG_DIR:-.ci-results/build}
mkdir -p "$log_dir"
log="$log_dir/${target//./_}.log"
file_list=$(mktemp)
trap 'rm -f "$file_list"' EXIT
# Materialize this before the loop so a failed find/sort cannot become success.
find "$source_dir" -type f -name '*.lean' -print | LC_ALL=C sort > "$file_list"
# Include the selected subtree's barrel when it exists.
if [[ -f "$source_dir.lean" ]]; then
  printf '%s\n' "$source_dir.lean" >> "$file_list"
fi
modules=()
while IFS= read -r path; do
  if [[ -n "$exclude" && ( "$path" == "$exclude"/* || "$path" == "$exclude.lean" ) ]]; then
    continue
  fi
  module=${path%.lean}
  modules+=("+${module//\//.}")
done < "$file_list"
if [[ ${#modules[@]} -eq 0 ]]; then
  echo "No Lean sources selected under $source_dir" >&2
  exit 2
fi
# Keep build.log for the existing manual conformance workflow; keep per-target
# logs as well so a later build cannot overwrite earlier evidence.
{
  printf 'Building %s and %s selected modules\n' "$target" "${#modules[@]}"
  python3 "$script_dir/ci/run_bounded.py" \
    --timeout "${BUILD_TIMEOUT_SECONDS:-1800}" \
    --report "$log_dir/${target//./_}.json" -- lake build "$target" "${modules[@]}"
} 2>&1 | tee "$log" build.log
