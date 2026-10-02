#!/usr/bin/env bash
# Build one exact snapshot of Z3 master. No prebuilt release/result cache.
set -euo pipefail
script_dir="$(cd "$(dirname "$0")" && pwd)"
revision=$(bash "$script_dir/resolve-z3.sh")
work_root=${Z3_WORK_DIR:-${RUNNER_TEMP:-/tmp}/blaster-z3}
mkdir -p "$work_root"
work=$(mktemp -d "$work_root/master-XXXXXXXX")
evidence=${Z3_EVIDENCE_DIR:-.ci-results}
mkdir -p "$evidence"
# Record the requested SHA even when fetch/configure/build fails.
printf '{"source_ref":"master","source_commit":"%s","build_type":"Release","library":"static"}\n' \
  "$revision" > "$evidence/z3-source.json"
git init -q "$work/source"
git -C "$work/source" remote add origin https://github.com/Z3Prover/z3.git
git -C "$work/source" fetch --quiet --depth 1 origin "$revision"
git -C "$work/source" checkout --quiet --detach FETCH_HEAD
if [[ "$(git -C "$work/source" rev-parse HEAD)" != "$revision" ]]; then
  echo "Z3 checkout does not match the requested commit" >&2
  exit 1
fi
parallel=${Z3_BUILD_JOBS:-2}
if [[ ! "$parallel" =~ ^[1-9][0-9]*$ ]]; then
  echo "Z3_BUILD_JOBS must be a positive integer" >&2
  exit 2
fi
# Use the default make generator, available on both Ubuntu and macOS.
log="$evidence/z3-build.log"
printf 'Building Z3 master at %s\n' "$revision" | tee "$log"
run_logged() {
  "$@" 2>&1 | tee -a "$log"
}
run_logged cmake -S "$work/source" -B "$work/build" -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_SHARED_LIBS=OFF -DZ3_BUILD_TEST_EXECUTABLES=OFF \
  -DZ3_ENABLE_EXAMPLE_TARGETS=OFF -DCMAKE_INSTALL_PREFIX="$work/install"
run_logged cmake --build "$work/build" --parallel "$parallel"
run_logged cmake --install "$work/build"
run_logged "$work/install/bin/z3" --version
printf '%s\n' "$work/install/bin" > "$evidence/z3-bin-path.txt"
if [[ -n "${GITHUB_PATH:-}" ]]; then
  echo "$work/install/bin" >> "$GITHUB_PATH"
fi
if [[ -n "${GITHUB_ENV:-}" ]]; then
  echo "Z3_COMMIT=$revision" >> "$GITHUB_ENV"
fi
