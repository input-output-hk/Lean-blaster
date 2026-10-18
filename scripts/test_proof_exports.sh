#!/usr/bin/env bash
# Export representative proofs and recheck the generated files with Lean.
set -euo pipefail
ulimit -c 0
cd "$(dirname "${BASH_SOURCE[0]}")/.."
lake build Blaster:shared Tests.Proof.Machine Tests.Proof.Lists
run_dir=$(mktemp -d "$PWD/.lake/proof-exports.XXXXXX")
echo "Proof export logs: $run_dir"
cp .lake/build/lib/libBlaster.so "$run_dir/libBlaster.so"
for name in Machine Lists MachineText; do
  file="Tests/Proof/$name.lean"
  options=()
  if [[ "$name" == MachineText ]]; then
    file=Tests/Proof/Machine.lean
    options=(-Dblaster.induction.exportTextAbove=0)
  fi
  mkdir -p "$run_dir/$name"
  timeout --signal=TERM --kill-after=5s 900s lake env lean \
    --plugin="$run_dir/libBlaster.so" -j2 -s65536 -M5000 \
    "-Dblaster.induction.export=$run_dir/$name" "${options[@]}" "$file" \
    > "$run_dir/$name.log" 2>&1
  if grep -q 'sorryAx' "$run_dir/$name.log"; then
    cat "$run_dir/$name.log"
    exit 1
  fi
done
shopt -s nullglob
exports=("$run_dir"/*/*.lean)
if (( ${#exports[@]} != 6 )); then
  echo "Expected six exported proofs; found ${#exports[@]}" >&2
  exit 1
fi
for file in "${exports[@]}"; do
  # Use Lean's default stack and no explicit plugin, as a downstream consumer.
  timeout --signal=TERM --kill-after=5s 900s lake env lean "$file" > "$file.log" 2>&1
  if grep -q 'sorryAx' "$file.log"; then
    cat "$file.log"
    exit 1
  fi
done
echo "All six exported proofs compile without sorryAx."
