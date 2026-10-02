#!/usr/bin/env bash
# Resolve the current master once. A supplied commit is for exact replay/matrices.
set -euo pipefail
revision=${Z3_COMMIT:-}
if [[ -z "$revision" ]]; then
  revision=$(git ls-remote https://github.com/Z3Prover/z3.git refs/heads/master | awk '$2 == "refs/heads/master" {print $1}')
fi
if [[ ! "$revision" =~ ^[0-9a-fA-F]{40}$ ]]; then
  echo "Could not resolve a full Z3 master commit" >&2
  exit 2
fi
printf '%s\n' "$revision" | tr 'A-F' 'a-f'
