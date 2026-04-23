#!/usr/bin/env bash
# blast-check.sh — convenience wrapper for projects that use Blaster as a dependency.
#
# Usage: ./blast-check.sh <ModuleName>
# Example: ./blast-check.sh MyProject.Theorems
#
# On first run (or after `lake update`), builds the blast_check binary from the
# Blaster dependency. Subsequent runs skip the build step if the binary exists.

set -euo pipefail

BINARY=".lake/packages/Blaster/build/bin/blast_check"

if [ ! -f "$BINARY" ]; then
  echo "Building blast-check binary..."
  lake build +Blaster:blast_check
fi

exec "$BINARY" "$@"
