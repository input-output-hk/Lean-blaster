#!/usr/bin/env bash
# Validate every workflow with a checksum-verified actionlint release.
set -euo pipefail
: "${RUNNER_TEMP:?Runs on the GitHub Ubuntu runner}"
archive="$RUNNER_TEMP/actionlint-1.7.12.tar.gz"
curl --fail --silent --show-error --location \
  https://github.com/rhysd/actionlint/releases/download/v1.7.12/actionlint_1.7.12_linux_amd64.tar.gz \
  -o "$archive"
printf '%s  %s\n' \
  8aca8db96f1b94770f1b0d72b6dddcb1ebb8123cb3712530b08cc387b349a3d8 \
  "$archive" | sha256sum --check
mkdir -p "$RUNNER_TEMP/actionlint"
tar -xzf "$archive" -C "$RUNNER_TEMP/actionlint" actionlint
# Shell scripts have their own regression checks. Existing workflows contain
# legacy shellcheck style warnings, so this job checks the workflow schema.
# v1.7.12 predates these two GitHub features emitted by gh-aw v0.89.21.
# Keep the exceptions exact; other unknown fields/permissions must still fail.
"$RUNNER_TEMP/actionlint/actionlint" -shellcheck='' \
  -ignore 'unexpected key "queue" for "concurrency"' \
  -ignore 'unknown permission scope "copilot-requests"'
