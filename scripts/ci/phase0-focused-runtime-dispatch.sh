#!/usr/bin/env bash
set -euo pipefail

PROFILE="${1:?usage: phase0-focused-runtime-dispatch.sh <profile>}"

case "$PROFILE" in
  storage|accepted-response|rejected-response|exact-send)
    exec bash scripts/ci/phase0-focused-runtime.sh "$PROFILE"
    ;;
  hello-policy-validation|begin-policy-choice|version-session-choice|payload-cancel-choice)
    exec bash scripts/ci/phase0-control-runtime.sh "$PROFILE"
    ;;
  client-control-send|server-framed-ingress|final-response-receive|storage-failure-detail)
    exec bash scripts/ci/phase0-protocol-runtime.sh "$PROFILE"
    ;;
  *)
    echo "unknown consolidated Phase 0 runtime profile: ${PROFILE}" >&2
    exit 2
    ;;
esac
