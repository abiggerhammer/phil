#!/usr/bin/env bash
# Replace haskell-actions/setup's one-shot index refresh with bounded retries.
# Isolate HTTP/1.1 preference to this command (curl error 92 workaround).
set -euo pipefail

max_attempts=4
curl_home="$(mktemp -d)"
trap 'rm -rf "$curl_home"' EXIT
printf '%s\n' '--http1.1' > "$curl_home/.curlrc"

for ((attempt=1; attempt<=max_attempts; attempt++)); do
  printf 'cabal update attempt %d/%d (curl HTTP/1.1)\n' "$attempt" "$max_attempts"
  if CURL_HOME="$curl_home" cabal update; then
    printf 'cabal update succeeded on attempt %d\n' "$attempt"
    exit 0
  fi

  if (( attempt == max_attempts )); then
    printf 'cabal update failed after %d attempts\n' "$max_attempts" >&2
    exit 1
  fi

  delay=$((2 ** (attempt + 1)))
  printf 'cabal update failed; retrying after %ds\n' "$delay" >&2
  sleep "$delay"
done

exit 1
