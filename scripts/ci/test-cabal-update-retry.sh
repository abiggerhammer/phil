#!/usr/bin/env bash
# Network-free controls for bounded update and safe failure.
set -euo pipefail

root="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/bin"

cat > "$tmp/bin/cabal" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
test "$1" = update
test -n "$CURL_HOME"
test -f "$CURL_HOME/.curlrc"
grep -Fxq -- '--http1.1' "$CURL_HOME/.curlrc"
printf x >> "$MOCK_COUNTER"
n="$(wc -c < "$MOCK_COUNTER" | tr -d ' ')"
if (( MOCK_SUCCEED_ON > 0 && n >= MOCK_SUCCEED_ON )); then
  exit 0
fi
echo 'mock curl: (92) HTTP/2 PROTOCOL_ERROR' >&2
exit 92
MOCK
cat > "$tmp/bin/sleep" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$1" >> "$MOCK_DELAYS"
MOCK
chmod +x "$tmp/bin/cabal" "$tmp/bin/sleep"
export PATH="$tmp/bin:$PATH"
export MOCK_COUNTER="$tmp/counter" MOCK_DELAYS="$tmp/delays"

: > "$MOCK_COUNTER"
: > "$MOCK_DELAYS"
export MOCK_SUCCEED_ON=3
bash "$root/cabal-update-retry.sh"
test "$(wc -c < "$MOCK_COUNTER" | tr -d ' ')" = 3
test "$(printf '4\n8\n')" = "$(cat "$MOCK_DELAYS")"

: > "$MOCK_COUNTER"
: > "$MOCK_DELAYS"
export MOCK_SUCCEED_ON=0
if bash "$root/cabal-update-retry.sh"; then
  echo 'unexpected success after all retries failed' >&2
  exit 1
fi
test "$(wc -c < "$MOCK_COUNTER" | tr -d ' ')" = 4
test "$(printf '4\n8\n16\n')" = "$(cat "$MOCK_DELAYS")"

: > "$MOCK_COUNTER"
: > "$MOCK_DELAYS"
export MOCK_SUCCEED_ON=1
bash "$root/cabal-update-retry.sh"
test "$(wc -c < "$MOCK_COUNTER" | tr -d ' ')" = 1
test ! -s "$MOCK_DELAYS"

echo "PASS: bounded Cabal update retries, scoped HTTP/1.1, exhaustion"
