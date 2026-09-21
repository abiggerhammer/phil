#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

if [[ "$(uname -s)" != "Linux" ]]; then
  echo "SKIP: PHIL-AUD-STEVE-REPLACE-001 helper failure injection requires Linux RLIMIT_FSIZE"
  exit 0
fi

work="$(mktemp -d "${TMPDIR:-/tmp}/phil-steve-replace-audit.XXXXXX")"
trap 'rm -rf "$work"' EXIT

worker="$work/replace-worker"
cabal exec -- ghc -iruntime/phase1 -Wall -Werror \
  test/Phase1AuditSteveReplaceWorker.hs \
  -o "$worker"

mkdir -p "$work/files"
printf 'replacement payload\n' > "$work/payload-small"
dd if=/dev/zero of="$work/payload-large" bs=1024 count=256 status=none
: > "$work/payload-empty"

run_limited() {
  local blocks="$1"
  local destination="$2"
  local payload="$3"
  (
    ulimit -f "$blocks"
    trap '' XFSZ
    exec "$worker" "$destination" "$payload"
  )
}

# Positive control: ordinary replacement publishes exact bytes.
printf 'old sentinel\n' > "$work/files/ordinary"
chmod 0640 "$work/files/ordinary"
test "$("$worker" "$work/files/ordinary" "$work/payload-small")" = "published"
cmp "$work/payload-small" "$work/files/ordinary"
test "$(stat -c '%a' "$work/files/ordinary")" = "640"

# Positive control: an empty replacement is valid even with a zero file-size limit.
printf 'old sentinel\n' > "$work/files/empty"
test "$(run_limited 0 "$work/files/empty" "$work/payload-empty")" = "published"
test ! -s "$work/files/empty"

# R01: a zero-capacity write failure preserves an existing destination exactly.
printf 'r01 sentinel bytes\n' > "$work/files/r01"
cp "$work/files/r01" "$work/r01.expected"
test "$(run_limited 0 "$work/files/r01" "$work/payload-large")" = "preserved"
cmp "$work/r01.expected" "$work/files/r01"

# R02: a partial staged write failure also preserves the existing destination.
printf 'r02 sentinel bytes\n' > "$work/files/r02"
cp "$work/files/r02" "$work/r02.expected"
test "$(run_limited 8 "$work/files/r02" "$work/payload-large")" = "preserved"
cmp "$work/r02.expected" "$work/files/r02"

# R03: failure before publication preserves prior absence.
rm -f "$work/files/r03"
test "$(run_limited 0 "$work/files/r03" "$work/payload-large")" = "preserved"
test ! -e "$work/files/r03"

# Unrelated state and staged temporary names must not leak across failures.
printf 'unrelated sentinel\n' > "$work/files/unrelated"
printf 'r04 sentinel bytes\n' > "$work/files/r04"
test "$(run_limited 0 "$work/files/r04" "$work/payload-large")" = "preserved"
grep -qx 'unrelated sentinel' "$work/files/unrelated"
if find "$work/files" -maxdepth 1 -name '.*.steve-replace.*' -print -quit | grep -q .; then
  echo 'temporary replacement file survived failed publication' >&2
  exit 1
fi

echo 'PASS: PHIL-AUD-STEVE-REPLACE-001 helper preserves prior state on write failure'
