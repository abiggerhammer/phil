#!/usr/bin/env bash
set -euo pipefail

command_name="${1:-}"
archive="${2:-}"
state_dir="${3:-}"

if [[ -z "$command_name" || -z "$archive" || -z "$state_dir" ]]; then
  echo "usage: $0 submit|poll ARCHIVE STATE_DIR" >&2
  exit 2
fi

: "${APPLE_NOTARY_KEY_PATH:?set APPLE_NOTARY_KEY_PATH to the App Store Connect API .p8 file}"
: "${APPLE_NOTARY_KEY_ID:?set APPLE_NOTARY_KEY_ID}"
: "${APPLE_NOTARY_ISSUER_ID:?set APPLE_NOTARY_ISSUER_ID}"

command -v xcrun >/dev/null 2>&1 || { echo 'xcrun is required' >&2; exit 1; }
command -v python3 >/dev/null 2>&1 || { echo 'python3 is required' >&2; exit 1; }
test -s "$archive"
mkdir -p "$state_dir"
state_dir="$(cd "$state_dir" && pwd)"
archive="$(cd "$(dirname "$archive")" && pwd)/$(basename "$archive")"
base="$(basename "$archive")"

notary_args=(
  --key "$APPLE_NOTARY_KEY_PATH"
  --key-id "$APPLE_NOTARY_KEY_ID"
  --issuer "$APPLE_NOTARY_ISSUER_ID"
)

json_field() {
  local file="$1" field="$2"
  python3 - "$file" "$field" <<'PY'
import json
import sys
with open(sys.argv[1], encoding='utf-8') as source:
    value = json.load(source).get(sys.argv[2])
if value is None:
    raise SystemExit(1)
print(value)
PY
}

case "$command_name" in
  submit)
    submit_json="$state_dir/$base.notary-submit.json"
    id_file="$state_dir/$base.notary-id"
    printf 'notarization_stage=submit\n'
    # Do not use --wait here. We need the submission ID immediately so a slow
    # Apple queue is observable and cannot pin a runner without a bound.
    xcrun notarytool submit "$archive" \
      "${notary_args[@]}" \
      --output-format json \
      | tee "$submit_json"
    submission_id="$(json_field "$submit_json" id)"
    test -n "$submission_id"
    printf '%s\n' "$submission_id" > "$id_file"
    printf 'notarization_id=%s\n' "$submission_id"
    ;;

  poll)
    id_file="$state_dir/$base.notary-id"
    test -s "$id_file"
    submission_id="$(cat "$id_file")"
    info_json="$state_dir/$base.notary-info.json"
    log_json="$state_dir/$base.notary-log.json"
    timeout_seconds="${PHIL_NOTARY_TIMEOUT_SECONDS:-1200}"
    interval_seconds="${PHIL_NOTARY_POLL_SECONDS:-30}"
    start="$(date +%s)"

    printf 'notarization_stage=poll\n'
    printf 'notarization_id=%s\n' "$submission_id"
    printf 'notarization_timeout_seconds=%s\n' "$timeout_seconds"

    while :; do
      tmp="$info_json.tmp"
      xcrun notarytool info "$submission_id" \
        "${notary_args[@]}" \
        --output-format json \
        > "$tmp"
      mv "$tmp" "$info_json"
      status="$(json_field "$info_json" status)"
      now="$(date +%s)"
      elapsed=$((now - start))
      printf 'notarization_status=%s elapsed_seconds=%s\n' "$status" "$elapsed"

      case "$status" in
        Accepted)
          printf 'notarization=Accepted\n'
          exit 0
          ;;
        Invalid|Rejected)
          xcrun notarytool log "$submission_id" \
            "${notary_args[@]}" \
            --output-format json \
            > "$log_json" || true
          echo "notarization failed with status $status" >&2
          exit 1
          ;;
      esac

      if (( elapsed >= timeout_seconds )); then
        echo "notarization still $status after ${elapsed}s; submission $submission_id remains inspectable" >&2
        exit 124
      fi
      sleep "$interval_seconds"
    done
    ;;

  *)
    echo "usage: $0 submit|poll ARCHIVE STATE_DIR" >&2
    exit 2
    ;;
esac
