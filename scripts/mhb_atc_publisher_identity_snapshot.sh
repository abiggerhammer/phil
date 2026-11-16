#!/usr/bin/env bash
# Resolve the pinned publisher App and bot using PUBLIC GitHub metadata only.
# No GITHUB_TOKEN and no publisher App private key are sent to these endpoints.
# This helper is sourced by both ATC controller census and the read-only PR CI.
set -euo pipefail

: "${PUBLISHER_APP_SLUG:?Publisher App slug not configured}"
: "${PUBLISHER_APP_ID:?Publisher App ID not configured}"
[[ "$PUBLISHER_APP_SLUG" =~ ^[a-zA-Z0-9][a-zA-Z0-9-]*$ ]] || {
  echo "Invalid MHB_ATC_PUBLISHER_APP_SLUG" >&2; exit 1;
}
[[ "$PUBLISHER_APP_ID" =~ ^[0-9]+$ ]] || {
  echo "Invalid MHB_ATC_PUBLISHER_APP_ID" >&2; exit 1;
}

# This endpoint explicitly supports unauthenticated PUBLIC app metadata.
# Sending the ordinary workflow GITHUB_TOKEN caused GitHub to return 403.
curl --fail --silent --show-error --max-time 20 --proto '=https' \
  -H 'Accept: application/vnd.github+json' \
  -H 'X-GitHub-Api-Version: 2022-11-28' \
  "https://api.github.com/apps/$PUBLISHER_APP_SLUG" \
  > /tmp/atc-publisher-app.json

encoded_bot="$(BOT="${PUBLISHER_APP_SLUG}[bot]" python3 -c 'import os, urllib.parse; print(urllib.parse.quote(os.environ["BOT"], safe=""))')"
curl --fail --silent --show-error --max-time 20 --proto '=https' \
  -H 'Accept: application/vnd.github+json' \
  -H 'X-GitHub-Api-Version: 2022-11-28' \
  "https://api.github.com/users/$encoded_bot" \
  > /tmp/atc-publisher-bot.json

# Validate both GitHub-reported identities against the protected-source
# owner-attested numeric App ID and deterministic bot login.
python3 scripts/mhb_atc_immutable.py publisher \
  --app-json /tmp/atc-publisher-app.json \
  --bot-json /tmp/atc-publisher-bot.json \
  --app-slug "$PUBLISHER_APP_SLUG" --app-id "$PUBLISHER_APP_ID" \
  > /tmp/atc-publisher-identity.json
