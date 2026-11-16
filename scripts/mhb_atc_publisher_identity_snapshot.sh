#!/usr/bin/env bash
# Read public GitHub bot metadata; pin the private App slug+ID in reviewed source.
# A private 'only this account' GitHub App may deny GET /apps/{slug} with
# HTTP 403 even without authentication. NEVER broaden the worker/controller
# permissions or request the publisher private key just to read App metadata.
set -euo pipefail

: "${PUBLISHER_APP_SLUG:?Publisher App slug not configured}"
: "${PUBLISHER_APP_ID:?Publisher App ID not configured}"
[[ "$PUBLISHER_APP_SLUG" =~ ^[a-zA-Z0-9][a-zA-Z0-9-]*$ ]] || {
  echo "Invalid MHB_ATC_PUBLISHER_APP_SLUG" >&2; exit 1;
}
[[ "$PUBLISHER_APP_ID" =~ ^[0-9]+$ ]] || {
  echo "Invalid MHB_ATC_PUBLISHER_APP_ID" >&2; exit 1;
}

# GET /users/{username} supports unauthenticated public user metadata;
# the bot's numeric ID and type must match the GitHub-authored PR identity.
encoded_bot="$(BOT="${PUBLISHER_APP_SLUG}[bot]" python3 -c 'import os, urllib.parse; print(urllib.parse.quote(os.environ["BOT"], safe=""))')"
curl --fail --silent --show-error --max-time 20 --proto '=https' \
  -H 'Accept: application/vnd.github+json' \
  -H 'X-GitHub-Api-Version: 2022-11-28' \
  "https://api.github.com/users/$encoded_bot" \
  > /tmp/atc-publisher-bot.json

# No untrusted App metadata substitutes for the protected ruleset's App ID.
# The authentic App token's app-slug output is checked during publication.
python3 scripts/mhb_atc_immutable.py publisher \
  --bot-json /tmp/atc-publisher-bot.json \
  --app-slug "$PUBLISHER_APP_SLUG" --app-id "$PUBLISHER_APP_ID" \
  > /tmp/atc-publisher-identity.json
