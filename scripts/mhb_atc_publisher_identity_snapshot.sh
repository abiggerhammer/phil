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

# The public unauthenticated API is rate-limited by GitHub Actions runner
# IP, and the same bot read has returned HTTP 403 on main after green PR CI.
# Use the already-scoped ordinary GitHub Actions GITHUB_TOKEN for this *user*
# metadata read. It is NOT the publisher App key or installation token.
# The response is checked against the owner-reviewed App ID/slug binding.
: "${GH_TOKEN:?Read-only GITHUB_TOKEN required for bot identity lookup}"
encoded_bot="$(BOT="${PUBLISHER_APP_SLUG}[bot]" python3 -c 'import os, urllib.parse; print(urllib.parse.quote(os.environ["BOT"], safe=""))')"
gh api "users/$encoded_bot" > /tmp/atc-publisher-bot.json

# No untrusted App metadata substitutes for the protected ruleset's App ID.
# The authentic App token's app-slug output is checked during publication.
python3 scripts/mhb_atc_immutable.py publisher \
  --bot-json /tmp/atc-publisher-bot.json \
  --app-slug "$PUBLISHER_APP_SLUG" --app-id "$PUBLISHER_APP_ID" \
  > /tmp/atc-publisher-identity.json
