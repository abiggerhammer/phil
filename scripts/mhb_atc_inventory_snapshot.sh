#!/usr/bin/env bash
# Complete GitHub REST census of every protected admitted ref and its PR history.
# Source this ONLY from an Actions job which checks out trusted main.
# GH_TOKEN must be the non-publisher scoped token; no ref/PR writes are made.
set -euo pipefail

: "${GH_REPO:?Missing GH_REPO}"
# Authenticate the App/bot using the exact public metadata verifier
# also exercised by PR CI; ordinary GITHUB_TOKEN cannot read /apps/{slug}.
. scripts/mhb_atc_publisher_identity_snapshot.sh
gh api --paginate "repos/$GH_REPO/git/matching-refs/heads/hamster/admitted" \
  | jq -s 'add // []' > /tmp/atc-admitted-refs.json
python3 scripts/mhb_atc_inventory.py --refs /tmp/atc-admitted-refs.json --list \
  > /tmp/atc-protected-lookups.json

: > /tmp/atc-protected-issue-pages.ndjson
: > /tmp/atc-protected-pr-pages.ndjson
while IFS= read -r item; do
  issue="$(jq -r '.issue' <<<"$item")"
  branch="$(jq -r '.branch' <<<"$item")"
  gh api "repos/$GH_REPO/issues/$issue" >> /tmp/atc-protected-issue-pages.ndjson
  owner="${GH_REPO%%/*}"
  encoded="$(FILTER="$owner:$branch" python3 -c 'import os, urllib.parse; print(urllib.parse.quote(os.environ["FILTER"], safe=""))')"
  gh api --paginate "repos/$GH_REPO/pulls?state=all&head=$encoded&per_page=100" \
    | jq -s 'add // []' >> /tmp/atc-protected-pr-pages.ndjson
done < <(jq -c '.[]' /tmp/atc-protected-lookups.json)

jq -s '.' /tmp/atc-protected-issue-pages.ndjson > /tmp/atc-protected-issues.json
jq -s 'add // []' /tmp/atc-protected-pr-pages.ndjson > /tmp/atc-protected-prs.json
python3 scripts/mhb_atc_inventory.py \
  --refs /tmp/atc-admitted-refs.json \
  --issues /tmp/atc-protected-issues.json \
  --prs /tmp/atc-protected-prs.json \
  --publisher-json /tmp/atc-publisher-identity.json \
  --repo "$GH_REPO" > /tmp/atc-inventory.json

# Even one known active ref blocks a *new* admission, irrespective of labels.
cat /tmp/atc-inventory.json
