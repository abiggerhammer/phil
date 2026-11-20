# MHB-ATC owner-local read-only authority audit

Parents: [W2-CI #1935](https://github.com/abiggerhammer/phil/issues/1935),
[worker confinement #1863](https://github.com/abiggerhammer/phil/issues/1863),
[commissioning #1839](https://github.com/abiggerhammer/phil/issues/1839).

This audit NEVER runs in GitHub Actions, never changes repository settings or
refs, never reads secret values, and never mints a token. It collects current
owner-authorized GitHub REST settings using the existing maintainer CLI login.

## Prior credential evidence

[W1 run #44594506800](https://github.com/abiggerhammer/phil/actions/runs/44594506800)
completed successfully and logged "Token revoked". It established the
authenticated worker App slug, positive installation ID, and a minted token
whose repository audience was exactly Phil. It did not authenticate the
underlying numeric App ID, complete installed permissions, or GitHub
environment configuration.

## Why use Jarvis?

The connected GitHub integration can read source, commits, issues, Actions
runs and the existing admitted-ref ruleset, but rejects settings endpoints
such as GET /actions/permissions/workflow and environment settings. Do not
grant an administration-privileged token to an Actions job merely to inspect
those endpoints.

On a maintainer workstation with an authenticated owner GitHub CLI session,
check out reviewed main first. Then, only AFTER this source-only validator
has been independently reviewed and merged, run:

    cd /workspace/phil           # Or the actual checkout location
    git switch main
    git pull --ff-only
    gh auth status
    python3 scripts/mhb_atc_live_authority.py | tee /tmp/mhb-atc-live-settings-report.json

The collector uses only gh api --method GET. It refuses execution inside
GitHub Actions, requires the maintainer's exact GitHub login and numeric ID,
checks that local and remote main agree before and after collection, and
prints only sanitized pass/block statuses with the main SHA and timestamp.
It never prints raw JSON, JWTs, bearer tokens, secret values, or client IDs.

## Checked boundaries

The checker requires the repository default GITHUB_TOKEN to be read-only,
with PR approval disabled. All four ATC activation variables must remain
OFF. Configured worker App ID and slug must equal the reviewed policy.

The environments macos-release, atc-worker-broker and atc-publisher must
have selected branch policies that name ONLY main. macos-release must also
have a nonempty required-reviewer gate. Secret NAME metadata must place
the Apple credentials only in the macOS environment, the worker App key
only in the worker broker environment, and the publisher key only in
the publisher environment. No such credential may be repository-wide.

If GitHub exposes public metadata for the worker App, the script checks
numeric ID, slug, owner and the intended Contents-write/Metadata-read-only
grants. If a private App cannot be inspected at that endpoint, the check
remains BLOCKED, never silently accepted. Missing API data, unexpected
types, duplicate JSON keys, incomplete pagination or unknown branch
policy patterns also block.

The record checks repository-wide secrets but cannot rule out organization
or enterprise-level secret inheritance. Secret VALUES are never inspected.

## Separate W1-ID and W3 obligations

This is a bounded, non-atomic metadata snapshot, not a proof that settings
will remain unchanged. Even when all source settings pass, the public
GET /apps/{slug} response does not authenticate the actual protected App
private key used for the W1 token. W1-ID needs a separately reviewed,
manual main-only App-JWT GET /app and GET /app/installations check, without
JWTs or keys appearing in logs, and without repository writes.

W3 negative protected-ref and direct-PR checks are separately bounded,
credential-bearing experiments that must use disposable resources and
stop on any unexpected success. A publisher trial must never merge a
candidate. Neither W1-ID nor W3 is authorized by this settings snapshot.

The offline tests under MHB ATC Radar Replay use synthetic data without
any GitHub connection or credentials. A green CI test establishes only
validator behavior, NOT compliance of the current live settings.
