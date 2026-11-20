# MHB-ATC W3 — bounded live negative commissioning: reviewed plan only

Tracking: [W1–W3 #1863](https://github.com/abiggerhammer/phil/issues/1863), [immutable admitted-ref controller #1839](https://github.com/abiggerhammer/phil/issues/1839), [W2-CI #1935](https://github.com/abiggerhammer/phil/issues/1935). **No worker, broker or controller activation is authorized by this document.**

## Current evidence, not inferred permissions

- [W1-ID manual run #44670951636](https://github.com/abiggerhammer/phil/actions/runs/44670951636) used reviewed trusted-main source, validated JWT-authenticated worker App ID **5836223**, exact App/installation Contents-write and Metadata-read permissions with no other active grants, then a Phil-scoped token with matching installation ID. Cleanup log says **Token revoked**. This run made no repository mutation. **One scoped token's single-repository audience is not the App installation's full selected-repository inventory.**
- Active ruleset [#27365284](https://github.com/abiggerhammer/phil/rules/27365284) matches **`refs/heads/hamster/admitted/*`**, with create/update/delete/non-fast-forward restrictions; sole unredacted bypass Integration App **5782193** (publisher). Worker App **5836223 is not on the bypass list**. GitHub enforces these operations via rulesets, but this read is **not yet a real denied worker-App operation**.
- An initial read-only inventory found **no** `hamster/admitted/*` refs and six existing historical `hamster/staged/*` refs. The staged refs are not disposable test targets. All current broker/worker source flags and the two configured lane records remain disabled.
- G1 staged-push CI isolation was observed with the **maintainer GitHub principal**, not the worker App. G2 source isolation and live owner configuration protect `macos-release` on exactly `main` with a required reviewer. PR tests still trigger other regular unprivileged CI.

## Commissioning phases and required independent approvals

**Phase 0 — source review and owner inventory only.** This PR introduces just a read-only readiness planner and offline hostile mutation tests. Run `scripts/mhb_atc_w3_readiness.py` only from a **clean current main** after source review/merge. It parses a fresh owner-authenticated GitHub ruleset response, two exact-main GETs and a full admitted-ref namespace snapshot. It checks reviewed source policies and fails closed on changed ruleset version, unknown additional bypass, unreviewed rule changes, drifted main or any occupied admitted namespace. A successful output says **`SOURCE_READINESS_CONFIRMED_REVIEW_REQUIRED`** and `execution_authorized:false`. It does *not* enable W3 actions or certify permissions.

**Phase 1 — independently verify installed repository selection.** In the GitHub account's **Installed GitHub Apps → phil-atc-worker → Configure** screen, check that repository access is **Only select repositories**, with exactly **`abiggerhammer/phil`** selected. Record a redacted owner-attested inventory receipt without showing installation credentials. The prior JWT metadata checked `repository_selection=selected` but not the complete selection. If it includes another repository, STOP rather than granting more scope.

**Phase 2 — independent review of a real negative-test implementation and cleanup.** Before any credential-bearing write attempts, require an independently accepted source-only manual plan that:
- Authenticates **the actual worker App** and exact installation ID/permissions again using a main-only protected environment; never passes the token/key to a worker, untrusted code, GitHub issue/PR, URL, command line, artifact or log.
- Verifies current ruleset #27365284, exact reviewed `main`, fresh unused nonce, empty (or separately reviewed) admitted namespace, and exact safe Git object SHA **immediately before each request**.
- Pre-authorizes a **separate, independently reviewed publisher App** cleanup path. Publisher App 5782193 is the only ruleset bypass, so a successful supposedly-denied ref operation can create an **undeletable-by-worker protected orphan**. Do not attempt creation until publisher cleanup can actually be executed and validated; do not use a maintainer PAT as a substitute for the publisher.
- Runs **serially**, single request at a time. **Immediately STOP on an unexpected 2xx**, an ambiguous 4xx/5xx, changed identity/ruleset, a late SHA mismatch, or resource contention. Explicit permission/ruleset denial must be identified from status **and** response body, not merely any `422` validation failure. Authenticate the token principal, and never retry an ambiguous response automatically.
- Retains status/denial messages, exact ref names/SHAs, App/installation IDs, GitHub Actions run IDs and post-action `Token revoked` result in a **sanitized ledger**. Keep credential and secret values out of the ledger.

**Phase 3 — bounded negative sequence, separately authorized.** All target refs must be **fresh single-component leaves** under `hamster/admitted/*`, not existing production branches. The planner produces two names:
- `hamster/admitted/w3-<nonce>-create`: initially absent; worker-token CREATE should be **denied**. If unexpectedly allowed, stop and invoke preauthorized **publisher-only** cleanup; never open a PR from that ref.
- `hamster/admitted/w3-<nonce>-seed`: first created at a known harmless SHA by the **publisher App only** after cleanup authorization. Worker-token UPDATE, FORCE-UPDATE and DELETE must then be denied on that **exact disposable ref**. Re-read its SHA after every negative; on any unexpected success stop and restore/cleanup through publisher-controlled, independently reviewed procedure. Ensure publisher seed creation is itself assessed for unexpected push-CI fanout before running.
- Direct worker-token PR CREATE must be tested only against a **separately approved benign valid head** that cannot access release secrets. **Unexpected success can immediately trigger ordinary PR CI**, so an abort-after-success cannot undo the work already scheduled. Review and authorize this possibility before issuing POST; a 422 for invalid head does **not** prove permission denial.
- Worker-token PR REOPEN requires a separately approved disposable, closed, **never-merge** PR. **Do not use existing user work**, and do not let a same-repository PR go through signing. Preauthorise closure/cleanup if unexpectedly reopened.

**Phase 4 — ATC end-to-end commissioning**, only after worker denials: a separately reviewed publisher-created immutable admitted PR, no-second-slot and crash/reconciliation checks, real worker-App staged-push G1 trigger isolation, and no ref reuse. Record everything in #1839; this is **not part of this PR**. Then one bounded Phase 2 lane pilot, with later expansion.

## Read-only snapshot instructions (after source-only review and merge)

On Jarvis with the existing owner GitHub CLI authentication, from a **clean** updated `main` checkout:

```bash
git switch main && git pull --ff-only
test -z "$(git status --porcelain --untracked-files=all)" || exit 1
gh auth status

tmp="$(mktemp -d)"
gh api repos/abiggerhammer/phil/git/ref/heads/main > "$tmp/main-before.json"
gh api repos/abiggerhammer/phil/rulesets/27365284 > "$tmp/ruleset.json"
gh api repos/abiggerhammer/phil/git/matching-refs/heads/hamster/admitted/ > "$tmp/refs.json"
gh api repos/abiggerhammer/phil/git/ref/heads/main > "$tmp/main-after.json"
nonce="$(openssl rand -hex 6)"

PYTHONDONTWRITEBYTECODE=1 python3 scripts/mhb_atc_w3_readiness.py \
  --ruleset-json "$tmp/ruleset.json" \
  --admitted-refs-json "$tmp/refs.json" \
  --main-before-json "$tmp/main-before.json" \
  --main-after-json "$tmp/main-after.json" \
  --nonce "$nonce"

rm -rf -- "$tmp"
```

These `gh api` operations are **GET only**; no worker App key or installation token is accessed. Keep transient raw snapshots outside the repository. Share only the sanitized planner result, **not** any token or private key. If any step fails, inspect without changing branch policies or loosening the ruleset. This report supports security review, not the execution of Phase 3.

## Source-only integration invariants

The MHB ATC Radar Replay executes **only synthetic offline tests** for the new planner. It neither calls GitHub's settings endpoints nor executes GitHub App signing or token minting. The trusted W1 preflight, W2 broker, admitted publisher, branch ruleset, release workflows and worker-lane registries are **unchanged** in this PR. The plan has no API write function. No completed result may be recorded as `W3 passed` without explicit real, credential-bearing denial receipts and verified cleanup.

**STOP:** Until all phases are independently reviewed and explicitly authorized, leave `broker_activation: disabled`, every configured Phase 2 lane disabled, and ATC auto-admission/staging flags OFF.