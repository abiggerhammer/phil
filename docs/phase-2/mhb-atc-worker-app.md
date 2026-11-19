# MHB-ATC W1 — shared Phase 2 worker App and credential preflight

**Scope:** [W1–W3 worker confinement #1863](https://github.com/abiggerhammer/phil/issues/1863), parent [ATC #1602](https://github.com/abiggerhammer/phil/issues/1602). The publisher side [#1849](https://github.com/abiggerhammer/phil/pull/1849), [#1858](https://github.com/abiggerhammer/phil/pull/1858), [#1860](https://github.com/abiggerhammer/phil/pull/1860) is separate. This document and preflight **do not activate** any worker or Phase 2 lane.

## Shared identity / immutable source intent

Maintainer-provided public identifiers pinned in [the source policy](../../.github/atc-worker-policy.json):

| Field | Expected |
| --- | --- |
| GitHub App slug | `phil-atc-worker` |
| App ID | `5836223` |
| Repository | `abiggerhammer/phil` only |
| App permissions | Metadata read (implicit), Contents read/write; **NO Pull requests / Issues / Actions / Administration / Workflows** |
| Key custody | Separate `atc-worker-broker` Actions environment, restricted to `main` |
| Environment secret | `MHB_ATC_WORKER_APP_PRIVATE_KEY` (complete private PEM) |
| Nonsecret repository variables | `MHB_ATC_WORKER_APP_ID=5836223`, `MHB_ATC_WORKER_APP_SLUG=phil-atc-worker`, `MHB_ATC_WORKER_APP_CLIENT_ID` (actual Client ID from App settings) |

These ID/slug values were supplied by the maintainer. The source pin is **not** a claim that GitHub settings, permissions, installation or stored private key have yet been checked by the new preflight. In App settings, verify the actual numeric ID, slug, permissions and selected-repository installation. Confirm the environment's *Selected branches and tags* restriction has **only `main`**, and that its key lives in *Environment secrets*, not repository or organization secrets. Do not share the PEM in chat or commit it.

## Fundamental isolation invariant

GitHub App Contents-write applies to its **repository**, not a single lane. Minting an installation token for each of seven hamsters would not give them separate branch privileges. **The worker App key and every Contents-write token are held only by trusted, main-only staging broker code.** Workers do not receive the key, token, workflow environment, or a privileged execution hook. The future broker must authenticate each worker's lane identity and validate the exact requested staged ref and commit ancestry before *any* staged write. Never run staged code with the broker credential.

A worker may propose a commit or artifact; the broker decides whether to write it to `hamster/staged/<lane>/<candidate>`. The separate `phil-atc-publisher` App alone creates immutable `hamster/admitted/*` refs and admitted PRs. The earlier dormant [Phase 2 bridge #1838](https://github.com/abiggerhammer/phil/pull/1838) is **not** a lane security boundary and remains disabled.

## First live gate — manual no-repository-write credential preflight

[The worker preflight workflow](../../.github/workflows/mhb-atc-worker-token-preflight.yml) is deliberately `workflow_dispatch`-only, requires `refs/heads/main`, and uses the main-restricted `atc-worker-broker` environment. It rejects activation flags that equal `true` in any case before minting a token. It checks the configured worker App ID and slug against source policy, and fetches its GitHub bot identity with the ordinary Actions token. It then uses the **existing pinned** `actions/create-github-app-token` action and the protected worker key to mint one token requesting **Contents write only** (Metadata read implicit; no PR permissions requested). The actual minted token is used solely for **GET `/installation/repositories`**, which must return exactly one repository: Phil. The authenticated action `app-slug` must equal the pinned slug, and installation ID must be valid.

Only **after source review and a green protected merge**, a maintainer may manually start it from Jarvis:

```bash
gh workflow run mhb-atc-worker-token-preflight.yml \
  --repo abiggerhammer/phil --ref main
```

Record exact run/job IDs, checked-out `main` SHA, App slug, installation ID, permitted token-visible repository and the post-action cleanup result in [#1863](https://github.com/abiggerhammer/phil/issues/1863). The preflight summary says revocation is **enabled**, not necessarily completed; inspect the post-action log for the actual `Token revoked` result or a warning.

**Important limitations:** This is a token mint and revocation, not a GitHub repository write. A green result proves this *token* can read metadata for just Phil and came from the expected App slug; it does **not** independently prove the underlying App's full installation selection, absent Pull requests permission, inability to write protected refs, per-lane isolation, or the broker's future correctness. Those require settings verification and controlled negative tests against the real principal.

## Subsequent W2/W3 gates — not part of this PR

1. Implement and independently review the trusted stage-only broker, explicit lane-owner registry and exact-head request validation. Do not pass the token to hamsters.
2. Using an actual broker-held worker App token, perform bounded negative checks for **protected ref creation/update/force/delete and direct PR creation/reopen**. Use safe disposable objects; do not attempt to alter active work. Stop on any unexpected success.
3. With a separately authorized publisher trial, admit one never-merge PR, test staged push isolation, single-slot capacity, orphan/reconciliation behavior, and close it without merge.
4. Pilot one Phase 2 lane, then scale to seven only after the previous gates are evidenced.

**All activation switches remain OFF**: `MHB_ATC_AUTO_ADMIT_ENABLED`, `MHB_ATC_IMMUTABLE_HEADS_ENABLED` and `MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED`. No source merge, preflight run or credential probe authorizes enabling them.
