# MHB-ATC A3 — dedicated GitHub App / immutable PR heads

**Status:** draft implementation for [#1846](https://github.com/abiggerhammer/phil/issues/1846), underneath [A3 #1839](https://github.com/abiggerhammer/phil/issues/1839). **Never assume this document grants runtime activation.** The publisher is fail-closed and OFF unless its exact opt-in variable is enabled. Do not enable the Phase 2 worker bridge or unattended scheduler until the GitHub-side controls and live negative tests pass.

## Why a separate publisher principal

The older one-slot ATC creates its PR from the same `hamster/staged/<lane>/<candidate>` branch that a worker can advance. A later worker push can trigger a new `pull_request.synchronize` CI wave without a new admission decision.

This tranche changes the published head to a **new single-segment protected ref**:

```text
staged   = hamster/staged/<lane>/<candidate>
admitted = hamster/admitted/atc-<issue>-<lane>-<40-hex-registered-SHA>
```

The checked receipt binds the exact bot-authored candidate issue, lane, staged branch, admitted branch, repository, base `main`, and full source SHA. **A worker push to the staged branch cannot modify a PR whose head is the separate protected ref.** No update/force/delete code is provided for admitted refs. An orphan protected ref is not automatically re-used or silently requeued: the controller holds for investigation.

A GitHub App installation token, not `GITHUB_TOKEN` or a personal `HAMSTER_PR_TOKEN`, creates the protected ref and PR to trigger ordinary PR CI. Ordinary issue labels/recovery still use GitHub Actions' scoped default token. This is not merge authority.

## Maintainer provisioning (must happen outside this PR)

### A. Register the App

At GitHub **Settings → Developer settings → GitHub Apps → New GitHub App**, create a dedicated App (suggested name `phil-atc-publisher`, or another available unique name). Set its homepage to the Phil repository. **Disable webhook delivery** unless GitHub requires a URL for registration; no webhook events are needed for the publisher.

Repository permissions:
- **Contents: Read & write** — create SHA-pinned `git/refs`.
- **Pull requests: Read & write** — create the admitted PR.
- **Metadata: Read** — normally mandatory/automatic.
- No Actions-admin, Administration, Issues, Secrets, Workflows, or organization permissions for this App. Leave unrequested permissions at *No access*.

Install only into **`abiggerhammer/phil`**, not all repositories. Save its numeric **App ID** and **Client ID**, generate a private key, and never paste the key into an issue/chat or commit it to the repository.

### B. Protected Actions environment (credential isolation)

Create GitHub Actions environment **`atc-publisher`** under repository Settings → Environments. Set **Deployment branches and tags → Selected branches and tags → `main`**. Verify other branches and any workflow injected by a worker cannot access it. **Use an environment secret, not a repository-wide secret**, for the private key:

- Environment secret: `MHB_ATC_PUBLISHER_APP_PRIVATE_KEY` = complete generated private key; no Base64 required.
- Repository variable: `MHB_ATC_PUBLISHER_APP_CLIENT_ID` = App Client ID.
- Repository variable: `MHB_ATC_PUBLISHER_APP_ID` = numeric App ID (verified ruleset actor ID `5782193`).
- Repository variable: `MHB_ATC_PUBLISHER_APP_SLUG` = **the exact App slug** from its GitHub App settings URL (e.g. `phil-atc-publisher` if that is the actual slug). This is required for publisher-authored PR verification; missing or incorrect slug fails closed. It is not the client ID or installation ID.
- Repository variable: `MHB_ATC_PUBLISHER_RULESET_ID` = numeric protected-ref ruleset ID (after creating it).
- Repository variable: `MHB_ATC_IMMUTABLE_HEADS_ENABLED` = **unset/false until negative commissioning**.

Only the trusted main-branch `mhb-atc-admit.yml` job uses `environment: atc-publisher` and the App key. Set up the environment deployment restriction **before** adding the secret. Do not grant this environment to the Phase 2 worker workflows. Its default-token permissions remain scoped for queue and PR-label bookkeeping.

### C. Enforce the admitted namespace in GitHub

In repository Settings → Rules → Rulesets create a **branch** ruleset:

- Suggested name: `Phil ATC immutable admitted refs`.
- Enforcement: **Active**.
- Target: **only** `hamster/admitted/*` (in the REST API, `refs/heads/hamster/admitted/*`); **no exclusions**. The suffix `atc-<issue>-<lane>-<sha>` has no nested slashes.
- Rules: **Restrict creations**, **Restrict updates**, **Restrict deletions**, and **Block force pushes**.
- Bypass list: **only the exact new GitHub App**, **Always**. Do **not** add administrator, personal-account, team, generic Write or RepositoryRole bypasses. This App technically has bypass power, so the trusted workflow must remain create-only and its private key isolated.
- Record ruleset ID in `MHB_ATC_PUBLISHER_RULESET_ID`. The owner-reviewed ruleset **#27365284** and sole-App bypass **#5782193** are pinned in [the source-reviewed policy attestation](../.github/atc-publisher-policy.json). The unprivileged workflow token may see GitHub's ruleset response **without `bypass_actors`** (GitHub restricts that sensitive field). It checks the live `created_at` and `updated_at` timestamps and all other visible rules against the owner-approved exact version. If `bypass_actors` is visible, it must also match. **Any edit to the ruleset invalidates the attestation and stops admission.** A maintainer with ruleset-write access must re-read the full unredacted policy, independently review the sole-App bypass, and land a new exact-version attestation through a protected PR before resuming. Do not grant repository administration to the publisher to solve a read-visibility problem.

GitHub branch rules use pathname-style `fnmatch`, where `*` does not cover a slash. Test one valid `hamster/admitted/atc-...` branch against **actual** effective rules, not only against the text of the pattern.

### D. Worker credentials and direct-PR bypass

A dedicated publisher is **not** sufficient if the worker can use a different token to open direct PRs or modify protected refs. Phase 2 worker credentials must be confined to staged branch creation/update and **lack Pull requests write**. Verify the worker receives denied responses for protected creation/update/delete and direct PR creation, including reopen. Existing Phase 1 hamsters are separate and deliberately unchanged.

The design limits **Phase 2 worker-induced** extra CI waves. It does **not** globally throttle unrelated/manual/Phase 1 PRs or prevent a repository administrator from deliberately creating PRs. Future global CI admission requires a separate policy review.

## Trusted workflow transaction

1. Require the immutable publisher opt-in flag, real App token and live matching **owner-attested ruleset revision**. Manual `dry-run` remains usable while the flag is off, but its summary explicitly says the protected namespace was not fully verified. The main-only App action's reported slug must match `MHB_ATC_PUBLISHER_APP_SLUG`.
2. Confirm the configured publisher slug `phil-atc-publisher` and numeric App ID `5782193` exactly match the protected, source-reviewed policy attestation. A private account-only GitHub App returned **HTTP 403** from `GET /apps/{slug}`, both with the ordinary Actions token and without authentication. Do **not** require this inaccessible API or add Administration permissions. Instead, query the public GitHub bot user endpoint and check its canonical bot login, type and numeric user ID; the **protected main-only App token action** must separately authenticate the actual App and emit the *same* slug before any ref creation. If either proof is absent, stop. Enumerate **every** `hamster/admitted/*` ref; look up each original issue (including closed/unlabelled) and exact-head PR history. An unknown, modified, orphaned or mismatched ref blocks admission. Verified closed issue + closed PR pairs remain historical state.
3. Derive deterministic `hamster/admitted/atc-<issue>-<lane>-<sha>` and canonical receipt. Reject a pre-existing ref (including one with a matching SHA).
4. Persist `atc: admitting` **before** protected ref/PR creation. Add the new lifecycle label first, then remove the old label: interruption may leave **two** labels (a manual-recovery hard stop) but never silently erase the last state marker. Revalidate ruleset and staged head. Using only the App token, **create** the admitted ref at the recorded SHA; read back ref and SHA.
5. Create a PR from the **admitted ref** with the canonical binding receipt. Read back the PR's GitHub-reported `user.login`, `user.id`, `user.type`, plus `performed_via_github_app.id` when present, against the independently resolved publisher App/bot. Require exact head/base/body correspondence **and** authenticated origin. Copying the receipt cannot create valid provenance. Apply `atc: admitted` to issue and PR; use add-before-remove lifecycle transitions. Ordinary required checks run before any separate merge decision.
6. Reconcile **all protected refs** before any repair/release. The global census finds unknown or orphan refs even if their issue has lost labels, changed body/SHA or been closed. Authenticated publisher origin is mandatory before automatic PR repair or release; a canonical body alone is insufficient. Positive exact-head PR closure releases the issue; valid incomplete labels can be repaired. A protected ref with no genuine matching PR stops the controller, even after 15 minutes.
7. An `atc: admitting` issue without an admitted ref or PR can still be requeued after the original 15-minute grace and complete no-PR evidence. A missing/drifted ref linked to any PR is a hard stop.

## Migration/order and compatibility

- The opt-in admission scheduler [#1836](https://github.com/abiggerhammer/phil/pull/1836) has **merged** into `main` at `3aadc713db8abe51d27a2148b5d776c88e634889`; this A3 PR [#1849](https://github.com/abiggerhammer/phil/pull/1849) was subsequently **retargeted to `main`**. Review and execute the repaired final integration against the current `main` tree before approving.
- A2 [#1838](https://github.com/abiggerhammer/phil/pull/1838) remains a separate, default-OFF PR; its Phase 2 staging WIP guard does not grant admission or merge authority.
- The old commissioning C2 [#1834](https://github.com/abiggerhammer/phil/issues/1834) used staged PR heads; those specific PRs and issues are already closed. **After this code is merged, the manual `admit-one` route no longer falls back to that legacy behavior.** Without the App/ruleset gate, it fails closed.
- `MHB_ATC_AUTO_ADMIT_ENABLED` (scheduled pump), `MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED` (worker staging bridge), and `MHB_ATC_IMMUTABLE_HEADS_ENABLED` (publisher route) are distinct switches. Keep all off until deliberate commissioning.

## Independent review remediations (Astra, 2026-11-16)

[Astra's technical review](https://chatgpt.com/library/share/libfile_fde3_f-6b6ec9e585a8819193e7ccc3a1185fc7_1f438c6a20f081919fa023e16ee02d05?account_id=personal) requests changes F1–F3 and fresh current-base integration checks. The fixes above implement a **version-pinned owner attestation**, **full namespace/history accounting**, and **authenticated App PR origin**. The path-filtered replay workflow also exercises the actual lower-privilege Actions policy-reader identity on this PR, rather than assuming the owner-connected GitHub API response has the same visibility.

A label-swap failure may leave both the old and new state labels. The planner **fails closed** on dual labels; manual recovery must inspect the issue/events/PR/ref before restoring one consistent state. The publisher never auto-deletes or reuses protected orphan refs. All live platform permissions, App slug, metadata shape, ref/PR lifecycle and worker-denial checks remain a separate deployment gate.

## Astra activation readiness re-review (R1–R3, 2026-11-16)

[Astra's activation re-review](https://chatgpt.com/library/share/libfile_fde3_f-6c54970017a88191ae08deba02b791f5_1f438c6a20f081919fa023e16ee02d05?account_id=personal) examined an earlier head `4606fccf0a959ba2552e091ffbea0ca7de7103c0` and returned **REQUEST CHANGES**:

- **R1 (P1, App identity read)**: private App `GET /apps/{slug}` returned 403 to both Actions and unauthenticated requests. A later revision source-pins exact `phil-atc-publisher` slug and App ID `5782193`, verifies its GitHub bot profile, and requires the protected publisher token action's authenticated slug to agree. [Live ATC identity read](https://github.com/abiggerhammer/phil/actions/runs/43864966394) passed on the post-review head. There is **no App-administration credential** in the read-only path.
- **R2 (P2, outsider issue availability)**: admission and reconciliation now share the **same creator-aware open-issue classifier** in `scripts/mhb_atc_admit.py`. Unlabelled human-authored issues quoting `ATC candidate: ` or the public staging marker are ordinary issues and are ignored. Unlabelled **trusted-stage-bot** issues remain hard errors; every lifecycle-labelled claim is still inspected and untrusted/dual-state claims fail closed. The protected-ref census independently loads each referenced original issue, regardless of its labels or closure; this filter never reduces protected-ref coverage.
- **R3 (P3, prefix-matched sibling branches)**: GitHub `matching-refs/heads/hamster/admitted` may return unprotected siblings such as `hamster/admitted-not-atc` or the exact branch `hamster/admitted`. The census ignores only those **outside** `hamster/admitted/`. Unknown, malformed or drifted refs **inside** the protected namespace still hard-stop.

Regressions cover both benign outsider issue forms, trusted lost-label and dual-label cases, labelled foreign claims, shared workflow use, protected siblings, unknown inside-namespace refs, and valid closed historical records. These are source changes subject to **fresh exact-head CI and independent re-review**; they do not grant deployment, merge or unattended automation authority.

## Required live negative commissioning (not covered by offline unit tests)

1. Verify App installation scope, environment secret main-only access, actual active ruleset and unique App bypass.
2. With worker credential, attempt creation, update, force update and deletion in the admitted namespace; all must be **rejected by GitHub before a synchronize CI event**. Confirm worker cannot open/reopen PRs directly.
3. With publisher credential, create a never-merge PR at a **new protected SHA-pinned branch**, observe ordinary CI. Advance the *staged* ref; confirm admitted PR head unchanged and **no fresh PR synchronize CI wave**. Do not create a second admitted PR while one is open.
4. Test manual issue/PR tampering, wrong base/identity/receipt, duplicate admission, wrong App/ruleset, absent token, missing/stale checks. Each must fail closed.
5. Simulate partial transactions: orphan admitted ref but no PR, and PR created but labels missing. Confirm no duplicate PR, no accidental ref reuse, repair only on matching identity; release only after exact head closure.
6. Close all never-merge test PRs without merge; verify slot recovers and all candidate issues have explicit disposition. Record exact run IDs, SHA, source, ref and effective permissions in #1839 before any activation.

No Phase 1 semantic/TCB/grammar/freeze claim, automatic merge rights or repository-wide CI limit follows from this work.

Official references: [GitHub ruleset creation](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/creating-rulesets-for-a-repository), [ruleset REST representation](https://docs.github.com/en/rest/repos/rules), [App token action](https://github.com/actions/create-github-app-token), [GitHub App registration](https://docs.github.com/en/apps/creating-github-apps/registering-a-github-app/registering-a-github-app).
