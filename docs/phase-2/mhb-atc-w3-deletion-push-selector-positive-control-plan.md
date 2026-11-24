# W3 branch-deletion push-filter positive control: disposable-repository protocol

**STATUS: SOURCE-ONLY PLAN — NOT AUTHORIZATION TO RUN.**
This is a proposed, independently reviewed experiment for a **new, disposable
GitHub repository** selected and configured by the owner. Do not run against
`abiggerhammer/phil`, use either production Phil GitHub App/key, install
new software in Phil's privileged environments, or change W3 source/runtime
flags. No protected refs, branch rulesets or CI in Phil are test subjects.

Tracking: [conditional assurance #1979](https://github.com/abiggerhammer/phil/pull/1979),
[W3 fanout canary #44877317938](https://github.com/abiggerhammer/phil/actions/runs/44877317938),
[immutable-admission gate #1839](https://github.com/abiggerhammer/phil/issues/1839).

## 1. One question, one precise countermodel

**External premise under test:** For a `push` event that GitHub Actions
recognizes as caused by deleting branch ref `r`, the `on.push.branches`
and `branches-ignore` predicates are evaluated against the original
deleted ref `r`, even if the run's selected default-branch workflow
revision, `GITHUB_SHA` or `GITHUB_REF` falls back to `main`.

Countermodel: `r=refs/heads/hamster/admitted/w3-<nonce>-canary` is deleted,
and GitHub erroneously treats the fallback default branch `main` as the
**branch-filter input**. Then `on.push.branches: [main]` could fire,
despite Phil's G1 static exclusion of the W3 branch family.

The official general Actions branch-filter documentation says selectors
match Git ref names; the Actions `push` documentation says a branch-deletion
run's SHA/associated refs revert to default branch. These are distinct
statements, and do not independently resolve the deletion-specific filter
input. This experiment provides positive/negative control observations,
not a universal delivery-completeness guarantee.

Official references:
- https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/trigger-a-workflow
- https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows
- https://docs.github.com/en/actions/concepts/security/github_token

## 2. Isolation and setup requirements

1. Use a **separate disposable repo**, not Phil, owned/controlled by the
   operator. No production workflows, runners, branch rulesets, deployments,
   secrets, release automation, or protected environments.
2. Use GitHub-hosted runners; each witness job has `permissions: {}`, no
   checkout, no repository write, no third-party actions, no artifacts
   containing credentials, and a short timeout (e.g. two minutes).
3. Put the **four workflow variants below** on default `main`, with
   distinct names/immutable source markers. Ensure Actions is enabled and
   all workflows are active. No path filters, reusable workflows or other
   triggers. The unfiltered witness may observe `create` and `delete`
   as well as `push`, but the other three are push-only.
4. Prepare the disposable target commit with the **same four workflow
   files** but with an intentionally different literal marker in each
   name/log step, e.g. `TARGET_V1` versus `DEFAULT_V1`. It may be
   prepared on a separate temporary setup branch, then pinned by exact
   commit SHA. Setup traffic must finish before experimental capture.
   Do not try to infer workflow-file selection solely from `GITHUB_SHA`.
5. Use a **fresh** disposable W3-format single-component branch ref,
   `refs/heads/hamster/admitted/w3-<nonce>-canary`, and exactly one
   known target commit SHA. Do not reuse any Phil nonce.
6. Ref CREATE and DELETE must be sent via the GitHub **REST Git refs API**,
   from an **owner-local client outside Actions jobs** using a token that
   can produce ordinary downstream workflow events. An authenticated
   owner CLI credential is acceptable for testing **branch selector
   behavior**; a distinct test-only GitHub App installation token would
   additionally test App-origin behavior. **Never** use a workflow's
   `GITHUB_TOKEN` as the mutator: its recursion suppression invalidates
   the inference. Do not transmit, print, upload or record token values.
7. Confirm the default branch stays `main`, nobody else mutates the test
   repo during the bounded experiment, and no other refs share the test
   prefix. Separate all phases by completed runs and their recorded UTC
   bounds. Never change `main` during the deletion observation phase.

## 3. The four tiny workflow variants

For each witness, use an exact, distinct filename and workflow `name`,
and a single no-checkout shell step emitting ONLY a fixed witness marker
and selected event fields:

```
witness=<UNFILTERED|MAIN_ONLY|W3_ONLY|IGNORE_PAIR>
source_marker=<DEFAULT_V1|TARGET_V1>
run_id, event_name, event_ref, event_created, event_deleted,
github_ref, github_sha, actor, workflow_ref
```

Pass dynamic fields via `env:` (rather than splicing untrusted event
values into shell source); print them as quoted `printf '%s'` data.
For `push`, retain the payload `ref`, `created` and `deleted`
fields **independently** of `github.ref` and `github.sha`. For
`create` / `delete`, record their event ref/type separately. No
full event dump, raw token, secrets, checkout, or workflow-generated
ref mutation. Retain GitHub run IDs, event, creation time, and selected
workflow revision/name through independent read-only API requests.

The workflow triggers must be **exactly**:

| Witness | Trigger section |
| --- | --- |
| **UNFILTERED** | `on: [push, create, delete]` |
| **MAIN_ONLY** | `on: {push: {branches: [main]}}` |
| **W3_ONLY** | `on: {push: {branches: ['hamster/admitted/w3-*']}}` |
| **IGNORE_PAIR** | `on: {push: {branches-ignore: ['hamster/staged/**', 'hamster/admitted/w3-*']}}` |

Use the equivalent expanded YAML mapping if a quoted/flow expression would
be harder to audit. `IGNORE_PAIR` must preserve the same exact two
patterns and order accepted by Phil's G1 validator. Distinct markers
matter: default and target workflow trees must be distinguishable.

## 4. Serial experiment protocol

For **each** phase, save a read-only before inventory and then capture
all `push`, `create` and `delete` Actions-run IDs in a tightly bounded
UTC window, paginating fully. Include an observation lag (e.g. 30 minutes)
and an additional delayed-tail check, documenting that neither is a GitHub
delivery SLA. Runs may remain queued; do not classify until their relevant
metadata/logs are available. Store original raw curated inventories and
the observer command/script version, exact repo ID, commit/tree IDs,
workflow blob IDs, client class, and API response statuses.

**Phase A — main positive control.** From the owner-local client,
make one ordinary controlled commit/push to the disposable `main`, and
confirm that UNFILTERED, MAIN_ONLY and IGNORE_PAIR run while W3_ONLY
does not. Fail STOP if those positive controls are absent or ambiguous.

**Phase B — W3 ref CREATE.** Perform exactly one
`POST /repos/{owner}/{repo}/git/refs` with the disposable ref and
the pinned target commit SHA. Read back exact ref/SHA; observe the
separate creation window. Expect UNFILTERED and W3_ONLY to report a
`push` for the target ref when delivery occurs, and `create` in
UNFILTERED when delivered. MAIN_ONLY and IGNORE_PAIR must not report a
matching W3-`push` run. A missing W3 positive control is an
**inconclusive setup**, never evidence for branch disjointness.

**Phase C — W3 ref DELETE.** With the target still at the expected
SHA and all creation runs reconciled, send exactly one
`DELETE /repos/{owner}/{repo}/git/refs/heads/hamster/admitted/w3-<nonce>-canary`
from the same non-`GITHUB_TOKEN` owner-local client. Read back ref
absence; save the exact HTTP result and independently confirm it is
gone. Capture the distinct deletion interval and its delayed tail.
Never assume an HTTP 204 by itself proves event selection.

**Phase D — end state.** Confirm the disposable ref is absent, all
candidate run IDs have been reconciled, and no other experimental
branches remain. Delete the test repo only after exporting sanitized
evidence and obtaining reviewer signoff on completeness; preserve
original hashes even if the disposable repo is retired.

## 5. Interpretation and STOP conditions

| Observed deletion-phase result | Decision |
| --- | --- |
| UNFILTERED `push` witness has `event.deleted=true` and payload ref equal to the exact W3 branch; W3_ONLY also runs for that same deleted ref; MAIN_ONLY and IGNORE_PAIR do **not** | **Supports** the intended deletion-ref filter premise for this setup |
| MAIN_ONLY runs with a verified deletion-caused `push` payload referring to the W3 branch | **COUNTEREXAMPLE / STOP** — do not propose quarantine certification |
| IGNORE_PAIR runs with a verified deletion-caused `push` payload referring to the W3 branch | **COUNTEREXAMPLE / STOP** — investigate exact pattern semantics |
| UNFILTERED has only a separate `delete` event, or no deletion-caused `push` witness | **INCONCLUSIVE** — do not infer safe filtering from absence |
| Expected controls fail, events are ambiguous, run inventories incomplete, source markers missing, unrelated traffic overlaps, or credential provenance unknown | **STOP / REVIEW** |

Classify by **event payload**, exact event ref and run ID, not by
`GITHUB_SHA` equality or `github.ref` alone. A default-branch-looking
run can still belong to a deleted branch event. Conversely, unrelated
main pushes must not be mistaken for deletion-caused fanout.

A successful result corroborates the current GitHub Actions behavior
within the exact test context; it does not establish an unbounded
absence-of-delivery theorem. If GitHub produces no deletion-caused
`push` witness, consider reviewing raw webhook deliveries through a
separately approved test-only sink, or retaining the external premise
without setting the quarantine bit.

## 6. Independent review, authority and transition gates

**Before any execution:** Astra independently reviews the exact
four workflow YAML files, both distinct workflow-source revisions,
the mutator/census commands, all token/permission boundaries, and
this STOP matrix. The owner explicitly authorizes the one-time
disposable-repository run and supplies/approves the test repo name;
the test credential is never given to Phil automation.

**Before any later Phil policy-bit proposal:** Revalidate the actual
then-current full default tree and immutable target tree; resolve or
qualify the deletion premise; prove the actual event-selection tree was
among validated trees despite the non-atomic final GET/ref-write race;
audit all consumers of
`push_ci_quarantine_verified`, including the prior fanout
controller's **current-false** precondition in its authenticated
recovery path; and account for the W3 commissioning controller's
distinct source-retirement/recovery behavior. A bit-only change
cannot be assumed recovery-neutral.

No success here by itself authorizes
`push_ci_quarantine_verified:true`, W3 `live_authorized:true`,
a new Phil nonce, runtime variable enablement, worker-denial writes,
broker/pilot activation or PR CREATE/REOPEN. Those decisions each
require a separate exact-head reviewed source/owner gate.
