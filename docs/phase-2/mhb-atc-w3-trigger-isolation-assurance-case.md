# W3 disposable-ref trigger isolation: scoped assurance case

**Status: DRAFT FOR INDEPENDENT REVIEW — NOT A QUARANTINE CERTIFICATE.**
No change to `push_ci_quarantine_verified:false`, `live_authorized:false`, nonce approval, source policy, GitHub settings, or runtime switches is authorized by this document.

Tracking: [worker confinement #1863](https://github.com/abiggerhammer/phil/issues/1863),
[immutable-admission boundary #1839](https://github.com/abiggerhammer/phil/issues/1839),
[frozen target/current-default validator #1953](https://github.com/abiggerhammer/phil/pull/1953),
[one-time W3 canary #44877317938](https://github.com/abiggerhammer/phil/actions/runs/44877317938),
[retirement #1977](https://github.com/abiggerhammer/phil/pull/1977).
The independent review of the event census is recorded with the retirement review.

## 1. Proposed claim, not unconditional GitHub-behavior proof

**Candidate scoped claim:** Under independently reviewed GitHub Actions event-selection
semantics, the exact frozen target workflow tree and the **freshly validated current-default**
workflow tree exclude ordinary `push`, `create` and `delete` workflow triggers arising from
a single W3 disposable admitted ref of the form

```
refs/heads/hamster/admitted/w3-<fresh-12-hex-nonce>-{canary,create,seed}
```

provided that the trusted controller enforces the full reviewed provenance,
ruleset/App identity, complete ref census, exact frozen commits/trees, and a
current-default SHA/tree-bound semantic quarantine **before every possible ref
mutation**. The guarantee is tied to those checks and the documented GitHub
trigger model, not to an eternal state of the repository.

**Out of scope:** arbitrary `hamster/admitted/*` refs, PR creation/reopen,
staged-worker pushes, broader automatic admission, legacy Phase 1 PR CI,
`workflow_dispatch` / `repository_dispatch` from independent actors,
unrelated webhook events, or all future GitHub Actions deliveries. A
time-bounded absence of observed runs is not a proof of eventual delivery
completeness or a platform-wide guarantee.

The desired assertion is **conditional trigger isolation of W3 disposable
refs**, *not* "the publisher GitHub App never causes any Actions run."

## 2. Evidence available now

### Historical source selection and static evidence

- Frozen target trio from source policy
  `.github/atc-w3-ref-trial.json`: source
  `d82a60a3c9f448c2e59ebe7bdfc710109159f7a9`,
  first parent `e38814a2e916252a8a7f3dd438943e8f4a21664a`,
  grandparent `4b7594ed83648372171a9bb1c34647522c064b22`.
  All select reviewed workflow tree
  `4b8b338a7a0ebed852407c9288d4a293bc26066f` (621 workflow blobs).
  The historical ancestry/selection contract was independently reviewed
  in #1953. The frozen targets are **data**, never privileged controller
  code.
- Strict source grammar and branch-disjointness checks:
  `scripts/test_mhb_atc_staged_push_ci.py`. For `on: push`, only accepted
  literal/terminal-glob branch allowlists disjoint from
  `hamster/admitted/w3-`, or the exact
  `branches-ignore: [hamster/staged/**, hamster/admitted/w3-*]`, are
  admitted. Unsupported selectors fail closed. Path filters cannot
  substitute for branch isolation.
- The current-default validator
  `scripts/mhb_atc_w3_default_quarantine.py` checks the **complete exact
  Git tree**, with strict parsing and rejection of unreviewed
  `on: create`/`on: delete`, unsafe `push`, incomplete inventories,
  non-workflow entries and oversized blobs. Its output binds a specific
  main commit SHA to the workflow tree SHA. The trusted W3
  `_write_and_record` wrapper runs this check before each protected
  ref request, including DELETE and independently authenticated recovery,
  then re-GETs main immediately before the request.

### Live publisher-App canary evidence

- Owner/manual original `workflow_dispatch` run
  [#44877317938](https://github.com/abiggerhammer/phil/actions/runs/44877317938),
  attempt 1, dispatch SHA `338a12849611e72610fb6ee1194dc9495935588f`.
  Real, Phil-scoped publisher App 5782193 CREATED the exact one-use canary
  with HTTP 201 and exact target SHA readback, then DELETED it with HTTP 204,
  verified absent ref and empty admitted namespace; the CREATE and
  cleanup token post-job logs each say `Token revoked`. All three original
  GitHub artifacts and both raw census snapshots are archived separately
  from the expiring Actions artifacts.
- Both actual protected mutations validated the **then-current** default
  commit `338a12849611e72610fb6ee1194dc9495935588f` and workflow tree
  `f73817adc849d925b258ea40775b981787ceb100` (630 workflows).
- Same-window before/after read-only census, UTC
  `2026-11-21T06:43:41Z` to `2026-11-21T07:43:41Z`:
  before and after each found the same unrelated push run
  `44877128877`; no newly reported `push`, `create`, or `delete`
  workflow-run IDs. The after capture was 2001 seconds after the window
  closed. Astra reproduced the bounded comparison and checked a further
  delayed tail with no matching candidates. The observer deliberately
  returned `NO_CANDIDATE_RUNS_REVIEW_REQUIRED` and
  `quarantine_certified:false`.
- This one canary exercises publisher CREATE and DELETE, **not** the
  later publisher seed or all worker-denial cases. It establishes bounded
  runtime evidence for the publisher token and trigger hypothesis,
  not a universal negative fact about the GitHub event dispatcher.

### Current tree is already different

At the time of this draft, `main` was
`796b4ba628125b94ebfaee513576707d744f2ef9`,
with current workflow tree
`18a5cca24aef4a62a0387f956a0bf7c7b83621b7` (631 blobs).
Relative to the live-canary commit, one
`fsem02-two-step-source-binder-preflight.yml` workflow was added,
and `phase1-surface-grammar-rocq-source-spine-correspondence.yml` changed.
Their visible `push` selectors target an FSEM branch and `main`,
respectively. That is **not a substitute for a complete fresh G1
validation of the new Git tree**. No perpetual certification of the
old default tree is implied.

## 3. External semantics and remaining trust assumptions

The GitHub Actions trigger engine is **outside Phil's trusted verifier**.
Its published model says that:

1. A separately minted GitHub App installation token can trigger new
   Actions runs; it does not inherit normal repository `GITHUB_TOKEN`
   recursion suppression.
2. `on: push` `branches`/`branches-ignore` selectors are evaluated
   against Git ref names. Branch creation/deletion are also `push`
   webhook events, in addition to distinct `create`/`delete` events.
3. On branch deletion, GitHub Actions may use the default branch's
   `GITHUB_SHA` and associated context; its `delete` event explicitly
   uses the default branch. **The verifier must not substitute a SHA
   equality check for an event-ref selector proof.** Review the
   deletion-side ref-filter semantics independently.
4. The Actions-run list is an inventory of *reported workflow runs*,
   not an authenticated ledger of all incoming webhook events or a
   guarantee of delivery by a fixed deadline.

Official references:
[GitHub token behavior](https://docs.github.com/en/actions/concepts/security/github_token),
[Triggering workflows and branch filters](https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/trigger-a-workflow),
[Events that trigger workflows](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows),
[Webhook push payload](https://docs.github.com/en/webhooks/webhook-events-and-payloads),
[Workflow selection](https://docs.github.com/en/actions/concepts/workflows-and-actions/workflows).

The final read-only default-SHA GET and a real Git ref mutation are not
an atomic GitHub transaction: main could advance after the GET.
Any later live commissioning must specify an owner-controlled quiet
window and independently accept or eliminate this residual race;
fail closed on detected drift and rerun the complete semantic check.

## 4. Acceptance questions for independent review

- [ ] **Scope:** affirm that the claim is only the W3 single-component
      disposable `w3-*` namespace and exact event classes/operations.
      Do not certify general event-delivery absence or Phase 2 PR CI.
- [ ] **Frozen trees:** verify actual Git object identity, first-parent
      relationships, merged-main reachability and strict G1 trigger
      disjointness of *all* workflows in the historical 621-blob tree.
- [ ] **Default trees:** validate the full actual current default SHA/tree
      and all triggers using the accepted strict parser, not a name-only
      grep or a prior workflow-count snapshot.
- [ ] **Deletion-side push:** independently justify, from GitHub's
      documented model and/or a separately scoped no-production-cost
      probe, the exact branch selector context after deletion. Treat an
      unresolved mismatch as a STOP for stronger certification.
- [ ] **Controller coverage:** check that every W3 protected-ref request
      (including failure cleanup and independently dispatched recovery)
      uses the same fresh validator, before-token/read-only checks and
      exact intent/response/readback evidence. Audit source/runtime
      authority, one-use nonce, App scope and worker denial paths.
- [ ] **Residuals:** explicitly document the post-GET concurrency race,
      failure/cancellation recovery, finite Actions event delivery
      observations and external GitHub semantics as separate assumptions.
- [ ] **No silent promotion:** require Astra's exact-head review,
      hosted CI, and an explicit owner decision before any PR sets
      `.github/atc-w3-ref-trial.json`
      `push_ci_quarantine_verified: true`.

## 5. Proposed staged decision

1. Independently review **this scoped assurance case and actual source**,
   resolving the deletion-side ambiguity and current-tree validation.
2. If accepted, a **separate, narrow source-policy review PR** may propose
   `push_ci_quarantine_verified:true` with an exact evidence ledger
   reference and explicitly limited W3 disposable-ref meaning. Keep
   `live_authorized:false`, `approved_nonce:null`, and all runtime
   switches OFF in that PR. Acceptance of this memo alone grants nothing.
3. A later **distinct one-time W3 negative-commissioning activation**
   needs a fresh never-used nonce, exact-head review, green CI and owner
   authorization, both publisher and worker identity/permission checks,
   the main quiet window, and independent cleanup. No PR CREATE/REOPEN or
   staged worker broker activation belongs to that experiment.
4. Retire the new nonce and source authorization after verified cleanup;
   never generalize a bounded no-observed-fanout result into a global
   repository CI-admission guarantee.

**Decision now: retain `push_ci_quarantine_verified:false`.** The
evidence supports a serious conditional assurance case, not an
unqualified permanent GitHub event-delivery theorem.
