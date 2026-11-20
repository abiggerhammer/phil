# W3 publisher-App canary: nonce-specific activation-readiness packet

**Prepared:** 2026-11-20 (Europe/Brussels).
**Current decision:** PREPARED FOR OWNER VERIFICATION AND ASTRA REVIEW ONLY.
**No live publisher authority. Do not dispatch mode=run.**

This packet follows accepted, merged dormant W3 publisher canary/recovery
PR #1963 (reviewed head 4bf41d079fd279c99a44329e780426a8a87a42bb),
the read-only event-census observer #1961, and frozen-target/current-default
quarantine #1953. The independent original-run mode wording correction is
tracked in documentation PR #1964. Source-only cleanup eligibility hardening
accompanies this packet and needs a new independent exact-head review.

## 1. Single proposed nonce and exact future mutation

Candidate nonce: d948536ad68f
Status: PROPOSED-RESERVED ONLY; not owner-approved, not source-activated,
not attempted. The owner must check all other nonce records before approving.

Original-run canary ref:
    refs/heads/hamster/admitted/w3-fanout-d948536ad68f-canary

Frozen ref target:
    e38814a2e916252a8a7f3dd438943e8f4a21664a

Historical target .github/workflows Git tree:
    4b8b338a7a0ebed852407c9288d4a293bc26066f

Repository: abiggerhammer/phil
Publisher App: ID 5782193, slug phil-atc-publisher
Ruleset: #27365284, sole integration bypass ID 5782193
Authorized operations after future approval: at most one CREATE
(POST /git/refs) and one exact DELETE. No UPDATE, FORCE, PR creation,
worker App token, admission or main-branch mutation.

This candidate was generated cryptographically. A connected search of
repository code and GitHub issues on 2026-11-20 found no matching nonce.
That is NOT an exhaustive or owner-authenticated reservation check.
See mhb-atc-w3-fanout-nonce-ledger.md.

## 2. Source-controlled safety snapshot: verified during packet drafting

- The owner-visible GitHub ruleset was ACTIVE; its updated_at was
  2026-11-16T11:31:08.503+01:00 and its bypass list contained only
  publisher App 5782193. GitHub returned zero refs under
  refs/heads/hamster/admitted/.
- Trusted main snapshot: f7cff0fb353d6c072de01235743f047391b515ad.
  Its .github/workflows tree was
  b00f490f03e284ae67ea0adb16a5c5f96a59d3ee (626 workflow blobs).
  This tree is intentionally NOT the frozen historical target tree;
  the semantic G1 quarantine must validate the live default tree again
  immediately before each real protected-ref mutation.
- Actual source policy .github/atc-w3-fanout.json still had
  source_authorized: false and approved_nonce: null.
- The separate W3 source policy still had live_authorized: false,
  approved_nonce: null and push_ci_quarantine_verified: false.

All snapshots above can become stale after hamster merges and are
NOT standing authorization for a future time. Repeat the reads at
the supervised live preflight.

## 3. Owner-only checks NOT verified by this GitHub connection

GitHub's accessible repository APIs do NOT expose the environment and
Actions variable settings through this connection. These are mandatory
owner inspection items, not already-green gates.

- [ ] In GitHub repository Settings > Environments > atc-publisher,
      confirm the environment exists, restricts deployment to trusted
      main only, and has the intended required reviewers/approvals.
      Confirm no unreviewed path grants its publisher key to PR/fork jobs.
- [ ] In Settings > Secrets and variables > Actions > Variables,
      confirm MHB_ATC_W3_FANOUT_ENABLED is unset or NOT exactly true
      today; record the observed value/time without disclosing secrets.
- [ ] Confirm MHB_ATC_W3_REF_TRIAL_ENABLED,
      MHB_ATC_WORKER_BROKER_ENABLED,
      MHB_ATC_IMMUTABLE_HEADS_ENABLED, MHB_ATC_AUTO_ADMIT_ENABLED and
      MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED are all OFF.
- [ ] Confirm publisher App installation is scoped to Phil alone with
      the intended Contents-write token permission, ID 5782193 and
      authenticated slug phil-atc-publisher. Do not copy private keys,
      installation tokens, or secret values into PRs, logs or chats.
- [ ] Recheck the live ruleset ID/version, exact bypass and full admitted
      prefix occupancy; verify current default main's full semantic G1
      workflow quarantine and the historical target SHA/tree.
- [ ] Verify no original fanout attempts exist for this nonce in any
      owner-controlled run history or off-repository reservation ledger.
      Explicitly confirm or retire the reservation.

Previous successful publisher credential preflights and dormant-source
acceptance are helpful background, not substitutes for fresh inspection
before this specific nonce's live use.

## 4. Separate reviewable authorization: NOT applied by this packet

A future dedicated activation PR, and ONLY that PR, may propose the
following changes to .github/atc-w3-fanout.json after the owner verifies
the checklist and Astra reviews the activation's exact head:

    "source_authorized": false   -> true
    "approved_nonce": null       -> "d948536ad68f"

These are proposal lines, NOT changes in this packet's Git tree. Keep
W3 live_authorized false, W3 push_ci_quarantine_verified false, all
worker/broker activation switches OFF, and other source policies intact.

Before merging that activation PR:

- [ ] Astra independently ACCEPTS the exact activation head, source
      guards, environment and recovery safety contract.
- [ ] Required CI on that exact head is fully green; a new head needs
      fresh evidence.
- [ ] The owner explicitly authorizes exactly one live run and confirms
      nonce d948536ad68f and one-time reservation.
- [ ] Document the approved source SHA, owner decision and original
      expected runtime variables in the audit thread.
- [ ] Decide on a short, controlled main-merge quiet window between the
      original owner dispatch and CREATE. The controller deliberately
      stops if main moves during that period. This is NOT a request to
      pause hamsters during design review.

No source/runtime toggling or App-token minting may be done on the
strength of this packet alone.

## 5. Supervised future runbook (not authorized by this packet)

A. Before enabling anything, owner may run the manual workflow
   MHB ATC W3 Publisher Fanout Canary with:
      mode: plan
      nonce: d948536ad68f
      confirm: PLAN_ONLY
      original_run_id: (empty)
   Plan is GET-only and must not mint a publisher token or write refs.
   Inspect the exact run SHA, ruleset/namespace and STOP/plan receipt.

B. After separate source activation acceptance and owner sign-off,
   use GitHub Actions Variables to set MHB_ATC_W3_FANOUT_ENABLED to
   exactly true for the single supervised original run. Keep the other
   five activation switches OFF. Preserve that fanout variable until
   the automatic cleanup result/absence is independently confirmed,
   or explicitly switch to the manual recovery procedure. A runtime
   switch change must never strand a known original canary.

C. Before the write, capture a bounded read-only push/create/delete
   Actions run census with the already accepted observer #1961. Use
   one common fixed UTC window around the intended run, <=120 minutes,
   with fewer than 200 Actions runs per event, and retain the original
   source/head/window metadata. The observer takes only an Actions-READ
   token, not a publisher App token. Record the before snapshot.

D. Single owner/manual first-attempt workflow dispatch from main:
      mode: run
      nonce: d948536ad68f
      confirm: AUTHORIZE_W3_FANOUT_CANARY_ONLY
      original_run_id: (empty)
   Observe the protected atc-publisher approval. Do not rerun a
   failed/ambiguous run or reuse the nonce.

E. Confirm actual publisher CREATE only at the exact frozen SHA,
   HTTP 201, exact ref readback and complete one-ref admitted census.
   Observe the separate automatic cleanup; require actual HTTP 204,
   absent exact ref and empty admitted prefix, not merely a scheduled
   cleanup step. Check action post-job logs for actual token revocation.

F. If cleanup was canceled, failed, skipped, or ambiguous, STOP the
   experiment. Use the separately authenticated manual owner dispatch
   ONLY after inspecting the original-run ID and current ref census:
      mode: cleanup
      nonce: d948536ad68f
      confirm: RECOVER_W3_FANOUT_CANARY_ONLY
      original_run_id: (original numeric Actions run ID)
   That path authenticates the original run and the historically active
   source policy; it can work after current source/runtime are OFF.
   It may DELETE only the known exact canary SHA, never other refs or
   one whose ownership is ambiguous. No maintainer PAT fallback.

G. After a VERIFIED empty namespace, disable the fanout runtime switch
   and separately turn the source policy OFF by reviewed PR. Mark this
   nonce SPENT in the owner reservation ledger; never reuse it. Retain
   the original-run origin artifact before its 30-day expiry.

H. Complete a fresh after census for the SAME UTC interval, at least
   15 minutes after it closes. This lag is not a GitHub delivery SLA.
   Every positive candidate triggers immediate STOP/investigation.
   No candidates means review required, NOT automatic proof of absence.
   Preserve raw run IDs/actors/paths and sanitized receipts, including
   any main/default-branch delete-event ambiguity.

## 6. Evidence decision and remaining independent gate

Record the following in the audit issue #1839 with links to immutable
GitHub commit/run IDs, excluding any keys or bearer tokens:

- Owner's reservation approval and environment/variable observations.
- Actual activation source SHA, original owner/manual run ID, nonce,
  original origin artifact and historic pinned policy blob.
- The Publisher App action's authenticated slug/installation audience,
  both request intents, response statuses and exact post-state reads.
- Full admitted-ref namespace snapshots before CREATE and after cleanup.
- Explicit confirmation of post-action App token revocation in logs.
- Before/after event census, exact UTC bounds, candidate run IDs and
  independent attribution review. Treat delayed/incomplete runs as STOP.
- Formal independent verdict on whether this observation supports a
  future, separate reviewed change to W3 push_ci_quarantine_verified.

A green canary workflow or zero apparent fanout is NOT itself permission
to activate W3 worker denials, broker, admission or Phase 2 deployment.

**STOP conditions:** missing or unsafe default workflow semantic
inventory, changed ruleset, any nonempty/foreign admitted ref, main SHA
drift during original CREATE, mismatched original Actions run or source
policy, unapproved nonce, inaccessible environment constraints, failed
App principal/audience check, ambiguous HTTP/readback, incomplete
cleanup/revocation evidence, or any unexpected Actions run.

The final read/write gap is not atomic with GitHub. Explicitly accept
that residual risk in the one-time live review; otherwise defer.
