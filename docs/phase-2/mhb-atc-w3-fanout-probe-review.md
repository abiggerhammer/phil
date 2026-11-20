# W3 publisher fanout — dormant mutation/recovery review record

**STATUS: DORMANT SOURCE CANDIDATE. NOT LIVE AUTHORIZED.**

This is the separate publisher-App canary and cleanup implementation
following accepted read-only observer #1961 and frozen target/default
quarantine #1953. It deliberately leaves the separate W3 activation
switches OFF and has no real publisher-token or protected-ref execution.

## Exact fixture, identity and source gate

- Fanout policy .github/atc-w3-fanout.json stays source_authorized=false
  and approved_nonce=null. No nonce has been selected or consumed.
- A new MHB_ATC_W3_FANOUT_ENABLED repository variable must be explicitly
  true, together with an independently reviewed source/nonce activation,
  before any original CREATE job can run. It is currently unset/OFF.
- W3 live_authorized=false, W3 approved_nonce=null, and
  push_ci_quarantine_verified=false remain unchanged. Worker broker,
  automatic admission, stage bridge and immutable heads also stay OFF.
- Only ref: refs/heads/hamster/admitted/w3-fanout-<nonce>-canary.
- Only target commit: e38814a2e916252a8a7f3dd438943e8f4a21664a.
  Historical target .github/workflows tree:
  4b8b338a7a0ebed852407c9288d4a293bc26066f.
- Only original-run ref operations: one POST /git/refs with exact ref/SHA
  and one DELETE of that exact ref after readback. No PR, issue, worker,
  force, PATCH, arbitrary SHA, or retry.
- Ruleset: 27365284, sole publisher App bypass ID 5782193. Token action
  authenticates slug phil-atc-publisher and installation; token's
  /installation/repositories GET must enumerate Phil alone.

## Three manual-only jobs and privilege boundaries

The new .github/workflows/mhb-atc-w3-publisher-fanout.yml declares only
workflow_dispatch modes plan/run/cleanup, requires owner/manual main,
first attempt and separate confirmation, and uses the shared
mhb-atc-admission-global noncanceling concurrency group. Every checkout
is the exact dispatch github.sha, fetch-depth 0, no persisted credentials.
The SHA-256-pinned G1 YAML parser installs before App-key or token access.

The unprivileged prepare job checks source activation for run mode,
ruleset, complete admitted-ref occupancy, frozen target ancestry/tree,
and current-default semantic push/create/delete exclusion. It creates
and uploads a 0600/fsynced nonsecret original-run binding BEFORE the
publisher App token can be minted. Plan mode is GET only with source OFF.

The publisher CREATE job re-downloads and authenticates that original
binding with read-only GitHub token, then mints a Contents-write-only
Phil-scoped publisher App token in protected atc-publisher environment.
The token action is SHA-pinned and has skip-token-revoke:false. A
new independent current-default SHA/tree semantic check precedes the
exact CREATE; operation INTENT is fsynced before the request. HTTP status
and ref readback are recorded afterward. The CREATE job does not delete.

A distinct always()-guarded cleanup job is arranged after success,
failure or cancellation of the CREATE job when a prepare run succeeded,
and also serves a separate owner/manual cleanup dispatch. It fetches
the original-run binding and authenticates the original GitHub run and
historical policy BEFORE any publisher token is minted. If the admitted
prefix is empty, no App token and no DELETE are needed. If the only
ref is the exact authorized canary at the expected SHA, cleanup gets a
separately scoped App token, validates the current-default tree again,
persists INTENT, attempts one DELETE, reads back the ref, verifies an
empty admitted namespace and records a sanitized final receipt.
Cancellation can still prevent automatic cleanup or artifact upload;
the manual independent recovery path remains mandatory.

App-token revocation is registered by the pinned action post hook.
Hosted token-revocation log and final census evidence remain separate
requirements; a green cleanup step is NOT an independent proof that
the token was actually revoked.

## Original-run binding and independent recovery

MHB-ATC-W3-FANOUT-ORIGIN-V1 records the original run ID, owner/main
dispatch SHA, exact nonce/ref, target/tree, source-policy Git blob SHA,
workflow path and run identity. Recovery GETs the original Actions run
and independently checks its ID, owner and triggering actors, repository,
source branch/SHA, first attempt, and workflow path. The canonical origin
artifact and trusted run-only prepare/upload path establish the original
`mode=run`; the Actions GET does not independently validate that dispatch
input. The original source policy blob must be reconstructed from the authenticated
original dispatch commit and must demonstrate source_authorized:true
and the exact approved nonce. That original commit must remain reachable
from current trusted main. Current source may have gone OFF while
independent cleanup is still permitted by proven original authority.

This composes authenticated run provenance with trusted Git object
identity and original artifact custody; it does not claim a stand-alone
remote proof that every historical source was independently audited.
If the original artifact, run, Git objects or exact origin are missing,
recovery STOPs without guessing or falling back to a maintainer PAT.
The binding artifact currently expires after 30 days; later recovery
may require manual escalation rather than bypassing origin verification.

## Ref-state and current-default protections

Before CREATE, the entire admitted prefix must be EMPTY and the canary
must be absent. Before DELETE, either the entire prefix is empty
(idempotent success without a token/write), or the canary is the SOLE
admitted ref and points to the independently pinned exact target SHA.
A foreign/ambiguous ref, wrong rule version, altered App identity or
unsupported Git workflow trigger causes STOP.

Before each mutation, inspect the current GitHub default main SHA and
the exact Git workflow tree via the accepted strict G1 semantic
validator. Store operation/default-SHA/default-tree separately from the
historical target pin. Read main again immediately before sending the
write. Cleanup may allow main to advance, but MUST newly validate its
tree and never reuse stale evidence. GitHub offers no atomic
last-GET-to-ref-mutation transaction: that residual concurrency race
is not claimed eliminated. No retry occurs after an ambiguous request.

The new sanitized, fsynced FanoutEvidence ledger records separate
original/controller dispatch SHAs, exact App/installation, nonce,
historical target, current-default checks, INTENT, RESPONSE, READ,
VERIFIED and STOP, without logging raw exception/API bodies.
An uncertain post-state remains incomplete and requires independent
reconciliation, never a fabricated green receipt.

## Gates still outstanding

1. Astra's independent exact-head review, Radar Replay and full PR CI.
2. Separate owner/source activation PR approving a fresh never-used nonce
   and the exact new runtime switch/environment, with all other lanes OFF.
   Owner must maintain a nonce reservation ledger: an absent Git ref
   alone is NOT proof that a deleted nonce has never been used.
3. Supervised real App operation and immediate readback plus independent
   confirmation of cleanup, final namespace census and token revocation.
4. Read-only complete push/create/delete event census from #1961,
   reconciliation of uncertain or delayed runs, and separate review
   before changing W3 push_ci_quarantine_verified. No automatic
   fanout certification or W3/worker-broker activation.

## Independent reviewer focus

Check both actual source and authorized execution paths: manual owner
conditions, exact historical source policy, authentic original Actions
run and no token before successful unprivileged preflight; one CREATE
and max one DELETE with proper 0600/fsync evidence; cleanup idempotence,
foreign-occupancy STOP and recovery after main/source activation changes;
current-default semantic quarantine before CREATE and DELETE; token
principal and Phil-only audience; automatic-cancellation and manual
recovery limits; no authority escalation or source switches changed.
