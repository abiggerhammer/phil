# W3 publisher-App fanout: independently reviewed experiment protocol

STATUS: DORMANT, INDEPENDENT LIVE REVIEW REQUIRED.
The read-only observer is merged. A separately disabled, owner-only
publisher canary and authenticated recovery implementation are now
proposed in a new dormant source PR. No App token, protected-ref mutation
or workflow activation is authorized by the source additions.

Tracking: W3 worker confinement #1863, immutable-admission gate #1839,
and accepted W3 frozen/default-tree quarantine in #1953.

## The question

Does a protected branch created and deleted by the real Phil publisher
GitHub App unexpectedly schedule ordinary Actions workflows?

The repository's automatic GITHUB_TOKEN normally suppresses most
follow-on Actions runs, but a separately minted GitHub App token does
not have that suppression. Therefore an experiment using only the
ordinary GITHUB_TOKEN is not evidence about publisher-App fanout.

References:
- https://docs.github.com/en/actions/concepts/security/github_token
- https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows
- https://docs.github.com/en/rest/actions/workflow-runs

## Separate source policy, still disabled

The source policy for this proposed experiment is
.github/atc-w3-fanout.json. It explicitly has source_authorized=false
and approved_nonce=null. The existing W3 ref-trial policy independently
remains live_authorized=false, approved_nonce=null and
push_ci_quarantine_verified=false.

An exact-head separately reviewed activation PR must later approve a
fresh unused nonce and one tightly bounded publisher-only experiment.
It must not switch on the worker broker, automatic admission, or main W3
commissioning as a side effect.

The intended test object is:

- Ref: refs/heads/hamster/admitted/w3-fanout-<nonce>-canary
- SHA: e38814a2e916252a8a7f3dd438943e8f4a21664a
- The source object's workflows subtree:
  4b8b338a7a0ebed852407c9288d4a293bc26066f
- Ruleset: 27365284; sole bypass: publisher App 5782193
- Principal: Phil-only scoped phil-atc-publisher installation access token
- Original-run mutations: one exact CREATE, then one exact DELETE
- No seed branch, worker token, UPDATE, FORCE-UPDATE, issue or PR operation

The ref is within the already reviewed hamster/admitted/w3-* exclusion
and immutable admitted-ref ruleset, but its w3-fanout- prefix makes it
distinct from the main W3 one-time ref-test nonce namespace.

## Mandatory gate before any live publisher write

The proposed dormant implementation includes an owner-only manual
workflow, exact-intent controller, sanitized durable evidence, and an
authenticated original-run recovery path. Their presence is not
permission to run. See the separate implementation review record:
mhb-atc-w3-fanout-probe-review.md.

For that future implementation, Astra must review a finite owner/manual
main-only workflow with a separate runtime enable variable, strict
nonce and one-time use reservation, the publisher-only atc-publisher
protected environment, and token generation only after an unprivileged
read-only preflight. Both exact source and runtime gates must be ON
only after separate independent activation approval.

Before either mutation, revalidate trusted dispatch SHA and current
main, default_branch=main, complete current-default semantic workflow
quarantine, the pinned target SHA and frozen target workflow tree,
ruleset ID/version/bypass, App slug/installation identity and Phil-only
token audience. The namespace requirement is phase-specific:

- Before CREATE, require the admitted namespace to be completely empty
  and the exact proposed canary to be absent.
- Before DELETE, require the admitted namespace to contain only the
  exact previously authorized canary at the independently established
  expected frozen SHA. The DELETE path must recheck current-default
  workflow semantics under the accepted #1953 contract.

Commit a nonsecret, fsynced INTENT **before** each write. Record the
bounded actual HTTP status and independently read post-state **after**
the request; neither may be claimed until observed. A failed/ambiguous
CREATE must never be retried
without exact read-only reconciliation; an unexpected existing/foreign
SHA is a STOP. A failed DELETE requires publisher-only recovery, not a
maintainer PAT. A cancellation may prevent cleanup or artifact upload.
The dormant implementation provides an always()-guarded separate cleanup
job and independent manual recovery of an ORIGINAL authenticated run,
nonce, exact ref, and known SHA before token mint. The manual cleanup
does not rely on the runtime enable variable. It still requires the
original source to have been approved, the current-default quarantine,
and the protected publisher environment. Do not treat "cleanup
scheduled" as "ref absent". Retain final ref census and token-revocation
evidence; cancellation may prevent even the cleanup job from executing.

No publisher write should take place merely because this event observer
passes its offline tests.

## Read-only observation in a busy repository

The existing Actions history has substantial ordinary main-branch
traffic, so a simple before/after total count cannot prove isolation.

Capture full, paginated push, create and delete run inventories for
the SAME narrowly defined UTC interval before and after the supervised
probe. Our source-only script
scripts/mhb_atc_w3_fanout_observer.py
performs GitHub GETs only, requires an exact window of at most 120
minutes, enumerates every reported page in bounded four-run batches with a
separate GET-only fixed-route Actions HTTPS reader, no redirects or
retries and a 64 KiB response bound. It refuses windows with 200 or
more runs of any one event type and rejects count changes,
duplicates, foreign/malformed runs and oversized inventories, and
writes a curated local 0600 JSON snapshot. It deliberately never
certifies W3 quarantine.

Example CLI syntax (illustrative nonce/time ONLY, not permission to run
a publisher probe; replace with the actual separately approved values):

    python3 scripts/mhb_atc_w3_fanout_observer.py collect \
      --nonce d1e2f3a4b5c6 --role before \
      --window-start 2026-11-21T12:00:00Z \
      --window-end 2026-11-21T12:25:00Z \
      --out /tmp/w3-fanout-before.json

    python3 scripts/mhb_atc_w3_fanout_observer.py collect \
      --nonce d1e2f3a4b5c6 --role after \
      --window-start 2026-11-21T12:00:00Z \
      --window-end 2026-11-21T12:25:00Z \
      --out /tmp/w3-fanout-after.json

    python3 scripts/mhb_atc_w3_fanout_observer.py compare \
      --before-file /tmp/w3-fanout-before.json \
      --after-file /tmp/w3-fanout-after.json \
      --target-sha e38814a2e916252a8a7f3dd438943e8f4a21664a \
      --publisher-actor 'phil-atc-publisher[bot]'

The observer needs only a GitHub token with Actions READ access,
supplied in GH_TOKEN or GITHUB_TOKEN. Do not put the publisher key or
publisher installation token in the observer environment.

The actor argument must be corroborated by the real App token's
authenticated identity and GitHub run details; its spelling alone
does not prove attribution. A branch-deletion push may be associated
with current default main, not the deleted ref, so the comparator also
flags new runs by the independently confirmed publisher actor or the
frozen target SHA. Ordinary unrelated main traffic is counted but
does not automatically become a publisher-fanout claim.

An observed candidate run demands immediate POTENTIAL_FANOUT_STOP_REVIEW,
even before the window ends or during the fifteen-minute observation lag.
The lag qualifies only an **absence** of candidates: an early empty
census returns INCOMPLETE_OBSERVATION_RECHECK. This conservative
inspection interval is NOT a GitHub delivery-time guarantee.
A later comparison that finds no candidate runs still reports
NO_CANDIDATE_RUNS_REVIEW_REQUIRED, with quarantine_certified=false.
Every candidate result is a STOP for independent investigation.
Imported before/after artifacts are checked against the same curated
record/volume limits as freshly collected runs; retained run IDs must keep
the same identity metadata, although status/conclusion may evolve.
This validation does not establish custody or authenticate local files.

Complete evidence requires original probe run ID, authenticated App
principal, time-bounded before/after workflow-run IDs, observed events,
current-default and frozen tree receipts, canary ref create/readback/
delete/absence proof, cleanup/recovery logs, and actual token
revocation. Store sanitized receipts under #1839.

## Review boundary and next action

The read-only observer was accepted and merged as #1961. The later
dormant implementation adds publisher CREATE/DELETE code and recovery,
but it remains source-disabled and cannot commission W3.

After Astra accepts the distinct dormant implementation and all CI is
green, a separate nonce-specific activation review and owner authorization
are still necessary before any live publisher-App canary.
Independent event-census, cleanup and token-revocation evidence must be
reviewed before W3 push_ci_quarantine_verified can be set. The observer
and the canary controller never set it themselves.
