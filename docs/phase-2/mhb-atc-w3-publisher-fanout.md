# W3 publisher-App fanout: independently reviewed experiment protocol

STATUS: DORMANT SOURCE-ONLY PLAN AND READ-ONLY EVENT OBSERVER.
No App token, protected-ref mutation or workflow activation is authorized
by this document or by the observer.

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

The source-only experiment does not yet include the privileged probe
workflow or independently authenticated recovery logic. Those are
required in a separate dormant implementation PR before any write.

For that future implementation, Astra must review a finite owner/manual
main-only workflow with a separate runtime enable variable, strict
nonce and one-time use reservation, the publisher-only atc-publisher
protected environment, and token generation only after an unprivileged
read-only preflight. Both exact source and runtime gates must be ON
only after separate independent activation approval.

Before CREATE or DELETE, revalidate: trusted dispatch SHA and current
main, default_branch=main, complete current-default semantic workflow
quarantine, the pinned target SHA and frozen target workflow tree,
ruleset ID/version/bypass, a complete empty admitted-ref namespace,
exact absence/readback of the canary, App slug/installation identity
and Phil-only token audience. The potential DELETE must recheck
current-default workflow semantics as independently accepted in #1953.

Commit an fsynced, nonsecret INTENT and bounded actual status/post-state
before each write. A failed/ambiguous CREATE must never be retried
without exact read-only reconciliation; an unexpected existing/foreign
SHA is a STOP. A failed DELETE requires publisher-only recovery, not a
maintainer PAT. A cancellation may prevent cleanup or artifact upload.
The future implementation must provide and test a distinct, always()
cleanup job as well as an independently dispatchable recovery path
bound to the authenticated ORIGINAL run, nonce, exact ref and known
historical SHA before token mint. Do not treat "cleanup scheduled" as
"ref absent". Retain the final ref census and token-revoked evidence.

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
minutes, enumerates every reported page in bounded four-run batches (empirically
within the existing W3 HTTPS client's 64 KiB response limit), refuses
windows with 200 or more runs of any one event type, and rejects count changes,
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

The comparator refuses to treat an observation made less than fifteen
minutes after the end of the selected interval as complete. This is a
conservative inspection interval, NOT a GitHub delivery-time guarantee.
A later comparison that finds no candidate runs still reports
NO_CANDIDATE_RUNS_REVIEW_REQUIRED, with quarantine_certified=false.
Any candidate result is a STOP for independent investigation.

Complete evidence requires original probe run ID, authenticated App
principal, time-bounded before/after workflow-run IDs, observed events,
current-default and frozen tree receipts, canary ref create/readback/
delete/absence proof, cleanup/recovery logs, and actual token
revocation. Store sanitized receipts under #1839.

## Review boundary and next action

This PR adds only a read-only observer, its disabled source contract,
offline hostile tests and CI registration. No privileged workflow or
GitHub mutation path is present in this PR.

After this observer passes CI and independent review, implement the
separate publisher-only probe/cleanup workflow with source OFF, get
Astra's exact-head approval, then separately authorize a one-time
nonce and supervised live run. Only independently justified evidence
from that run may support a later reviewed change to W3's
push_ci_quarantine_verified flag. This observer cannot set it.
