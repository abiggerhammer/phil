# W3 executable protected-ref denials — dormant source-only implementation

Tracking: [worker boundary #1863](https://github.com/abiggerhammer/phil/issues/1863), [immutable admission #1839](https://github.com/abiggerhammer/phil/issues/1839), [G1/G2 CI #1935](https://github.com/abiggerhammer/phil/issues/1935). Builds on accepted and merged [read-only W3 plan #1944](https://github.com/abiggerhammer/phil/pull/1944). **This PR must NOT activate W3 or mint either App's token.**

## Exactly what this slice implements

A new manually triggered, main-only, owner-only workflow `.github/workflows/mhb-atc-w3-ref-commissioning.yml` and strict state machine `scripts/mhb_atc_w3_ref_trial.py`. Its only future writes are operations on three disposable single-component branches covered by the admitted-ref ruleset #27365284:

- `hamster/admitted/w3-<nonce>-canary` — publisher App 5782193 creates the canary at the trusted first parent commit, verifies its SHA, deletes it and verifies absence. **No worker test begins until the publisher has proven it can perform the exact cleanup operation.**
- `hamster/admitted/w3-<nonce>-seed` — the publisher creates an exact disposable seed at that same first-parent SHA. Worker App 5836223 attempts a valid fast-forward UPDATE to trusted main, a FORCE-UPDATE toward the second ancestor, and DELETE. Each should be denied by the active ruleset, then immediately read back unchanged.
- `hamster/admitted/w3-<nonce>-create` — absent at preflight. The worker App attempts one valid CREATE at the trusted main SHA, expecting explicit repository-rules denial; it must remain absent. 

These four negative requests run **sequentially**, never in parallel. Every attempt is preceded by checking current main, live ruleset version/conditions, a complete admitted-namespace prefix snapshot, exact seed SHA and absence of the other disposable refs. Every denial must be explicit in the **status and response body**, mention repository rules **and the exact disposable ref**. A bare HTTP 422 or a generic access error does not count. Any 2xx, ambiguous error, unexpected ref motion or live state drift stops all subsequent worker attempts.

## Credential boundaries and recovery

Workflow jobs have **separate protected environments**: `atc-publisher` for canary/seed and cleanup; `atc-worker-broker` for worker denials. The key and minted token of one App are never supplied to the other job, any worker container, candidate source, artifact or URL. Both tokens are Phil-only and request only Contents write; the token's action-returned App slug and installation ID are checked and `GET /installation/repositories` must show exactly Phil before any attempted write. This is still a narrowly authorized test, not delegation to a hamster.

The `publisher_cleanup` job uses `always()` after any attempted seed job and either worker outcome. It reads only the three exact disposable names and can delete a ref **only** when its current SHA is one of the known, tested trusted commits. Other refs, arbitrary hashes, different nonce, main or source branches are never cleanup targets. It verifies absence after each deletion. An unexpected PR does not occur in this slice. On a failed cleanup or an unknown ref SHA: **STOP for operator and independently approved publisher recovery**; never use a maintainer PAT to work around the ruleset.

Cleanup cannot be made perfectly atomic using GitHub's ordinary DELETE ref API. The test relies on the ruleset's exclusive publisher bypass plus a cross-ATC concurrency group and repeated exact ref reads, and does not claim protection against arbitrary external publisher writes. A cleanup job can fail to start due to platform outage or environment gating; **do not run a trial without an independent publisher recovery procedure.**

## Multiple independent activation gates (currently all OFF)

- **Source policy** `.github/atc-w3-ref-trial.json` has `live_authorized: false` and `approved_nonce: null`. A future independently reviewed PR must set `live_authorized: true` and pin **one exact fresh 12-hex nonce**; this PR does not.
- Repository variable `MHB_ATC_W3_REF_TRIAL_ENABLED` must be exactly `true` only for the separately authorized attempt. It is currently assumed absent/OFF; the workflow will refuse actual execution if absent. A source policy merge by itself does not enable it.
- The operator must manually dispatch the new workflow from **`main` as `abiggerhammer`**, choose `run`, supply that exact nonce and type `AUTHORIZE_W3_PROTECTED_REFS_ONLY`. `plan` uses `PLAN_ONLY` and performs only GET operations with the default read token.
- The source runner revalidates all activation switches and dormant worker/broker/lane policy before writes. It runs from the exact dispatch SHA, makes a local `main` from that SHA, checks clean source and remote main, and refuses to continue on a SHA or ruleset mismatch.

A valid nonce alone is **not a historical reservation**. Future review of a live activation must establish separately that it has never been used or proposed before (including deleted refs). A second dispatch for the same nonce is explicitly **not authorized** even if the refs were cleaned up. Turn off the runtime variable immediately after the bounded live run, retain the issue ledger and post-action token revocations. The initial seed/canary push may trigger GitHub Actions; inspect trigger inventory and resulting runs before authorizing execution.

**No PR CREATE or REOPEN operations belong to this slice**. These need different valid disposable PR setup, explicit CI-fanout containment and preauthorized closure. A 422 on an invalid PR head would not establish authorization denial.

## What tests establish

The new `scripts/test_mhb_atc_w3_ref_trial.py` drives a fake in-memory GitHub API. It covers publisher canary create/delete before the seed, four correctly formed serial worker negative requests, denial classification, ref readback, changed-main and ruleset version, wrong SHA cleanup, no foreign ref deletion and source/run activation staying OFF. CI's ATC radar replay **never calls the live trial**. No App token, live GitHub mutation or privileged environment appears in that CI job.

## Remaining gates

After this exact-head source PR passes CI and Astra's independent security review, there must still be a **separate explicit activation/nonce review and authorized live W3 run** with successful cleanup and token revocation evidence. Next come **worker-App direct PR CREATE/REOPEN denied requests**, an actual worker-App staged push/G1 isolation check, publisher immutable admitted PR/single-slot/recovery commissioning, then a bounded Phase 2 pilot. Nothing here enables the broker or admits a worker proposal.
