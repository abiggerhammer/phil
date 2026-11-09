# FSEM claim-release recovery after Actions startup failures

> Infrastructure safety procedure; no formal-semantics authority changes.
> Controller: [`scripts/fsem_claim.py`](../../scripts/fsem_claim.py).
> Dedicated recovery workflow: [`fsem-claim-recovery.yml`](../../.github/workflows/fsem-claim-recovery.yml).
> Tracking issue: [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## Incident: FSEM-02 #1707

On 2026-11-09, protected PR [#1707](https://github.com/abiggerhammer/phil/pull/1707)
merged at `27e63cc663fb1cc8a501b6b9411e6bcf739e18d5`
after its exact-head checks and post-ready claim guard passed. The normal
[`pull_request_target: closed` release run #42662805521](https://github.com/abiggerhammer/phil/actions/runs/42662805521)
finished with GitHub conclusion `startup_failure`, **without creating a job**.
The trusted `scripts/fsem_claim.py release` controller therefore never ran.
The original `fsem-02` ref remained at
`fe134069b108ec07770d0eab6a8a801701cd47d2`. Nearby executions
of the same workflow succeeded; the available run record does not prove
a repository-code cause of that scheduler/startup failure.

This exposed a single-event dependency, not an ownership-check failure:
the unique claim ref intentionally prevented any new FSEM-02 claim, but
there was no independent retry path for a lost release event.

## Independent recovery

The default-branch **FSEM Slice Claim Recovery** workflow is separate from
the original `pull_request_target` workflow. It runs on:

- `workflow_run: completed` for **unsuccessful** normal claim-release runs;
- a periodic `schedule` (17 and 47 minutes past each hour) if the
  failed-run notification itself is lost;
- optional `workflow_dispatch` for audited manual recovery.

A `workflow_run` has a privileged token; the recovery job **never checks out
or executes the triggering PR's head**. It checks out the default branch
and runs offline controller tests before any reconciliation.

In automatic `reconcile`, the controller reads each *live exact* FSEM
claim ref and immutable `.fsem-claim.json` record, then requires **one and
only one** closed **merged** same-repository formal-semantics PR on the
claimed source branch, opened after that claim, with the exact
`FSEM-Slice: fsem-XX` marker and lane label. The normal release
checker **re-fetches** the closed PR, confirms the original claim SHA,
checks the unique issue #1613 claim comment and absence of competing
open same-family or ambiguous PRs, and verifies the ref hasn't moved
before deleting it. Unmerged/abandoned claims, active PRs and ambiguous
matches remain locked; they require review, never automatic inference.

GitHub's REST delete-ref endpoint does not support an expected-SHA CAS
argument; the second ref read is a safety preflight, not a claim of an
atomic conditional delete. Out-of-band ref mutation remains forbidden
by the coordination protocol.

## Manual fallback / incident response

On the repository **Actions** tab, choose **FSEM Slice Claim Recovery**
and **Run workflow** on the default branch. To reconcile all live families
using the strict automated checks, leave both inputs blank. To recover
one independently audited merged PR, supply **both** its PR number and
the exact 40-hex *claim commit* SHA. For this incident, the pair is:

- PR: `1707`
- expected claim SHA: `fe134069b108ec07770d0eab6a8a801701cd47d2`

The exact SHA is the *claim ref's* SHA, **not** the PR head or squash
commit. Missing/mismatched inputs fail closed. Never delete, move,
or re-acquire the claim ref by hand to work around a failed event.

After a successful recovery, inspect the workflow run and
[`#1613`](https://github.com/abiggerhammer/phil/issues/1613)
for the trusted `<!-- FSEM-SLICE-RELEASE-V1 -->` audit comment, then
confirm the old claim ref is absent. Only then may the FSEM-02 hamster
acquire a fresh claim for its next bounded slice. FSEM-02 itself remains
an **open, non-normative** proof/implementation obligation.

## Limits

This prevents a single failed close-event workflow from creating a
permanent unmonitored lock. It does **not** guarantee GitHub Actions
scheduling, claim an unobservable `startup_failure` root cause, or
promote any FSEM proof. If *all* Actions scheduling is unavailable, the
manual workflow cannot run until scheduling recovers; the untouched
claim remains safely locked.
