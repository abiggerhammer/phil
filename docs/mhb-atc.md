# Mecha Hamster Ball — Air Traffic Control (MHB-ATC)

Status: opt-in staging and manual one-slot admission have passed a controlled
live commissioning test. Automatic release and recovery reconcile reservation
state; **none of these components merges PRs or alters the existing Phase 1
hamster auto-PR lanes**.

## Historical baseline (measured 2026-11-06)

Source: GitHub Actions REST run listing for abiggerhammer/phil, filtered by
UTC creation day (created=YYYY-MM-DD..YYYY-MM-DD).

| UTC date | Workflow runs reported | Note |
| --- | ---: | --- |
| 2026-09-21 | at least 2,500 | date query reached its result ceiling; lower bound |
| 2026-09-30 | 588 | historical comparison |
| 2026-10-05 | 375 | historical comparison |
| 2026-11-05 | 2,327 | heavy recent activity |
| 2026-11-06 | 567 | partial day, around 09:32 UTC |

These counts include push, pull_request and helper workflow events; they are
NOT PR counts, job counts, billed runner minutes, or unique commits. Historical
query counts sometimes exceed the set of runs available through pagination.
Do not extrapolate from the missing pages without an explicit sampling method.

A revision caused approximately 28–35 near-simultaneous workflows in
September/October samples. A sampled main push on November 5 had 56 distinct
workflow names. The main resource concern is fanout per revision.

Samples of individual jobs (created to started; started to completed):

| UTC date / run | Queue wait | Runtime |
| --- | ---: | ---: |
| Sep 21 PR CI, run 35669893424 | 151 s | 670 s |
| Sep 21 PR Proofs / Rocq, run 35669893458 | 401 s | 85 s |
| Sep 30 PR CI, run 36783581835 | 2 s | 590 s |
| Oct 5 PR CI, run 37353089065 | 3 s | 699 s |
| Nov 5 PR Proofs / field projections, run 42133129498 | 323 s | 399 s |
| Nov 5 push CI, run 42081041967 | 499 s | 713 s |
| Nov 6 ATC PR CI, run 42192947291 | 240 s | 547 s |

These are selected examples, not a representative distribution. The results
support contention as a concern but do not isolate GitHub runner limits from
fanout, repo configuration, workflow mix and other upstream factors.

## Read-only radar

The manual-only workflow "MHB ATC Radar (Manual)" samples UTC today and
yesterday, retains a JSON artifact and publishes a workflow summary. It
never runs automatically on push or pull_request.

Historical replay with an authenticated GitHub CLI:

    python3 scripts/mhb_atc.py --repo abiggerhammer/phil \
      --date 2026-09-30 --date 2026-11-05 \
      --max-pages 3 --jobs-per-day 6 --format markdown

Run offline policy and sampler tests:

    python3 scripts/test_mhb_atc.py

Reported daily run totals are distinguished from newest-first sampled runs and
sampled jobs. Sample medians are not population percentiles. For comparisons,
keep the same date window and sampling budget. The sampler fails closed on
malformed responses and partial job pages.

## Shadow admission

The deterministic selector takes an offline JSON snapshot:

    {
      "capacity": 1,
      "admitted": [
        {"state": "verifying",
         "head_sha": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}
      ],
      "candidates": [
        {"branch": "hamster/rocq-refinement/proof-one",
         "head_sha": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
         "enqueued_at": "2026-11-06T09:00:00Z"}
      ]
    }

Invoke:

    python3 scripts/mhb_atc.py --admission-snapshot snapshot.json

It holds when verification capacity is occupied, otherwise recommends the
oldest candidate by UTC enqueue time with deterministic tie-breaking.
Unknown states, invalid SHAs, duplicate branch identities and naive timestamps
fail closed. It neither grants clearance nor contacts GitHub.

## Opt-in durable staging (new, inactive for Phase 1)

A worker can prepare a branch under:

    hamster/staged/<lane>/<candidate-slug>

No existing Phase 1 auto-PR branch pattern matches this namespace. A staged
branch by itself does **not** open a PR or trigger the full PR verification
fanout. The worker submits a trusted repository_dispatch event to the default
branch with event_type 'mhb-atc-stage' and a client_payload consisting of:
- branch: the full staged branch name;
- head_sha: the exact forty-character commit SHA to register.

The workflow in .github/workflows/mhb-atc-stage.yml runs trusted main-branch
code, compares the supplied SHA with the live GitHub branch head, and creates
or updates one open issue titled "ATC candidate: <branch>" with labels
"atc: staged" and "lane: <lane>". The issue's original creation timestamp
is the durable FIFO enqueue time. An update to the same branch preserves
that timestamp, but replaces the recorded exact head SHA. A closed issue
cannot be reopened by reusing its branch name: create a new candidate slug.

A GitHub CLI example, after a staged branch is already pushed:

    branch=hamster/staged/mhb-atc/my-first-candidate
    sha=$(git rev-parse HEAD)
    gh api --method POST repos/abiggerhammer/phil/dispatches \
      -f event_type=mhb-atc-stage \
      -f "client_payload[branch]=$branch" \
      -f "client_payload[head_sha]=$sha"

The dispatcher shares the global MHB-ATC admission concurrency group with
admission and reconciliation, using queue:max and cancel-in-progress:false,
so candidate mutations cannot race each other or discard pending requests. It uses the workflow's scoped GitHub token to write
issues; no untrusted staged branch code is checked out or executed.

**Not admission clearance:** staging does not create a PR, reserve a runner,
or imply that the recorded SHA is current later. A future controller must
re-check branch identity and exact SHA immediately before admitting a
candidate. The issue registry is opt-in and does not automatically scan
hamster branches or change any of the three existing Phase 1 lanes.

Operational limitations to address before live adoption: test repeated
dispatch idempotence against the actual GitHub issue search response,
bound the issue-search result set, add retry/backoff for rate-limit or
transient API failures, define cancellation/supersession behavior, and
ensure a global atomic admission decision across multiple queued issues.

## Manual single-slot admission (opt-in commissioning)

The workflow "MHB ATC Admit One (Manual)" implements the *first*
repository-backed admission decision. Its default **dry-run** mode is
read-only: it fetches the complete GitHub API lists of open issues and open
PRs and reports the oldest eligible staged candidate. At most one candidate
would be admitted while any staged-branch or ATC-admitted PR is open.

Explicitly selecting **admit-one** re-reads the authoritative snapshot,
checks that the choice is unchanged, validates the recorded SHA against the
live GitHub branch, verifies no open PR for that branch exists, and opens a
single pull request with the existing HAMSTER_PR_TOKEN credential (not
GITHUB_TOKEN), so ordinary PR-triggered checks actually run.

A successful admission labels the PR and corresponding issue "atc: admitted".
It does not merge anything. An in-progress (atc: admitting) or already admitted issue blocks
all later admissions. The admission workflow reserves capacity with
atc: admitting **before** creating its PR; the reconciliation controller
closes the candidate after its exact-head PR closes. Failed or interrupted partial admissions cannot
silently open another PR: a staged-branch PR counts as occupying capacity
even without its final labels.

**Not yet automatic**: no schedule, no automatic hamster integration, and no
merge/release controller. The existing three Phase 1 lane auto-PR workflows
continue unchanged. Admission fairness is FIFO by trusted issue creation time
and issue number. A manual out-of-band creation of staged PRs is not prevented
by GitHub permissions; it is detected and blocks the next ATC admission.
Commissioning requires a controlled end-to-end staging test and checks that
creating a PR with HAMSTER_PR_TOKEN correctly triggers mandatory CI.

## Automatic slot release and partial admission recovery

The trusted workflow at .github/workflows/mhb-atc-reconcile.yml reconciles
candidate issues with the lifecycle of their exact authorized PRs. It runs
after a same-repository staged-branch PR is closed and every 30 minutes as
a fallback for missed/delayed close events or interrupted admissions. It can
also be invoked manually in **dry-run** mode (no writes), or explicitly in
reconcile mode.

All stage, admission and reconciliation workflows share the concurrency
group "mhb-atc-admission-global" with queue:max, preventing two controller
operations from modifying the issue state concurrently. Other repository
actors are not prevented from modifying PRs manually; before writing, the
controller re-reads its authoritative snapshot and rejects changed plans.

ATC candidate lifecycle:

    atc: staged -> atc: admitting -> atc: admitted -> issue closed
                      |                  |
                      | no matching PR   | exact-head PR closed
                      | after >=15 min   v
                      +--> atc: staged   slot released

- Closed linked PR (merged or simply closed): close the candidate issue to
  release the verification slot. This does **not** certify its work or grant
  merge authority.
- Open linked PR with incomplete labels or an admitting issue: repair the PR
  labels and promote the issue to admitted.
- Admitting issue with no PR after 15 minutes: return it to staged for a
  future explicit admission attempt, but only after complete PR lookup and
  revalidation while holding the shared controller concurrency group.
- Admitting issue with no PR for less than 15 minutes: leave the capacity
  reserved; do not create another PR.
- Admitted issue with no matching exact-head PR, multiple matching PRs,
  incorrect branch/base/commit, inconsistent labels, malformed machine
  records, or untrusted issue provenance: **fail closed** and require
  investigation. Never infer release or merge success from missing data.

The reconciliation planner is pure and unit-tested using failure/replay
snapshots. Live reconciliation is a separate workflow using only trusted
main-branch code; it has issue and PR metadata write permissions but never
merges anything or checks out the candidate's code.

### Commissioning baseline

The first live test (November 6, 2026) staged one documentation-only
candidate at head 0d643f2fd1ea8923f76bb37b112b448e1075a02c. The
stage job created candidate issue #1608, a dry-run selected it, and explicit
admission opened PR #1609. Fourteen ordinary PR-triggered workflows started;
the test PR was closed **without merging**, and the issue was closed. This
validated staging, selection, CI triggering, and manual closeout, but was
completed before automatic recovery and release were installed. Do not
treat it as an automated recovery commissioning test.

### Limitations before unattended scheduling of admissions

This controller releases slots automatically, but does not automatically
admit the next candidate, and it cannot guarantee when GitHub's scheduled
workflows run. An unexpected or unknown state fails closed. Further
commissioning should exercise a two-candidate scenario (second candidate
held while the first PR remains open, then released by the close event),
a mid-admission crash simulation, and duplicate stage event idempotency.
Keep the admission workflow manually triggered until those are tested.

## Rollout

1. Observe representative queue delays, run costs, cancellations and verified
   merges/hour. Never infer entire-population statistics from newest samples.
2. Stage hamster branch candidates durably before opening a PR. Integrate all
   hamster wakes with a serialized admission controller, not ad hoc gate checks.
3. Admit one CI revision, binding the decision to branch, lane, exact head SHA,
   WIP limits and a durable queue; forbid push or reopened-PR bypasses.
4. Recover from stale heads, retries, timeouts and cancellation without treating
   absent verification as successful verification.
5. Expand to two admitted revisions only if verified merges/hour improve.
6. Deduplicate builds and proof checks only with an explicit required-check
   manifest; retain the existing exact-head verification invariant.

Merge serialization foundation: PR #1601 (merged).
Tracking issue: #1602.
