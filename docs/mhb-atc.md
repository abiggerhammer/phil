# Mecha Hamster Ball — Air Traffic Control (MHB-ATC)

Status: **shadow / read-only**. This phase measures traffic and exercises a
deterministic admission policy. It does **not** gate real PRs, allocate live
leases, or merge code.

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

The dispatcher is serialized with a global GitHub Actions concurrency group
using queue:max and cancel-in-progress:false, to avoid overwriting an earlier
pending stage request. It uses the workflow's scoped GitHub token to write
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
It does not merge anything. An unfinished or already admitted issue blocks
all later admissions; manual closeout is required until a separate completion
controller is implemented. Failed or interrupted partial admissions cannot
silently open another PR: a staged-branch PR counts as occupying capacity
even without its final labels.

**Not yet automatic**: no schedule, no automatic hamster integration, and no
merge/release controller. The existing three Phase 1 lane auto-PR workflows
continue unchanged. Admission fairness is FIFO by trusted issue creation time
and issue number. A manual out-of-band creation of staged PRs is not prevented
by GitHub permissions; it is detected and blocks the next ATC admission.
Commissioning requires a controlled end-to-end staging test and checks that
creating a PR with HAMSTER_PR_TOKEN correctly triggers mandatory CI.

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
