# PR-head CI supersession — bounded first rollout

> Status: infrastructure safety policy and staged workflow migration. This is a scheduler optimization, not a relaxation of required proofs or conformance checks.

## Motivation

During #1644, repeated repair commits generated 192 obsolete workflow runs that needed manual cancellation. The initial rollout targets the 47 ordinary PR workflows visible in that exact-head CI wave. The repository has 448 workflow files in total; this document does not claim all are covered yet.

## Exact concurrency rule

```yaml
concurrency:
  group: ${{ github.workflow_ref }}-${{ github.event.pull_request.number || github.run_id }}
  cancel-in-progress: ${{ github.event_name == 'pull_request' }}
```

On a pull request, the workflow file identity and PR number form a stable group across updates. Newer runs supersede older queued or running executions of that same workflow/PR. Different PRs and different workflow files remain independent.

On non-PR events, the unique run ID replaces the PR number and cancellation is disabled. That means main-branch pushes, releases and manual runs cannot cancel or serialize each other through this rule. Existing workflows using unconditional cancellation have been corrected for this scope.

## Exclusions

FSEM's `fsem-claim-guard.yml` and `fsem-claim-release.yml` implement the exact-claim protocol and are not changed. MHB admission/staging/radar/reconcile workflows have a global coordination domain whose `cancel-in-progress: false` and serialization must remain intact. Do not replace that domain with a per-PR group.

## Enforcement

The reviewed set of 47 workflows is recorded in [`scripts/ci/pr-concurrency-covered.txt`](../../scripts/ci/pr-concurrency-covered.txt). [`scripts/ci/check_pr_concurrency.py`](../../scripts/ci/check_pr_concurrency.py) requires each to retain the exact PR trigger, group expression and event-gated cancellation. [`scripts/ci/test_pr_concurrency.py`](../../scripts/ci/test_pr_concurrency.py) tests isolation across PRs/workflows and non-PR run IDs, plus common regressions.

The read-only [PR CI Supersession Policy workflow](../../.github/workflows/pr-ci-supersession-policy.yml) runs whenever workflows or its policy files change. To make this policy strictly mandatory, add its `verify-pr-head-supersession` check to the repository required-check ruleset after its first green run.

## Next increments

Other PR workflows outside the inventory retain their current behavior. Migrate additional ordinary workflows in small audited batches, adding each to the inventory. Do not bulk-edit all 448 workflows in a single PR; modifying workflow YAMLs can trigger proof jobs itself.

The text-level offline tests model GitHub expression behavior; an end-to-end scheduling check remains useful: push successive commits to a test PR and confirm that older same-workflow runs cancel while the current-head required check succeeds, and that a `main` run is never cancelled.

After this, examine workflow path filters and shared build caching to reduce the number and duration of independent runs per head. Queue cancellation eliminates obsolete work but does not make necessary CI intrinsically cheaper.
