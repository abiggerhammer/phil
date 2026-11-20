# MHB-ATC G2 — no privileged execution of admitted worker PR code

Controlling stop gate: [#1935](https://github.com/abiggerhammer/phil/issues/1935). The G1 staged-push source patch was merged in #1937. A separate source-only live probe used the connected GitHub principal, not the dedicated worker App: a comment-only staged push caused zero Actions runs, while a matching ordinary push caused the four expected INT-001/002 runs. This does not discharge W1-ID, worker App commissioning or privileged PR safety.

## Trust boundary and scope

A protected `hamster/admitted/**` ref is **not trusted source code** merely because the publisher App creates the immutable ref. GitHub's ordinary `pull_request` event can check out candidate code. Tests may run this code with a read-only token, but **never** under a signing/notarization environment, a credential-bearing job, or explicit write-capable Actions/publisher permissions.

G2's first **source-only** patch separates ordinary PR verification from release/signing execution. It does not enable unattended workers, authenticate the actual GitHub App, audit live environment secrets/approval rules, or establish the effective repository default `GITHUB_TOKEN` permissions.

## Three release workflows — separate PR tests from secrets

The source audit found three `pull_request` workflows with `macos-release` signing/notarization secrets:

- `.github/workflows/phase1-int011-darwin-distribution-release.yml`
- `.github/workflows/phase1-int011-github-release.yml`
- `.github/workflows/phase1-steve-github-release.yml`

Their six `darwin-build-submit`/`darwin-poll-assess` jobs now require trusted `refs/heads/main` **and** either a main `push` event or an operator `workflow_dispatch` by `abiggerhammer` (where the workflow offers that event). No `pull_request` event satisfies the job gate. The release `publish` jobs already restrict their Contents-write token to `push` on main; that guard is retained and tested.

PR-triggered, unprivileged Linux build/test jobs remain intact, but the signed/notarized artifact chain is deliberately skipped on PRs because its signing jobs are skipped. This is a deliberate change in what the PR CI establishes: a PR must not claim signed-release verification or signing readiness simply because the workflow is green with skipped jobs. Trusted-main release evidence remains separate.

## INT-007 discovery workflows — avoid Actions-write PR tokens

Seven INT-007 source-discovery workflows carried root `actions: write`. Six used it solely for a manual "cancel superseded runs" job step; the seventh had no such step. All already declared native `concurrency.cancel-in-progress: true`.

This source patch removes `actions: write` from all seven, removes the six redundant cancellation steps, and keeps native concurrency and the existing contents-read PR checks. If PR cancellation behavior must change, review it separately; do not silently restore `actions: write` to a job that checks out candidate code.

## Controllers and source-policy audit

The ATC reconciler is a deliberate exception: `mhb-atc-reconcile.yml` handles only closed admitted-branch PRs and executes **trusted main**, with `persist-credentials: false`. It needs write access to issue/PR metadata; its PR event identity check and checkout boundary remain unchanged.

`scripts/test_mhb_atc_privileged_pr_ci.py` uses the pinned strict YAML loader from the G1 audit and reads the entire `.github/workflows` inventory. For workflows that have a `pull_request` event, it refuses root or job write permissions (except the exact reviewed reconciler and main-only release publisher), refuses unguarded jobs with an environment, disallows unreviewed PR-job secret references, pins all six release signing gates and all seven INT-007 read-only permissions, and mutates the actual inventory to prove that unsafe changes deny. MHB ATC replay runs the audit whenever any workflow file changes.

The source policy is **not a complete proof of actual GitHub authority**. Future workflow aliases, new event mechanisms, repository-default token settings, branch-protection semantics, GH runner behavior, reusable workflows, and GitHub environment deployment-branch/approval rules require independent verification. Particularly, workflows lacking explicit `permissions` still rely on repository settings for their default token scopes; those settings are **not authenticated here**. Do not convert a green source audit into an unqualified claim about every PR's effective runtime token.

## Remaining commissioning and acceptance gates

Keep `broker_activation: disabled`, both W2 lanes disabled/unconfigured, and the pre-existing ATC automation switches OFF. Do not request a worker App token, publish a staged candidate through W2, open an admitted worker PR, or exercise `macos-release` as part of this dormant G2 source patch.

Before real untrusted PR admission, independently obtain effective environment settings and permission evidence, review historical-workflow inheritance (including the W2 main/base/head workflow-tree binding), run harmless *denied* PR/job cases without executing signing code, and record source SHA/run IDs/principal and environment denials. Independent acceptance of this source PR and exact-head CI are prerequisites, not substitutes for the live G2 commissioning gate. W1-ID and W3 remain separately unresolved.
