# MHB-ATC opt-in scheduled admission (A1)

**Status:** implementation proposed in PR for [A1 #1835](https://github.com/abiggerhammer/phil/issues/1835). NOT enabled by this documentation or PR. Controlled live commissioning is [#1834](https://github.com/abiggerhammer/phil/issues/1834).

## Contract

The existing trusted `.github/workflows/mhb-atc-admit.yml` retains manual `workflow_dispatch` with a **dry-run** default and explicit `admit-one` option. The A1 change adds a low-frequency schedule at minutes 7, 22, 37, and 52 each hour. A scheduled job runs only when repository Actions variable `MHB_ATC_AUTO_ADMIT_ENABLED` is the exact string `true`. **Unset (default), empty, `false`, or any other value skips admission.** The PR does not set this variable, and does not enable unattended operation.

Both manual and scheduled invocations use exactly the existing one-slot FIFO admission controller, the same serialized `mhb-atc-admission-global` concurrency queue, fail-closed exact-head revalidation, durable `atc: admitting` reservation, nonrecursive real PR-CI credential, and existing reconciliation. An empty queue or occupied slot returns `hold`; an unexpected API failure must not become permission to open another PR. This is not a PR merge workflow.

## Activation gate

**Do not enable until all are true:**

1. [#1834](https://github.com/abiggerhammer/phil/issues/1834) two-candidate **live** hold/release, duplicate dispatch, interrupted admission and stale-head tests have passed and recorded run IDs.
2. Manual dry-run works on the merged main branch; the scheduled job has been observed **skipped** with the repository variable unset.
3. Protected verification and the exact-head merge-intent guard remain independently enforced. Staged workers do not bypass the admission gate.
4. Maintainer explicitly authorizes the switch.

To enable after those gates, set the repository Actions variable `MHB_ATC_AUTO_ADMIT_ENABLED=true` in GitHub Actions repository variables. To **disable immediately**, unset it or set it to `false`. Existing manually invoked dry-run and admit-one remain usable; already-open PRs do not close automatically because the pump is disabled.

A scheduled workflow is not a hard real-time guarantee: if GitHub delays or skips a scheduled run, the next run revisits the durable queue. Never rely on its cadence for safety or correctness. The variable only controls the *pump*, not the independent close-event/30-minute reconciliation workflow. Capacity remains **one**.

## Observation and evidence

For the first enabled cycle, inspect the job summary and record: selected staged issue, exact registered SHA, live SHA, new PR identity, usual PR-triggered required checks, issue label transitions, and no second admission while the PR is open. If any evidence conflicts, disable the variable, close only clearly identified experimental PRs without merging, and investigate.

The scope of A1 excludes Phase 1 hamster migration, Phase 2 worker branch integration (A2), verification-manifest policy, check fanout reduction, or increasing capacity.
