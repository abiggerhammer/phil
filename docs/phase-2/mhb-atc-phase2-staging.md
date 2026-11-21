# MHB-ATC Phase 2 staged-branch bridge (A2)

**Status:** proposed in [A2 #1837](https://github.com/abiggerhammer/phil/issues/1837). The bridge is **disabled by default**. The Phase 1 worker auto-PR workflow is not modified.

## Identity and contract

The only branch families accepted by this bridge are:

- `hamster/staged/phase2-selfhost/<unique-candidate>` — later Phase 2 compiler/self-hosting work;
- `hamster/staged/phase2-embedded/<unique-candidate>` — later Phase 2 ESP32/target work.

Do not re-use a closed candidate's name; assign a fresh slug for every successor. These are intended as immutable *candidates*, not continuously updated mainline branches.

The workflow `.github/workflows/mhb-atc-phase2-stage-bridge.yml` runs on pushes to these exact branches **only if** the repository Actions variable `MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED` equals the literal string `true`. Unset, `false`, or any other value does not stage candidates. The workflow checks out only trusted `main` code, validates the branch identifier and exact live head, and dispatches `mhb-atc-stage` with the exact branch and SHA using the token dedicated to the trusted workflow. GitHub's `GITHUB_TOKEN` can trigger `repository_dispatch`; the stage registry is a second, separately trusted default-branch workflow, and no staged branch content is checked out or executed by the bridge.

The existing trusted stage workflow re-checks the live SHA, creates/updates the durable bot-authored candidate issue and **does not open any PR**. New Phase 2 lanes have an additional checked WIP guard:

- maximum **one** `atc: admitting` / `atc: admitted` candidate plus **one** `atc: staged` successor per lane;
- same-branch staged refresh with a new validated exact SHA retains original FIFO timestamp;
- a second distinct staged candidate is refused, as are ambiguous state/ownership records;
- existing Phase 1 lanes and the special ATC commissioning lane are unchanged by this new WIP limit.

ATC admission is separate: see the existing manual single-slot workflow and optional scheduled pump [A1 #1835](https://github.com/abiggerhammer/phil/issues/1835). Neither stage registration nor the appearance of a PR is merge clearance.

## Required gate before enabling the bridge for unattended workers

**Not yet discharged:** the current admission workflow opens its PR **from the staged branch itself**. Anyone able to push new commits to that branch *after admission* may trigger a fresh PR CI wave without consuming a new ATC slot. The exact-head admission, merge-intent and reconciliation checks must fail closed on SHA drift, but this does not itself eliminate CI resource bypass.

Before setting `MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED=true`, independently review and enforce an immutable admitted-head strategy (for example, checked server-generated admitted ref plus a suitable GitHub write restriction or monitored fail-closed branch policy). Exercise push-after-admission, PR reopen, direct PR creation, duplicate dispatch, and branch ref drift tests; prove no unreserved full CI admission. Do not claim the implementation provides a repository-wide CI gate while manual Phase 1 PRs still exist.

Also require successful [live two-candidate commissioning #1834](https://github.com/abiggerhammer/phil/issues/1834), review of [single-slot pump #1836](https://github.com/abiggerhammer/phil/pull/1836), and explicit maintainer authorization of this switch. Do not activate the bridge or add automated workers simply by merging this PR.

## Rollback

Unset or set `MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED=false`. No new Phase 2 candidate push will dispatch a staging event. Existing staged candidate issues remain durable and must be reconciled/closed separately; the one-slot admission controller is unaffected. Neither this variable nor the A1 pump variable changes any Phase 1 proof/assurance evidence or release authority.

## Evidence needed on first deployment

Record the pushed SHA, bridge Actions run, bot-authored stage issue, original enqueue time, one-active/one-successor decisions, admission exact SHA, actual PR CI wave, final closed-PR reconciliation, and negative tests. No new normative Phase 1 conformance cases or automatic merge authorization is implied.
