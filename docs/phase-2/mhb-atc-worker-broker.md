# MHB-ATC W2: trusted fork-to-staged worker broker (source-only first gate)

Parent: [worker W1–W3 #1863](https://github.com/abiggerhammer/phil/issues/1863), [admission controller #1602](https://github.com/abiggerhammer/phil/issues/1602). This W2 PR **does not enable worker publication or install an unattended trigger**.

## Why the workers use separate source forks

The single shared `phil-atc-worker` App has repository-wide Contents write. Seven installation tokens would **not** be seven separate lane-scoped GitHub principals. Giving those tokens to hamsters would permit cross-lane staged writes wherever branch rules allow. The W2 design therefore keeps both the private key and every minted worker App token inside a trusted-main staging broker; workers only prepare *data* in public forks of `abiggerhammer/phil`.

This first implementation is **operator-mediated**: the authenticated maintainer `abiggerhammer` manually requests a proposed commit from a source fork registered in trusted main. The source fork is per lane; GitHub's actual fork and owner numeric IDs are pinned in source policy and checked against GitHub metadata, together with the parent identity. The fork owner is responsible for who may push to that fork. In particular, using one shared writable fork for all seven hamsters would defeat the intended isolation. Later unattended intake needs its **own authenticated lane request channel**; `repository_dispatch` input, a worker-provided lane string, and a shared bot login do not provide that authority by themselves.

## State at source merge — all OFF

- `.github/atc-worker-lanes.json` registers **only** `phase2-selfhost` and `phase2-embedded`, with `enabled: false` and no source fork. The remaining planned lanes are deliberately not invented.
- `.github/atc-worker-policy.json` remains `broker_activation: disabled` (W1 source pin).
- The new repo variable `MHB_ATC_WORKER_BROKER_ENABLED` is **absent/off**. Do not set it as part of source merge.
- `MHB_ATC_AUTO_ADMIT_ENABLED`, `MHB_ATC_IMMUTABLE_HEADS_ENABLED`, and `MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED` remain OFF.
- The existing [draft A2 stage bridge #1838](https://github.com/abiggerhammer/phil/pull/1838) remains inert. The old Phase 1 auto-PR workflow remains unchanged.
- No private key is in any checked-in file. The existing environment `atc-worker-broker` is intended to permit **only** `main` and contains `MHB_ATC_WORKER_APP_PRIVATE_KEY`, not any worker-controlled workflow.

## Request and source contract

The new `mhb-atc-worker-broker.yml` accepts only a main-branch `workflow_dispatch` initiated by GitHub-authenticated actor `abiggerhammer`. Its inputs are:

| Input | Meaning |
| --- | --- |
| `mode` | `plan` (default, no credential or writes), or separately gated `publish` |
| `lane` | An enabled trusted-source registry lane |
| `candidate` | Fresh, simple, one-segment slug |
| `base_sha` | Exact lowercase Git SHA ancestor of both source candidate and current main |
| `head_sha` | Exact lowercase Git SHA currently at the registered fork's proposed ref |

The only accepted proposal ref is `hamster/proposed/<lane>/<candidate>` in the **registered public Phil fork**, and the only staged target is `hamster/staged/<lane>/<candidate>` in Phil. Source repo is not supplied by dispatch input. It comes from the reviewed registry and is checked through GitHub's pinned repository `id`, `full_name`, `fork=true`, `private=false`, `parent.full_name=abiggerhammer/phil`, and pinned owner login/id. A deleted/recreated fork or renamed/replaced owner cannot silently inherit the lane. The live exact source branch must point to a commit of the requested SHA.

The broker checks out the exact trusted **dispatch SHA**, not a floating later main. It refuses to proceed if main has advanced; no hidden rebase. It reads the matching staged namespace and the open issue census, refusing a second staged candidate or an existing staged branch in the same lane, while allowing at most one already-admitted/admitting candidate as the active predecessor. Ambiguous or unowned issue states fail closed. The stage target is **create-only**, never updated or force-written. The main-ancestor and source-ancestor checks are performed in a temporary **bare** Git repository; proposed content is never checked out or executed. A candidate may have up to 100 nonmerge commits and up to 1000 changed paths. The diff is computed with renames disabled so a deletion disguised as a rename cannot skip the path guard. No proposal may modify `.github/**`, `.gitattributes`, `.gitmodules`, or `scripts/mhb_atc*`; path validation reads NUL-delimited Git diff output, not newline-delimited names. A second matching raw diff check rejects symlinks, submodule gitlinks, unexpected mode changes and disagreement between changed-path sets.

## Mode behavior

**Plan:** Reads public fork metadata, live source ref, existing stage refs and issue state, and fetches Git objects into a bare repo. Validates exact SHA and ancestry. **Does not mint an App token, modify Phil, create an issue or PR, or dispatch anything.**

**Publish:** Requires *all* of the following:
1. Authenticated maintainer dispatch from `main`.
2. Explicitly enabled and source-reviewed fork mapping for the selected lane.
3. Reviewed W1 source policy changed to `broker_activation: enabled`.
4. Separate repo variable `MHB_ATC_WORKER_BROKER_ENABLED=true`.
5. Other ATC activation switches OFF during this bounded first pilot.
6. All pure, fork-metadata, SHA, Git-ancestry, changed-path and stage/issue checks successful.

Only after those gates does the trusted environment mint a Phil-only Contents-write worker App token. Before any write, it checks the authenticated App slug, positive installation ID, pinned configured numeric App ID, and the actual minted token's `GET /installation/repositories` result (exactly Phil). The configured numeric ID comparison is **not** yet authenticated numeric App-ID evidence; W1-ID must be resolved before production broker use. The token stays inside the workflow, never in a remote URL, git config, proposed fork, worker process or artifact. A static Git askpass helper supplies it **only** to `git push`. `git push --force-with-lease=refs/heads/<staged>:` means the destination ref must not already exist; any race fails closed. The broker validates the created exact staged ref, then uses its held App token to send the existing `mhb-atc-stage` repository_dispatch, triggering a **trusted main** workflow that creates the durable ATC candidate issue. The broker **never creates a PR or an admitted ref**.

The `mhb-atc-stage` handler currently runs asynchronously after the dispatch. The broker's successful dispatch is **not** evidence that an issue exists: commissioning must separately verify the issue/receipt. If ref push succeeds but dispatch or issue creation fails, the new staged ref is an orphan and blocks subsequent automatic plans. Investigate/reconcile it; never silently delete it, reuse its name, or force-push a second candidate.

## Tests and remaining gates

`scripts/mhb_atc_worker_broker.py` contains pure policy and snapshot validation, tested by `scripts/test_mhb_atc_worker_broker.py`. The ATC replay workflow runs the new tests on PR and main changes. These tests cover bad actors, forged lane/source refs, unsafe slugs, wrong fork parent/owner, stale HEAD, malformed snapshots, existing stage refs/issues, denied trust-path changes, and disabled-by-default source configuration.

**Review still required before any live publish:** source-vs-runtime isolation, Git object import and Git push options, full matching-ref and issue census under GitHub REST, precise staging issue recovery, token action permissions and cleanup, W1-ID authenticated numeric App identity binding, underlying App installation/permission settings, actual Actions environment main-only restrictions, and fork owner permissions. Do not treat a green plan as proof of GitHub protected-ref or direct PR denial. Those belong to W3.

**Controlled one-lane progression:** choose an actual public fork and isolated owner, pin both GitHub numeric IDs, register **one** lane in an independently reviewed source change, run a main-only `mode=plan` against its exact head, review its plan, deliberately authorize and gate one create-only publication, verify durable issue registration, then run the separate W3 denial tests and immutable publisher trial. Only after the pilot should unattended intake or additional lanes be enabled.

This source PR does **not** mutate GitHub settings, grant new permission, dispatch a broker run, publish a staged ref, delegate credentials, or authorize any worker.
