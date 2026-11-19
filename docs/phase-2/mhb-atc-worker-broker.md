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

The broker checks out the exact trusted **dispatch SHA**, not a floating later main. It refuses to proceed if main has advanced; no hidden rebase. It reads the matching staged namespace and a **fully paginated all-state issue history** (open and closed), rejecting any historical reuse of the exact candidate branch whether the original issue is open, admitted, or closed. The existing admission/reconciliation canonical candidate classifier validates each open controller issue's creator, body record, exact branch/SHA, title, issue kind, lifecycle labels and lane labels. No candidate can escape the WIP census merely by changing an issue title. It rejects a second staged candidate or an existing staged branch in the same lane, while allowing at most one separately named already-admitted/admitting candidate as active predecessor. Ambiguous or unowned issue states fail closed. The stage target is **create-only**, never updated or force-written. The main-ancestor and source-ancestor checks are performed in a temporary **bare** Git repository; proposed content is never checked out or executed. A candidate may have up to 100 nonmerge commits and up to 1000 changed paths. The diff is computed with renames disabled so a deletion disguised as a rename cannot skip the path guard. No proposal may modify `.github/**`, `.gitattributes`, `.gitmodules`, or `scripts/mhb_atc*`; path validation reads NUL-delimited Git diff output, not newline-delimited names. A second matching raw diff check rejects symlinks, submodule gitlinks, unexpected mode changes and disagreement between changed-path sets.

## Complete-history ingestion and bounded denial

Both pre-token and pre-write censuses use the full, paginated `state=all` GitHub issue/PR endpoint. The workflow compacts the joined JSON pages with `jq -sc 'add // []'`, retaining every issue and PR record. The broker applies an explicit **32 MiB** limit **only** to this complete issue-history input; all other JSON metadata retains its independent **8,000,000-byte** limit. The reader consumes at most one byte beyond each limit, then denies oversized input. No page count, historical identity check, canonical field or lifecycle validation is relaxed. If the history grows beyond 32 MiB, the broker stops rather than ignoring old records.

The shell uses `set -euo pipefail`: a later GitHub page failure or `jq` parse error aborts before the plan, so a successfully serialized prefix is never treated as a complete census. Offline regression tests feed the workflow's actual acquisition command a roughly 14 MB, 1,935-record, 20-page synthetic history and exercise the plan CLI, a reused name on the last page, malformed later pages and failed later-page retrieval. These are **synthetic local data tests**, not live broker dispatch, fork transport, App authority or credential evidence.

## Mode behavior

**Plan:** Reads public fork metadata, live source ref, existing stage refs and issue state, and fetches Git objects into a bare repo. Validates exact SHA and ancestry. **Does not mint an App token, modify Phil, create an issue or PR, or dispatch anything.**

**Publish:** Requires *all* of the following:
1. Authenticated maintainer dispatch from `main`.
2. Explicitly enabled and source-reviewed fork mapping for the selected lane.
3. Reviewed W1 source policy changed to `broker_activation: enabled`.
4. Separate repo variable `MHB_ATC_WORKER_BROKER_ENABLED=true`.
5. Other ATC activation switches OFF during this bounded first pilot.
6. All pure, fork-metadata, SHA, Git-ancestry, changed-path and stage/issue checks successful.

Only after those gates does the trusted environment mint a Phil-only Contents-write worker App token. Before any write, it checks the authenticated App slug **directly against the source-pinned slug** (and also the configured variable), positive installation ID, pinned configured numeric App ID, and the actual minted token's `GET /installation/repositories` result (exactly Phil). The configured numeric ID comparison is **not** yet authenticated numeric App-ID evidence; W1-ID must be resolved before production broker use. The token stays inside the workflow, never in a remote URL, git config, proposed fork, worker process or artifact. A static Git askpass helper supplies it **only** to `git push`. The empty `--force-with-lease=refs/heads/<staged>:` prevents overwriting a different-SHA ref, **but does not prove creation**: Git may report an existing same-SHA ref as up to date with exit status zero. The broker captures the porcelain response and requires a single explicit `* ... [new branch]` record with the reviewed SHA and exact destination, refusing any up-to-date/updated/ambiguous output **before** dispatch. It then verifies the created exact staged ref and uses its held App token to send the existing `mhb-atc-stage` repository_dispatch, triggering a **trusted main** workflow that creates the durable ATC candidate issue. The broker **never creates a PR or an admitted ref**.

The `mhb-atc-stage` handler currently runs asynchronously after the dispatch. The broker's successful dispatch is **not** evidence that an issue exists: commissioning must separately verify the issue/receipt. If ref push succeeds but dispatch or issue creation fails, the new staged ref is an orphan and blocks subsequent automatic plans. Investigate/reconcile it; never silently delete it, reuse its name, or force-push a second candidate.


## G1 staged-ref push isolation: source defenses, no live publication

A Contents-write GitHub App push to `hamster/staged/<lane>/<candidate>` normally triggers GitHub Actions `push` workflows defined **in the candidate's own tree**. W2 must not assume that the staged namespace itself is a CI quarantine. The main-branch source audit found four legacy Phase 1 push workflows whose `on.push.paths` restrictions had no branch restrictions. Each now explicitly adds `on.push.branches-ignore: ['hamster/staged/**']`, preserving ordinary main/feature-branch push and pull-request checks:

- `phase1-int-001-source-architecture.yml`
- `phase1-int-001-source-systems.yml`
- `phase1-int-001-witness-e2e.yml`
- `phase1-int-002-manifest-closure.yml`

All other current `.github/workflows` push triggers must either allow only branches whose literal glob prefixes are **provably disjoint** from `hamster/staged/` (including `main`, `scratch/**` or the existing distinct `hamster/proof-audit/**` lane) or explicitly exclude `hamster/staged/**`. The conservative offline `scripts/test_mhb_atc_staged_push_ci.py` checks this **entire source workflow inventory**, rejects unknown/broad overlapping branch patterns and newly introduced unbounded push triggers, and tests the four specific exclusions. The ATC replay is path-triggered on **every** `.github/workflows/**` edit so future workflow additions cannot silently escape that source check.

**Historical-base defense:** merely fixing the current workflow files is insufficient. W2 accepts a candidate whose `base_sha` is an ancestor of `main`; an older base might still contain the original unbounded triggers. Before generating any publication token, the broker's bare-Git preflight requires the `.github/workflows` **tree object ID** to be identical at `base_sha`, the exact candidate `head_sha`, and its checked trusted `main_sha`. The previous ban on candidate changes to `.github/**` remains in place. A candidate may lag main on ordinary source changes but **must refresh its base** if any workflow tree differs, or publication fails closed. The new regression executes the actual shell guard against real local Git histories: current-policy sources pass; a pre-isolation base or altered candidate workflow tree rejects. The broker never checks out or executes candidate code.

This is a **source-only G1 mitigation**, not yet runtime commissioning evidence. It has not demonstrated GitHub's actual branch-trigger behavior or the absence of workflow fanout after a controlled staged push; record a separately authorized, safe negative push probe and inspect Actions runs before the first W2 broker publish. It also does not prove cross-workflow, direct PR, or privileged environment isolation: `repository_dispatch` stage registration uses trusted main and the FSEM `workflow_run` recovery uses trusted base code, but those controllers retain their own boundaries.

## G2 admitted-PR and privileged execution gate remains mandatory

A staged branch later admitted as a PR can still cause ordinary PR-triggered workflows to evaluate worker-modifiable code. In particular the Darwin release workflow can execute candidate-editable release scripts in its `macos-release` environment. Before any admitted worker PR, independently audit all PR workflows, inherited historical workflow definitions, effective Actions token scopes and environment secret/approval restrictions. Do not treat G1 source safeguards as evidence that this G2 trust boundary is closed.

Both G1 live confirmation and G2 containment are tracked in mandatory pre-activation [W2-CI issue #1935](https://github.com/abiggerhammer/phil/issues/1935). Even if this G1 source patch merges, **all W2 publish gates remain OFF until the independent CI and identity commissioning work is accepted**. No broker key, worker App token, staged ref or live worker proposal is used for these static tests.

The path and mode guards describe only the **base-to-tip net diff**: a proposed commit series could temporarily add then remove a prohibited path. Root `.gitattributes` and `.gitmodules` are forbidden, but nested attribute files are not fully excluded by this guard. A stronger per-commit and nested-path policy must be reviewed if needed for the pilot. The source remains unexecuted in the broker itself.

## Tests and remaining gates

`scripts/mhb_atc_worker_broker.py` contains pure policy and snapshot validation, tested by `scripts/test_mhb_atc_worker_broker.py`. The ATC replay workflow runs the new tests on PR and main changes. These tests cover bad actors, forged lane/source refs, unsafe slugs, wrong fork parent/owner, stale HEAD, malformed snapshots, **closed history, retitled and forged active candidates, actual local Git same-SHA/up-to-date transport behavior, changed-App configuration**, existing stage refs/issues, denied trust-path changes, and disabled-by-default source configuration.

**Review still required before any live publish:** source-vs-runtime isolation, Git object import and Git push options, full matching-ref and issue census under GitHub REST, precise staging issue recovery, token action permissions and cleanup, W1-ID authenticated numeric App identity binding, underlying App installation/permission settings, actual Actions environment main-only restrictions, and fork owner permissions. Do not treat a green plan as proof of GitHub protected-ref or direct PR denial. Those belong to W3.

**Controlled one-lane progression:** choose an actual public fork and isolated owner, pin both GitHub numeric IDs, register **one** lane in an independently reviewed source change, run a main-only `mode=plan` against its exact head, review its plan, deliberately authorize and gate one create-only publication, verify durable issue registration, then run the separate W3 denial tests and immutable publisher trial. Only after the pilot should unattended intake or additional lanes be enabled.

This source PR does **not** mutate GitHub settings, grant new permission, dispatch a broker run, publish a staged ref, delegate credentials, or authorize any worker.
