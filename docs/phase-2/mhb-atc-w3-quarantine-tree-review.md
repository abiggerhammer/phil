# W3 workflow-tree quarantine candidate — independent review packet

**Status:** candidate only; independent exact-head review PENDING. This document
does not establish approval, live push-fanout evidence, permission to dispatch
W3 `run` or `cleanup`, or authority to mint either GitHub App token.

Tracking: [W3 hardening #1948](https://github.com/abiggerhammer/phil/pull/1948),
[G1/G2 #1935](https://github.com/abiggerhammer/phil/issues/1935),
[worker trust #1863](https://github.com/abiggerhammer/phil/issues/1863),
[commissioning #1839](https://github.com/abiggerhammer/phil/issues/1839).
See also [the dormant W3 trial contract](mhb-atc-w3-executable-ref-trials.md).

## Exact candidate

- Candidate **Git `.github/workflows` subtree**: `6fa265b2b55cef252ffb1e5cf4734df84bbda9fd`.
  This is **not** the repository root tree SHA or a hash of one YAML file.
- Observed in first-parent source commit
  [`69b3c419835f12085dbd41bf6f7d669e24a9828d`](https://github.com/abiggerhammer/phil/commit/69b3c419835f12085dbd41bf6f7d669e24a9828d),
  the #1949 FSEM-02 source-family envelope commit; **622** direct workflow
  blob entries, no truncated Git-tree listing. GitHub object identity can
  be checked by
  `git rev-parse 69b3c419835f12085dbd41bf6f7d669e24a9828d:.github/workflows`
  in an authenticated, clean local checkout.
- The previously reviewed #1948 [Radar Replay run](https://github.com/abiggerhammer/phil/actions/runs/44701661186)
  passed 229 tests across 17 suites for the earlier 621-file tree.
  That evidence is **not a review of the new workflow**. A new exact-head
  hosted G1/W3 full-inventory audit and independent delta review are required.
  Static hosted tests do not establish live publisher-origin push isolation.
- Astra's first-run acceptance of previous #1951 head
  `e38814a2e916252a8a7f3dd438943e8f4a21664a` applies to the earlier
  tree `4b8b338a7a0ebed852407c9288d4a293bc26066f` only. This candidate needs **fresh review** before merge.

### Critical current first-parent mismatch

At the source snapshot above, the three commits W3 would select are:

| Position | Commit SHA | `.github/workflows` SHA | Count |
|---|---|---|---:|
| Source / `main` | `69b3c419835f12085dbd41bf6f7d669e24a9828d` | `6fa265b2b55cef252ffb1e5cf4734df84bbda9fd` | 622 |
| First parent | `4b7594ed83648372171a9bb1c34647522c064b22` | `4b8b338a7a0ebed852407c9288d4a293bc26066f` | 621 |
| Second first-parent ancestor | `e1da5dc4bd6b01cffe8f21d9dedf119dfe209059` | `6a66400495eb06e310abc8ff1aab3c7087c68c28` | 621 |

All three Git tree responses were complete (`truncated: false`).
The most recent change (#1949) **added just one workflow**,
`fsem02-paired-source-family-envelope-preflight.yml`; its `push`
selector allowlists only `formal-semantics/fsem02-paired-source-family-envelope`
with file-path filters, its `pull_request` trigger has file-path filters,
and its default token permission is `contents: read`. This appears
disjoint from `hamster/admitted/w3-*`, but must be checked independently
using the exact new 622-workflow tree. All pre-existing workflow blob IDs
are identical to the previously reviewed `4b8b338a7a0ebed852407c9288d4a293bc26066f` tree.

**Do not enable a protected-ref trial against this snapshot.** The existing
`snapshot_tree()` gate in `scripts/mhb_atc_w3_provenance.py` correctly
rejects the unequal ancestry, even with a matching source pin.

## Independently review this exact tree

The reviewer must examine the actual 622-file Git tree (not just this
description), with particular attention to:

1. **All push-trigger selectors**, including scalar/list `on`, quoted keys,
   YAML aliases/duplicates, branches, branches-ignore, path filters and any
   unsupported event grammar. G1's strict `StrictWorkflowLoader` and
   `audit_workflow_inventory` in
   `scripts/test_mhb_atc_staged_push_ci.py` fail closed on unreviewed forms.
2. **Four previously unrestricted workflows.** Their exact
   `branches-ignore` list is
   `['hamster/staged/**', 'hamster/admitted/w3-*']`;
   changes must preserve ordinary main/feature push behavior without
   matching W3 disposable leaves.
3. **All other workflow triggers and credential boundaries.** Confirm no
   source workflows execute on `hamster/admitted/w3-<nonce>-{canary,seed,create}`
   push, including surprising unreviewed branch selectors; inspect
   `workflow_run`, privileged environments and indirect fanout assumptions.
4. **Historical source selection.** A publisher-created ref pointing to a
   *prior* commit can select that prior commit's workflow definitions. All
   source / first-parent / grandparent subtree IDs must equal this exact pin
   at commissioning time, not merely the newest source checkout.
5. **Evidence scope.** The hosted inventory audit and source SHA establish
   static source quarantine only; neither independently validates live GitHub
   event delivery under publisher App 5782193 nor proves a token was revoked.

Review acceptance must be explicit and bind the **exact pin value, workflow
tree content and this candidate PR head**. On any workflow-tree modification
after review, **STOP and repeat review** for a new exact tree; do not
interpret an old acceptance as portable to a changed tree.

## Current read-only owner-state snapshot (2026-11-20)

GitHub API GETs showed ruleset **27365284** active for
`refs/heads/hamster/admitted/*`, with creation, update, deletion and
non-fast-forward restrictions and sole bypass Integration App **5782193**.
A read-only `git/matching-refs/heads/hamster/admitted/` returned **zero refs**.
This is a momentary observation, not reservation of a nonce, proof of a
worker-App denial, or proof of environment/variable configuration. Refresh
the ruleset, exact identities, app installation repository selection,
namespace and `main` in the reviewed preflight before any separate
commissioning authorization.

## Stabilization and operator STOP checks

No padding commits or modification of live policy is required for review.
Before *any* later activation, advance `main` through **two consecutive
first-parent transitions without changing `.github/workflows`** from
the candidate tree (or use a newly reviewed tree and repeat this requirement).
Natural source-only merges are acceptable; any intervening workflow edit
resets the window. On a clean local `main` checkout, after fetching origin:

```bash
set -euo pipefail
test -z "$(git status --porcelain --untracked-files=all)"
pinned="$(python3 -c 'import json; print(json.load(open(".github/atc-w3-ref-trial.json"))["reviewed_quarantine_tree_sha"])')"
test "$pinned" = "6fa265b2b55cef252ffb1e5cf4734df84bbda9fd"
for rev in HEAD HEAD^1 HEAD^1^1; do
  actual="$(git rev-parse --verify "$rev:.github/workflows")"
  printf '%s %s\n' "$rev" "$actual"
  test "$actual" = "$pinned" || { echo 'STOP: historical quarantine mismatch' >&2; exit 1; }
done
python3 scripts/test_mhb_atc_staged_push_ci.py
```

The live W3 `snapshot_tree()` and authenticated independent recovery
verification must perform their **own** checks again; this operator read is
never a substitute. Do not change `main` workflow definitions or the source
pin to bypass a failed comparison. Recovery must use the authenticated
original run binding from #1948, not a new `main` ancestry.

## Explicit separate pre-live obligations

- **Independent source/tree acceptance** and ancestry stabilization as above.
- **Observed actual publisher App push-event fanout** through a separately
  designed, independently approved bounded test before
  `push_ci_quarantine_verified` may become `true`. Do not use a protected
  admitted ref merely to shortcut this prerequisite.
- **Separate activation PR** approving a fresh never-used 12-hex nonce and
  `live_authorized: true` only after all source/preflight conditions;
  runtime variable, protected environments, owner/manual/first-attempt
  dispatch and independent cleanup authority must also be approved.
- **Fresh authenticated read-only preflight**: ruleset and its full bypass
  inventory, installed App repository selection and token identity,
  zero unexpected admitted refs, first-parent links, current main and origin
  binding; stop on drift. Retain rollback/recovery and sanitize all receipts.
- **Supervised W3 serial negative operations**, post-action exact ref census,
  independently verified cleanup and real App-token revocation evidence.
  No worker broker activation or PR CREATE/REOPEN tests in this slice.

**This candidate PR changes neither workflow files nor W3 execution gates.**
The pin, if independently accepted and merged, is necessary but insufficient
for a trial. Its existence does not grant live-run or cleanup authorization.
