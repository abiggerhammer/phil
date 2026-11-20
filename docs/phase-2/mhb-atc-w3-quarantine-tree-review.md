# W3 workflow-tree quarantine pin — accepted review record

**Status:** source/tree accepted by Astra at #1951 exact head
`ec1941020deb9fff6259dc5bfa275d01f998c15f`; [merged](https://github.com/abiggerhammer/phil/commit/1a14600d0a455435e420ab8e0629172a4b8e351d).
This is **not** live push-fanout evidence, permission to dispatch W3 `run`
or `cleanup`, or authority to mint either GitHub App token.

Tracking: [W3 hardening #1948](https://github.com/abiggerhammer/phil/pull/1948),
[G1/G2 #1935](https://github.com/abiggerhammer/phil/issues/1935),
[worker trust #1863](https://github.com/abiggerhammer/phil/issues/1863),
[commissioning #1839](https://github.com/abiggerhammer/phil/issues/1839).
See also [the dormant W3 trial contract](mhb-atc-w3-executable-ref-trials.md).

## Exact reviewed pin

- Accepted **Git `.github/workflows` subtree**: `6fa265b2b55cef252ffb1e5cf4734df84bbda9fd`.
  This is **not** the repository root tree SHA or a hash of one YAML file.
- Observed in first-parent source commit
  [`69b3c419835f12085dbd41bf6f7d669e24a9828d`](https://github.com/abiggerhammer/phil/commit/69b3c419835f12085dbd41bf6f7d669e24a9828d),
  the #1949 FSEM-02 source-family envelope commit; **622** direct workflow
  blob entries, no truncated Git-tree listing. GitHub object identity can
  be checked by
  `git rev-parse 69b3c419835f12085dbd41bf6f7d669e24a9828d:.github/workflows`
  in an authenticated, clean local checkout.
- The earlier #1948 [Radar Replay run](https://github.com/abiggerhammer/phil/actions/runs/44701661186)
  passed 229 tests across 17 suites for the former 621-file tree.
  This alone was **not** evidence for the later workflow addition.
- Astra accepted the original 621-file #1951 candidate at `e38814a2`,
  then accepted the corrected, exact **622-file** tree and PR head
  `ec1941020deb9fff6259dc5bfa275d01f998c15f`.
  The [corrected-head Radar Replay](https://github.com/abiggerhammer/phil/actions/runs/44710316580)
  and post-ready checks passed before merge. This is static source-level
  acceptance, **not** live publisher-origin push-fanout evidence.

### Historical pre-merge first-parent mismatch

Before #1951 merged, the following three commits W3 would have selected were:

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
disjoint from `hamster/admitted/w3-*`; Astra accepted the updated exact
622-file tree after a focused delta re-review. All pre-existing workflow
blob IDs were identical to the earlier reviewed
`4b8b338a7a0ebed852407c9288d4a293bc26066f` tree.

**Do not enable a protected-ref trial against that historical snapshot.**
At the #1951 merge, source `1a14600d` and first parent `69b3c419` shared
the reviewed tree, but second first-parent ancestor `4b7594ed` did not.
One further first-parent transition with unchanged workflow content was
required as of that merge. Recheck live ancestry at the actual dispatch:
later workflow changes or concurrent merges can invalidate it.

## Independent review criteria and future-change contract

The independent review assessed the actual 622-file Git tree, not just this
description. Any later replacement tree requires a fresh review of:

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

Acceptance of #1951 bound the **exact pin value, workflow-tree content
and the reviewed head** `ec1941020deb9fff6259dc5bfa275d01f998c15f`.
On any later workflow-tree modification, **STOP and repeat independent
review** for a new exact tree; do not treat the old acceptance as portable.

## Read-only owner-state snapshot (2026-11-20)

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

Before *any* later activation, the current `main` and its two successive
first-parent ancestors must have the exact same reviewed `.github/workflows`
subtree. At the #1951 merge, only the newest two matched. A documentation-only
follow-up or other natural source-only merge can complete the first-parent
window; never manufacture unreviewed workflow changes or skip this equality
check. Any intervening workflow edit resets the window and demands a fresh
pin review. On a clean local `main` checkout, after fetching origin:

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

**The merged #1951 PR changed neither workflow files nor W3 execution gates.**
Its accepted pin is necessary but insufficient for a trial. The pin alone
grants no live-run, ref-mutation, token-mint, or cleanup authorization.
