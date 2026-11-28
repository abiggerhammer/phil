# G2-1 static candidate CI inventory

G2 remains HOLD. G1 and W3 commissioning remain separately gated. This slice
checks repository source and inert evidence. Production enforcement before
candidate execution requires a separate integration review.

The historical audit and implementation base are both
`89ef6436a68a5d1ac9ac5a3d0223047c567f7ac9`, workflow tree
`2b37e8a8aab547ebbbefe28ef1531f16b8f61137`. The base inventory contains 636
workflow files, 1,079 job definitions and 2,093 job/event definitions.
No intervening workflow additions, removals, renames or blob changes occurred
between those pins. `baseline-definitions.json` records each base identity and
workflow blob; `inventory.json` records the resulting source inventory. The
test reconciles exact row sets and the changed workflow blobs. Within this PR
the only changed workflow blobs belong to the 19 permission repairs and the
offline-test wiring. No workflow, job or event definition was added or removed.

All 19 single-job workflows receive an explicit contents-read map and disable
credential persistence on their single checkout. Their existing build and
test routes read repository contents. The Steve ordinary-source workflow also
fetches the public base branch. Trigger filters and test commands are
preserved. There are zero checkout changes outside those 19 workflows.

The strict eligibility function assumes independently authenticated exact
source selection. It issues no credentials and is unwired to production
admission. The supported candidate subset is explicit. Unsupported events,
expressions, alternate source, reusable workflows, mutable actions, effects
and authority return denials. The legacy PR structural checks remain separate,
including their existing guarded controller and signer checks. They do not
override candidate denial. Inventory denials are reported and retained even
for unchanged legacy paths. The host checkout and read-only fixture are positive
controls for the pure policy. The hosted PR workflows provide evidence for
existing build paths when selected by their original filters.

Matrix expansion records only finite literal scalar axes and explicit
include/exclude handling. Symbolic or unknown forms remain unresolved. Definition
and variant rows do not imply execution. The skipped-job fixture is an exact
field projection of provider job 138492848006, run 45407726056, at the recorded
SHA. It supplies a recorded skipped case for the offline state classifier.
[Recorded job](https://github.com/abiggerhammer/phil/actions/runs/45407726056/job/138492848006)

The 461 uploads and 162 downloads use separately observed v4 tag resolutions.
The policy file captures the action contracts and defaults associated with
those immutable revisions. Source still selects the mutable v4 tag, so actual
job resolution must be established independently. The upload model records
include/exclude paths, hidden-file handling, empty-path behavior, retention,
compression and overwrite. Filesystem match and contents remain unresolved.
The download model records authentication mode, all/exact/glob selection, and
extraction destination/layout. Glob expansion currently models the audited
literal-prefix wildcard. Other glob forms remain unknown. Each candidate edge
includes producer authority and an unresolved marker for expression evaluation,
event/variant eligibility and runtime provenance. Name matches never
authenticate outputs. The Steve bundle has both platform artifact candidates.
W3 publisher create and the current-run arm of cleanup identify prepare step 6;
the historical arm remains unresolved. Provider evidence must establish exact
principal, repository, run, attempt, job, artifact ID and digest.
[Upload action contract](https://github.com/actions/upload-artifact/blob/ea165f8d65b6e75b540449e92b4886f43607fa02/action.yml)
· [Download action contract](https://github.com/actions/download-artifact/blob/d3f86a106a0bac45b974a628896c90dbdf5c8093/action.yml)

Offline regression entry points:

```sh
python3 scripts/test_mhb_atc_g2_policy.py
python3 scripts/test_mhb_atc_privileged_pr_ci.py
python3 scripts/test_mhb_atc_staged_push_ci.py
```
