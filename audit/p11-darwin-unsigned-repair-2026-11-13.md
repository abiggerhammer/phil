# P11 unsigned Phil Darwin package contract repair — November 13, 2026

Status: **AUTHORIZED FOR ONE ENGINEERING PR, NOT CERTIFIED OR PUBLISHED.**

Controlling decision: https://github.com/abiggerhammer/phil/issues/1736#issuecomment-6849730565.
This change is a narrow new repair; it does **not** move or replace rejected
review checkpoint `13808408f9de0f67cefd6fa744f87d81a2d22fbb`,
its tree `1e5847a146401e5d36ac4250a868e284ff4640fd`,
or the byte/delta evidence in
[audit/p11-provisional-candidate-handoff-2026-11-12.md](p11-provisional-candidate-handoff-2026-11-12.md).
The old Phil Darwin archive remains smoke-REJECTED; old bytes are not to be
re-signed, overwritten, or retroactively accepted.

## Scoped correction

`scripts/release/build-phil-phase1-darwin-package.sh` now installs
`share/phil/phase1-handoff-manifest-v1.tsv`, invokes the preexisting
`Phase1INT011DistributionReleaseMain.hs emit-darwin` with the **actual
unsigned shipped** `bin/philc`, and emits
`share/phil/phil.release-package`. Its `BUILD-INFO` records the exact
release identity, source head, target, compiler and handoff SHA-256.
`TCB.txt` copies the four machine-record trust roots verbatim, avoiding
a second inconsistent handwritten disclosure. A `.release` sidecar is
computed from the completed ZIP and its included `SHA256SUMS`; sidecar and
archive SHA-256 files are generated separately.

The binary remains **UNSIGNED**. A valid distribution manifest proves byte
association **within this unsigned staging record**, not a Developer-ID
signature, notarization, authenticated P7 source occurrence → actual public
executable derivation, external auditor approval, or final Phase 1 freeze.
The signed/notarized builder is not modified.

## Fail-closed native CI

The new unprivileged
`.github/workflows/phase1-p11-darwin-unsigned-repair.yml` has separate
native x86-64 Linux and Apple Silicon macOS jobs. They build the source from
the **actual PR head**, exercise both Phil and Steve builders, check exact
archive/sidecar hashes, independently unpack the archives and execute the
existing full `smoke-test.sh` programs, then capture source/head, build
toolchain, SHA-256 receipts and smoke logs as temporary Actions artifacts.
The Darwin job also checks the internal/archive release identity and the
fail-closed negative where the handoff manifest is altered after extraction.
The jobs use `contents: read` and have no signing/notary/release credentials
or public-release publishing action.

A workflow's green result is evidence of tested **unsigned staging** only.
No `P11_CHECKPOINT_REVIEW=PASS` or final source/tag/asset pin may be inferred
without review of actual complete receipt hashes. Recompute both historical
source-to-candidate deltas, including the unsigned builder change, before
asking an external auditor to countersign. Preserve original 244 normative
conformance cases, TCB and separate P8–P10 obligations.

## Exit gate

- [ ] PR exact HEAD smoke/build/check workflow fully successful (all platform jobs)
- [ ] Fresh unsigned Phil Linux, Steve Linux, Phil Darwin and Steve Darwin hashes recorded
- [ ] Phil Darwin extracted full native smoke and tamper-negative both executed
- [ ] Protected merge intent successful with exact head and no overlapping main changes
- [ ] One-PR budget consumed; automation paused for review
- [ ] New *provisional source review* checkpoint nominated separately, if warranted
- [ ] External independent signed/notarized candidate, public-byte download and review still pending

**`FinalArtifactCertified`: UNPROVED. Independent Phase 1 freeze: NOT YET.**
