# P9-F1 checked static source use — producer contract (bounded)

**Authority:** [#1791](https://github.com/abiggerhammer/phil/issues/1791), [#1771 maintainer decision](https://github.com/abiggerhammer/phil/issues/1771#issuecomment-6889258828), and audit #1584. This F1 slice is **not** P9, P10, FinalArtifactCertified, or a Phase 1 release/freeze.

## Distinct immutable static use

`CheckedStaticUse` is a third `AssuranceUse` category, distinct from actual `ErasureUse` and actual `RetainedRuntimeUse`. Its domain-separated, length-delimited digest includes the checked source unit, persistent declaration site/key, K/I, exact span, whole static branch route, event ordinal, original and canonical proposition, checked evidence-use kind and named binder, selected immutable evidence ID(s) and revision. The preexisting erasure/runtime digest representations are unchanged. The manifest ID already commits to every selected immutable use digest.

The ordinary `verifyManifest` gate requires a selected nonempty same-revision usable `KernelChecked` evidence entry, exact checked-static role and checker/producer designation, canonical proposition, source-fact input digest, accepted result, validity, dependency/assumption/permission constraints, and a nontrivial checked semantic proposition. **The ledger and copied event are public data, not a source authority token.** Ordinary manifest acceptance must never imply that a real checker consumed the selected event.

## Stronger source-produced acceptance

The opaque `AcceptedCheckedStaticUse` can be obtained only through `acceptSelectedCheckedStaticUse` with one real `VerifiedStageClosureProduction` (P6 from P2's private raw-source recheck), one independently closed `CertifiedSourceManifestBinding`, accepted context/ledger and a selected immutable static use. The acceptor compares the complete same-source checked architecture instance descriptor (not I alone); independently runs `verifyManifest`, insists the use is selected, and derives **the original typed event fact** by replaying the sealed source graph's actual occurrence, branch, span, ordinal and semantic proposition. It refuses a match supplied only as a copied public event, a caller-selected ledger, a matching digest/name, or an unrelated source instance.

This F1 contract qualifies only real successful named static checker uses: exact named `SourceRequirementEvidence`, or `SourceProveEvidence` with actual `FocusByEvidence`. It does not reinterpret `prove true`, automatic proof, a provider decision (including Steve `digest_check`), or a synthetic generic runtime/erasure operation as a qualified static use. This is an **actual checked static alternative**, not evidence of the dynamically executed branch or final P7 use. A source environment's named evidence admission is governed by existing accepted Phase 1 checker policy, not a new oracle.

## Actual regressions and remaining gaps

The focused real-source regression rechecks the historical Upload client/server through P2, P6 and the immutable selected source-instance manifest binder, selects a genuine checked `BeginPolicy` proof consumer, verifies its evidence entry, and refuses a deliberately rehashed false site/ordinal plus a separate empty selection. Historical P7 structural Upload/Steve tests remain honestly P7-bounded, and all original source cases continue to run. The new dedicated workflow has no write/secret permissions and runs strict GHC 9.6.7 and the existing E1/E2/INT-002 tests.

This proof is **narrow** and requires further audit of independent evidence checker qualification and completeness for all source-use kinds. It does **not** prove arbitrary source-environment proof provenance, full Core event simulation, SYS-012 complete later consumers, SYS-013 selected immutable assumption/discharge, P8 full cross-language correspondence, or P7 final selected evidence use. In particular the accepted selected assurance metadata is not by itself a historical proof of original checker consumption; the opaque source producer gate is mandatory. The ordinary independent immutable ledger policy is not changed.

Next, only if F1 is protected-merged and the existing grammar/qualified checker supports it, F2 must produce a **nontrivial meaningful Steve** and Upload positive through this same qualified seam (not `digest_check` relabeling or `prove true`). If this is unachievable under current source/TCB, stop. Only after a competent contract can the separately authorized E3 install mandatory selected P7 final use. No P10, signed release, or freeze is implied.
