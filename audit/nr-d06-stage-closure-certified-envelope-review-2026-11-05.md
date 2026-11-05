# NR-D06 — StageClosure / certified-envelope caller reconciliation

**Date:** 2026-11-05  
**Lane:** bounded independent-audit follow-up / current-source review; not final independent sign-off  
**Source baseline:** `abiggerhammer/phil` main `551b44f2f5eaff8362cdc4acfbe03188930d4908` (before this audit-only replay branch)  
**Predecessor:** independent NR-D05, 2026-09-30, source review `0d96a19950b70a3ca0897f4467f0579172c49991`. Historical event and evidence remain unchanged.  
**Existing finding lineage:** `D-ARTIFACT-MANIFEST-REFLECTION-01`, `D-CERT-SUPPORT-01`, `D-SYS-ASSUMPTION-AUTHORITY-01`. These are not three newly discovered bugs.

## Question

Do the actual StageClosure, source-assurance, certified-release, sidecar, and stage-summary callers preserve their independently supplied authority and exact identity domains, or does a locally coherent stage/manifest get mistaken for whole-artifact certification?

## Source and consumer dispositions

| Boundary | Verified source-level behavior / explicit limit |
| --- | --- |
| **Concrete StageClosure** (`src/Phil/Systems/StageClosure.hs`) | `verifyStageClosureBundle` first verifies the supplied concrete branch (BranchResource or BoundaryCommit) and independently stored next-stage trunk. It then compares subject, instance, realization, normalized Systems artifact, *common* Phase-1 StageContract, and verifier profile across trunks, and recomputes stored normalized Systems and *final closed* contract revision. The extracted decision-kernel predicate is downstream of the concrete predecessor checks. This is not a checker of arbitrary unsupplied semantic-provider truth. |
| **VER-010 source/artifact pair** (`src/Phil/Verification/ArtifactClosure.hs`) | `certifyApplicationArtifact` requires an already accepted `GenericApplicationAssurance` witness and independently verifies the supplied `StageClosureBundle`. It neither constructs nor verifies a final manifest; calling this pair the complete final-release gate would be incorrect. |
| **INT-005 certified envelope** (`src/Phil/Verification/CertifiedRelease.hs`) | `certifyReleaseArtifact` independently verifies the supplied `AssuranceManifest` against its own `VerificationContext` and ledger, and the supplied complete StageClosure. It compares manifest target and compilation profile, manifest raw implementation digest and lowering root against the *concrete* stage Systems artifact, emitted LLVM source/target digests and canonical text, exact target profile, and the declared trust-kind domain. Its constructor is not exported. No supplied source-assurance witness is an argument to this function; the proof's source-assurance binding is an **additional correspondence premise** across callers, not magically established by the envelope alone. |
| **Semantic proof and native/model adapter** (`proof/Phil/Verification/VerificationArtifact.v`, `FinalManifestStageReflection.v`, `FinalManifestNativeCoordinateReflection.v`, `FinalManifestFixedAdapter.v`) | `FinalArtifactCertified` requires accepted source, preserved stage, and matching final manifest. Native acceptance, the exact manifest-to-stage/source relation, and exact model representation are explicit premises of the adapter theorems; the fixed adapter is a `Prop` record of obligations, **not a native extractor**. No fresh Haskell-to-Rocq representation proof or full accepting source/manifest/stage adapter is inferred here. |
| **Identity domain separation** | The raw `systemsArtifactDigest`, normalized `SystemsArtifactRevision`, common `Phase1StageContractRevision`, and final `ClosedStageContractRevision` are distinct. Manifest raw digest comparison must not be used as a substitute for common or closed-stage revision agreement. Proof's manifest StageContract coordinate refers to the **common** contract. |
| **INT-005 package / INT-007 runtime stage summary** | `ReleasePackage.hs` emits an inspectable manifest/LLVM/lowering/cost/trust sidecar, **not** a full serialization of every StageClosure field. The separate INT-007 runtime/build handoff carries stage-specific canonical and revision information with decoding/expected-summary comparison. One sidecar's smaller field set does not establish loss of the separately verified runtime/build handoff. |

## Executed controls requested by this follow-up

Extend the permanent `test/Phase1INT005CertifiedReleaseEnvelopeMain.hs` native Haskell caller suite for both Upload and Steve:

- Already-green positive `certifyReleaseArtifact` constructions remain; ordinary manifest/LLVM/trust negative controls remain unchanged.
- Mutate only the stored normalized Systems revision in an otherwise unchanged StageClosure; require direct `verifyStageClosureBundle` rejection and the exact nested `CertifiedReleaseStageClosureRejected` wrapper.
- Mutate only the closed StageContract revision in an otherwise unchanged StageClosure; require direct and nested rejection without confusing it with common Phase-1 StageContract identity.
- Recompute a *self-consistent* independent manifest and VerificationContext with a wrong raw Systems digest; require the envelope to reject against the unchanged stage's independently recomputed actual Systems digest.
- Replay existing `test/Phase1VerificationSourceArtifactClosureMain.hs`, `test/Phase1StageClosureMain.hs`, and `test/Phase1INT005ReleasePackageMain.hs` to preserve separate source/artifact, trunk identity, and package controls.
- Compile the existing seven-module final-manifest fixed-adapter Rocq dependency closure and print its named theorem assumptions, **without** inventing a native adapter.

The dedicated workflow should record exact-head results. Until green, the items above are *submitted controls*, not executed evidence.

## Bounded disposition

**No new distinct canonical language implementation defect was established by this source review.** NR-D06 is a connection/caller audit, not an automatic license to promote the existing model's assumption to a derived native proof. The existing `D-ARTIFACT-MANIFEST-REFLECTION-01` native-to-proof correspondence, plus its inherited assumption-authority/source binding premises, still needs a separately scoped accepting-adapter closeout if the final certification claim requires it.

Do not claim publication-byte verification, LLVM native semantics beyond the named tests, complete signed independent source review, general runtime or provider correctness, a final candidate, or Phase 1 audit freeze. Independent final delta and public release-byte revalidation remain separate.

**Links:** [historical implementation audit ledger](https://drive.google.com/file/d/1DkP56xVvYMIPyliSF7TxbER_2Lss492l/view), [independent code review index](https://drive.google.com/file/d/1M5mk_xuWPp0AFnP8r9nwLzbshZVrdT7X/view), [Phase 1 readiness reconciliation](https://github.com/abiggerhammer/phil/blob/main/audit/phase1-readiness-reconciliation-2026-11-05.md).
