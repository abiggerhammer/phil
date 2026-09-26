# Phase 1 audit — fixed final-authority adapter correspondence

Status: defensive proof-correspondence continuation for `D-ARTIFACT-MANIFEST-REFLECTION-01`.

The independent package audit established a bounded native contract, and the preceding proof slice kept raw Systems digest, normalized Systems revision, common StageContract revision, and final closed-stage revision distinct.

This slice formalizes one narrow proof-side boundary: a fixed or supplied Phase-1 adapter may connect a source assurance, an independently supplied native manifest, an independently supplied native stage, and the semantic `ArtifactStageContext` only by carrying their exact coordinate equalities. It does not infer authority from matching names, from one Boolean, or by rebuilding manifest fields from the stage.

`FixedFinalAuthorityAdapter` records the exact source-assurance identity, implementation digest, lowering root, subject, instance and realization revisions, normalized Systems revision, common StageContract revision, closed-stage revision, and verifier-profile revision. From that record, the proof derives the existing `NativeReleaseBound` and `NativeReleaseStageRepresents` premises and composes them with the existing native-release theorem to establish `FinalManifestMatches`.

This is a correspondence theorem for a documented fixed or supplied Phase-1 adapter. It is not an extraction of the Haskell source-admission, manifest, or stage-bundle types; it does not claim an automatic source-to-complete-stage producer; and it does not add a general Phase-2 compiler requirement. A stronger ordinary-source/native producer remains a separate claim that would need its own implementation evidence.

LLVM remains trusted in Phase 1. No production Haskell, package script, runtime path, or release artifact changes.
