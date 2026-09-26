# Phase 1 audit — certified-release native coordinate reflection

Status: defensive proof-correspondence continuation for `D-ARTIFACT-MANIFEST-REFLECTION-01`.

The independent artifact/package replay established that Phil's native Phase-1 release path keeps the supplied `AssuranceManifest` and supplied `StageClosureBundle` independently authoritative, checks the manifest implementation digest against the actual raw Systems artifact digest, and checks the lowering-ledger root independently. It also exposed a proof-side representation hazard: several native identities are related but are not interchangeable.

This slice makes those distinctions explicit without changing the Phase-1 trusted computing base.

The new proof keeps separate native coordinates for the raw Systems artifact digest, the normalized/common Systems revision used by the semantic stage model, the common Phase-1 StageContract revision, and the final closed-stage contract revision. It also keeps the manifest implementation digest and lowering-ledger root as distinct native manifest coordinates.

The proof only projects those native coordinates into the existing `NativeFinalManifestAuthority` model after three explicit premises hold: the independently accepted manifest is bound to the exact source assurance, raw Systems digest, and lowering root; the native stage is bound to the exact already-verified `ArtifactStageContext`; and the proof-side `FinalManifestFacts` represents that same native manifest and stage.

Negative theorems record that a raw Systems digest cannot stand in for a distinct normalized Systems revision, a final closed-stage contract revision cannot stand in for a distinct common StageContract revision, and digest/lowering-root drift breaks the native release binding.

This remains a proof-correspondence model. A Rocq record named `NativeReleaseManifest` is not automatically an extraction of Haskell `AssuranceManifest`, and `NativeReleaseStage` is not automatically an extraction of `StageClosureBundle`. Concrete Haskell field extraction, digest/revision representation, canonicalization, and the competent source-to-stage association remain explicit native correspondence boundaries.

No LLVM behavior is audited here. LLVM remains trusted in Phase 1. No production Haskell, release package, runtime path, or Phase-2 requirement changes.
