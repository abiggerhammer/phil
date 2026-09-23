# Phase 1 audit — exact final-manifest/stage reflection

Status: defensive proof-correspondence slice for `D-ARTIFACT-MANIFEST-REFLECTION-01`.

This slice follows the SYS-013 imported-assumption-authority boundary without changing the Phase 1 trusted computing base. It addresses one narrower correspondence question from the live audit handoff: when the semantic proof says a final manifest matches source assurance and an exact `StageClosure`, what ensures that the proof-side manifest actually represents the independently supplied native manifest rather than values copied from the stage itself?

## Boundary

`proof/Phil/Verification/VerificationArtifact.v` already defines `FinalManifestMatches`. Its coordinates include the accepted source-assurance identity plus exact subject, instance, realization, Systems, common StageContract, and verifier-profile identities from the concrete stage.

`src/Phil/Verification/CertifiedRelease.hs` independently accepts a supplied `AssuranceManifest` and a supplied `StageClosureBundle`, verifies both, and checks their shared release coordinates. It does not construct the manifest from the stage.

The new `FinalManifestStageReflection.v` proof makes the missing representation premise explicit:

1. a native final manifest is independently accepted;
2. that native manifest is exactly bound to the accepted source assurance and stage coordinates; and
3. the proof-side `FinalManifestFacts` exactly represents that same native manifest.

Only from those three facts does the proof derive `FinalManifestMatches` and, with the existing source/stage premises, `FinalArtifactCertified`.

## Negative pressure

The proof also records why stage-local equality is insufficient. A proof-side manifest may satisfy `FinalManifestMatches` relative to a stage while still failing to represent an independently authoritative native manifest whose Systems coordinate differs. This prevents a future adapter from making the theorem vacuous by populating model manifest fields directly from the stage under test.

Two additional rejection lemmas keep source-assurance identity drift and common StageContract drift explicit.

## What this does not claim

This PR does not add a new release format, a richer SYS-013 assumption representation, a Phase 2 requirement, or a new trusted component. It does not yet implement the native application adapter that extracts every erasure/assumption authority relation. The live handoff's producer/consumer binding work remains separate.

LLVM remains inside the Phase 1 trusted computing base. This slice audits only Phil-owned proof correspondence.
