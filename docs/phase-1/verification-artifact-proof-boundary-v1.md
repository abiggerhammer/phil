# PHIL-VERIFY-ARTIFACT-001 proof boundary v1

This boundary certifies the semantic distinction between source assurance and emitted-artifact certification.

## Certified composition

A final artifact is certified only when all three layers hold independently:

1. **Source assurance is already accepted.** Source-level verification remains a necessary predecessor and is not replayed or rewritten by realization.
2. **The exact emitted realization passes Certified `PHIL-SYS-STAGE-CLOSURE-001`.** This imports exact source-disposition coverage, exact target-mechanism justification, validity-scope matching, and the exact subject / architecture instance / architecture realization / Systems / StageContract / verifier-profile identity trunk.
3. **The final assurance manifest closes and is bound to that exact source assurance and StageClosure identity.** A closed manifest cannot silently refer to another realization, Systems revision, StageContract revision, target, or profile.

## Fail-closed consequences

The proof establishes that:

- source closure alone is never artifact certification;
- a stale stored Systems identity or final StageClosure identity prevents artifact certification;
- a changed realization or Systems identity that no longer matches the final manifest remains uncertified;
- any live target mechanism without an exact certified StageClosure justification prevents artifact certification; and
- the final manifest must retain exact realization, Systems, and StageContract correspondence.

These are closure-stage failures. They do not rewrite source assurance or change proposition truth.

## Production correspondence

`src/Phil/Verification/ArtifactClosure.hs` implements VER-010's source-plus-StageClosure composition. Its `GenericApplicationAssurance` input is already accepted source assurance by construction; `verifyStageClosureBundle` is the independent realization/Systems gate.

The final manifest gate is deliberately kept separate. Phase 1's permanent INT-002/INT-005 paths build and verify the scoped `AssuranceManifest` and bind it into certified-release artifacts. `VerificationArtifactImplementation.v` therefore certifies the finite conjunction structure across the existing source-assurance, StageClosure, and manifest authorities instead of pretending that `ArtifactClosure.hs` alone is the entire release-certification pipeline.

## Explicit boundaries / TCB

This proof does **not** eliminate or re-prove:

- concrete `GenericApplicationAssurance` construction and digest representation;
- Haskell `StageClosureBundle` representation or the Haskell/Rocq correspondence already owned by the StageClosure certification boundary;
- concrete `AssuranceManifest` / ledger construction and verification;
- canonical serialization and hashing;
- compiler/backend translation correctness beyond the certified StageClosure contracts;
- LLVM/toolchain correctness, host runtime behavior, qualified providers, external checkers, or target-platform assumptions.

Those remain explicit predecessor, representation, or Phase-1 residual-TCB boundaries. Source theorem evidence never silently proves translation correctness.
