# Steve provider witness implementation refinement v1

This slice stages machine implementation refinement for
`PHIL-PROV-STEVE-WITNESS-001` without changing the production Steve provider
qualification materializer.

The Certified theorem in
`proof/Phil/Core/SteveProviderQualificationWitness.v` is a bounded witness over
the two Phase 1 Steve provider artifacts.  The implementation-refinement surface
groups its nineteen theorem consequences into eleven machine-facing facts that
match the existing PROV-016 pressure corpus:

1. both provider qualification artifacts are admitted;
2. the DigestMatches proposition retains the exact stable owner subject;
3. the scoped-borrow observation is mapped to that stable subject;
4. DigestProvider preserves the candidate-byte borrow;
5. BlobProvider preserves its candidate borrow on all three install outcomes;
6. BlobProvider has state, no-replace law, lifecycle, and authority layers;
7. a second installed event remains forbidden by the no-replace law;
8. partial publication remains forbidden by the lifecycle model;
9. BlobProvider overwrite/delete extra authority is explicit and dispositioned;
10. both qualification evidence manifests close exactly over their declared
    obligation domains; and
11. claim conditions remain explicit in evidence and admission, including the
    DigestProvider SHA-256 profile condition.

`proof/Phil/Core/SteveProviderQualificationWitnessImplementation.v` proves the
Certified witness entails those eleven grouped facts and provides
`decideSteveProviderQualificationWitnessByFacts`.  Fresh Rocq extraction writes
`SteveProviderQualificationWitnessKernel.hs`.  The direct correspondence
harness accepts all eleven facts and rejects each individual group when it is
forced false.

## Staging boundary

`src/Phil/Examples/Steve/ProviderQualifications.hs` remains the production
implementation in this slice.  Its existing provider semantic, evidence, state,
law, lifecycle, authority, and qualification-identity checkers continue to own
native diagnostics and concrete representation behavior.  The unchanged
11-case `Phase1SteveProviderQualificationMain.hs` corpus is rerun beside the
exact extracted decision surface.

A later production-binding slice must gate successful
`materializeSteveProviderQualifications` output through the exact extracted
kernel before this obligation can be promoted from **Certified** to
**Implementation Refined**.

## Explicit nonclaims and residual boundaries

This witness correspondence does **not** prove:

- SHA-256 cryptographic correctness or collision resistance;
- that a filesystem, object store, or other backing store behaves according to
  the BlobProvider model;
- completeness of the modeled interruption, retry, corruption, lifecycle, or
  authority state space;
- universal correctness of DigestProvider or BlobProvider implementations;
- full Steve `ArchitectureRealization` / Systems / `StageContract` integration;
- source elaboration, deployment correctness, scheduler properties, progress,
  fairness, or performance; or
- correctness of Rocq extraction, GHC, or the Haskell runtime.

The SHA-256 profile appears here only as an **explicit qualification condition**:
the witness proves that the condition remains visible in claim, evidence, and
admission lineage.  Its truth is external evidence, not a consequence of this
kernel.
