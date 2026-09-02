# Systems identity implementation refinement v1

This staging slice mechanically refines already-Certified `PHIL-SYS-ID-001` without changing production behavior.

The Certified theorem in `proof/Phil/Systems/Identity.v` owns two exact normalized relations:

- `ArtifactIdentityVerified`: five equality gates binding trusted source, Systems target/program, complete Systems artifact, recomputed lowering root, and manifest lowering root;
- `DecisionBindingVerified`: five per-decision gates requiring nonempty stable identity, exact map-key identity, exact recomputed decision digest, and exact source/target artifact binding.

`proof/Phil/Systems/IdentityImplementation.v` exposes those relations as two fail-closed executable classifiers and proves Boolean-reflection correspondence to the Certified propositions. `IdentityImplementationExtraction.v` fresh-extracts the classifiers to `SystemsIdentityKernel.hs`.

The staging workflow runs 12 direct controls: accepted plus each of the five failure classes for artifact identity, and accepted plus each of the five failure classes for decision binding. It also strict-typechecks the unchanged production verifier and reruns the unchanged 20-case `test/SystemsMain.hs` corpus, whose existing identity cases include source identity, target identity, lowering-root tamper, and decision-digest tamper rejection.

## Deliberate boundary

This theorem and extracted kernel treat digests as opaque equality-bearing values. Concrete `Digest`/`Text` representation, canonical serialization, SHA-256 collision resistance or injectivity, `Map`/`Set`/list traversal, recomputation functions, assurance-manifest construction, detailed Haskell diagnostics, and the truth of external/runtime evidence remain explicit implementation/correspondence/TCB boundaries.

A green staging merge leaves the ledger at `Discharged / Certified`. A separate production-binding closeout must route the concrete identity gates through the exact extracted kernel before `PHIL-SYS-ID-001` can be promoted to `Implementation Refined`.
