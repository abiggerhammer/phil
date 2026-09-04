# Phase 1 concurrency activation implementation refinement v1

This slice stages machine implementation refinement for `PHIL-CONC-ACTIVATE-001` without changing production behavior.

The Certified theorem in `proof/Phil/Core/ConcurrencyActivation.v` is reflected through six representation-neutral Boolean gates:

- explicit architecture-binding origin;
- exact and non-invented restricted initial ownership;
- exact and non-invented direct stateful ownership;
- the complete seven-field activation-context conjunction;
- the complete four-field participant-classification conjunction; and
- the outer Certified activation/participant conjunction.

`StaticPopulationValid` remains the `PHIL-CONC-SEM-001` predecessor fact. This slice does not redefine the static population semantics or introduce a second process identity model.

Concrete Haskell `Map`/`Set`/`Text` traversal, stable `ProcessKey` representation, source-to-architecture occurrence extraction, explicit binding extraction, and unrestricted-wrapper reachability remain correspondence boundaries. The unchanged Haskell activation/participant corpus continues to exercise those boundaries and retain native diagnostic behavior.

The dedicated workflow freshly extracts `ConcurrencyActivationKernel.hs` from Rocq, records its exact identity, executes the extracted artifact directly, and reruns the unchanged static-population, process-identity, activation-ownership, participant-classification, and unrestricted-reachability corpora.

A green staging merge leaves the obligation at **Certified** evidence. A later production-binding slice will compose the exact extracted kernel with the existing native activation and participant checkers, preserving native diagnostics first and failing closed on kernel disagreement.
