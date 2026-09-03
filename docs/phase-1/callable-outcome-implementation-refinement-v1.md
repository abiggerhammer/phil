# Callable Outcome implementation refinement v1

`PHIL-CALL-OUTCOME-001` is staged for implementation refinement without changing production Haskell behavior.

## Certified semantic seam

The existing Certified model in `CallableOutcomeFidelity.v` owns the final outcome decision after concrete identity/equality facts have been reflected:

1. exact caller-visible outcome-class domain;
2. exact branch-sensitive state;
3. exact callee transition;
4. residual-obligation disposition, including the exact bucket for a detected reclassification;
5. exact residual-obligation set when disposition is `ResidualExact`;
6. exact postconditions;
7. exact assumptions;
8. exact effects;
9. exact discharged facts.

The extracted decision preserves the Certified rejection precedence and returns one explicit classification for each failure or exact acceptance.

`callable_outcome_decision_matches_certified` proves that translating the extracted decision back to the Certified result is byte-for-byte the same decision tree as `checkCallableOutcomeContract` composed with `checkOutcomeBranch`, under explicit hypotheses reflecting the eight native equality facts to the corresponding `Nat.eqb` facts in the Certified model.

## Native boundary retained

This staging layer deliberately does not claim correspondence for:

- `CallableOutcomeClass`, `CallableOutcomeState`, `CallableOutcomeAtom`, or `CalleeTransition` representation/equality;
- list-to-`Map` normalization and duplicate detection;
- `Map`/`Set` domain, ordering, membership, difference, or extensional semantics;
- selection of the first missing residual obligation and the concrete reclassification witness;
- native diagnostic payload reconstruction;
- proposition/evidence truth behind semantic atoms;
- source elaboration or downstream checker competence;
- GHC/runtime correctness or the Rocq extraction toolchain.

The existing ten-case CALL-018 corpus remains the native conformance evidence for those concrete boundaries.

## Staging gate

The dedicated workflow:

- compiles the existing Certified proof plus the implementation correspondence proof;
- freshly extracts `CallableOutcomeKernel.hs`;
- records source, `.vo`, extracted-kernel, production Haskell, unchanged CALL-018 corpus, and direct-harness identities;
- strictly typechecks and executes fourteen direct extracted-kernel controls covering every decision class, all four residual reclassification buckets, and precedence-sensitive cases;
- strictly typechecks unchanged production `Phil.Core.CallableOutcome`;
- reruns the unchanged ten-case CALL-018 corpus.

A green staging merge leaves `PHIL-CALL-OUTCOME-001` at `Discharged / Certified`. Production binding to the exact extracted kernel is required before promotion to `Implementation Refined`.
