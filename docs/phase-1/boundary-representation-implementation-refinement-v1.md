# PHIL-BND-REP-001 implementation refinement staging

This slice stages an executable, representation-neutral decision surface for the
already-Certified `PHIL-BND-REP-001` boundary representation theorem. It does
not change production behavior.

## Certified decomposition

The bounded BND-004–007 theorem has three implementation-facing parts:

1. an ordered mapping decision requiring exact representation, grammar,
   semantic value type, recognized grammar, and recognized source-value
   identity before an explicit mapping disposition may accept;
2. exact construction of correspondence evidence carrying the representation,
   grammar, value type, recognized source identity, and semantic target
   identity without collapsing a transforming mapping; and
3. the exact receive-only / send-only / bidirectional use gate.

The production Haskell already implements those same decisions. This staging
slice extracts only their normalized semantic surface so a later closeout can
bind production to the Certified kernel without moving concrete `Text`, `Name`,
or revision representation into Rocq.

## Extracted decisions

`BoundaryRepresentationImplementation.v` owns:

- `decideBoundaryMappingByFacts`, over six reflected Boolean facts in the exact
  Certified/production rejection order:
  1. representation identity,
  2. grammar identity,
  3. value-type identity,
  4. recognized-grammar identity,
  5. recognized source-value identity, and
  6. explicit mapping acceptance;
- `planBoundaryCorrespondence`, a polymorphic construction plan preserving the
  exact representation, grammar, value-type, recognized-source, and
  semantic-target coordinates; and
- `decideBoundaryUse`, which is definitionally the already-Certified
  `checkBoundaryUse` function.

The Rocq correspondence proves that mapping acceptance is equivalent to the six
Certified facts under explicit Boolean reflection hypotheses, that every failed
fact retains the Certified precedence, that every correspondence-plan
coordinate is exact, and that the extracted direction decision is exactly the
Certified direction decision.

## Native bridge boundary

Production remains responsible for reflecting concrete Haskell facts into the
normalized kernel inputs:

- equality of `BoundaryRepresentationId`, `GrammarId`, `ValueTypeRevision`, and
  `Name` values;
- equality between the parsed witness grammar/source identity and the requested
  correspondence identity; and
- whether the concrete mapping competence layer returned `MappingAccepted` or a
  `MappingRejected detail` disposition.

The later production binding must continue to reconstruct the existing detailed
Haskell diagnostics, including concrete expected/actual identifiers and mapping
failure detail. The extracted decision surface owns only which semantic gate
accepts or rejects and its order.

Parser/recognizer correctness, the truth/competence of the supplied mapping
disposition, concrete equality implementations, Haskell/GHC correctness, and
Rocq extraction/toolchain correctness remain explicit boundaries.

Encoding qualification/canonicality, serialization, ABI/layout/zero-copy
realization, actual wire I/O, and typed protocol progression remain separate
obligations and are not widened here.

## Staging verification

The existing `Phase 1 Boundary Representation Proofs` workflow is extended
additively to:

1. compile the existing Certified theorem and this implementation
   correspondence;
2. fresh-extract `BoundaryRepresentationKernel.hs`;
3. strict-typecheck the extracted kernel under `-Wall -Werror`;
4. run direct controls for all mapping rejection gates, exact correspondence
   construction, and all six direction/use combinations;
5. strict-typecheck the unchanged production BND-004–007 mapping/direction
   implementation and corpus; and
6. rerun the unchanged 13-case BND-004–007 correspondence corpus.

The workflow records exact SHA-256 identities for the extracted kernel, the
unchanged production mapping/direction sources, the unchanged corpus, the
control harness, the correspondence proof, and this note.

## Status discipline

A green staging run is mechanized implementation-correspondence evidence only.
Production remains unchanged in this slice, so `PHIL-BND-REP-001` remains
`Discharged / Certified`. A separate exact-kernel production-binding closeout is
required before the ledger may move to `Discharged / Implementation Refined`.
