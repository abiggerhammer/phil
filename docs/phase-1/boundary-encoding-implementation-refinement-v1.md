# PHIL-BND-ENCODE-001 implementation refinement staging

This slice stages an executable, representation-neutral decision surface for the
already-Certified `PHIL-BND-ENCODE-001` boundary encoding theorem. Production
behavior is unchanged.

## Certified decomposition

The bounded BND-008–010 theorem has three implementation-facing decisions:

1. qualified generated encoding accepts only after an encoder is already
   admitted, its representation is exact, and the generated output owner is the
   exact expected owner;
2. canonicality is an independent opt-in requirement: a legal noncanonical
   grammar member is accepted unless canonical encoding was explicitly
   required; and
3. serialization accepts only checked-wire correspondence, then exact
   representation, then exact subject. Raw host-memory layout and matching
   C-struct shape are rejected before identity checks.

The generated evidence also preserves exactly the encoder implementation,
representation revision, and output owner.

## Extracted decisions

`BoundaryEncodingImplementation.v` owns:

- `decideQualifiedEncodingByFacts`, over reflected encoder-admission,
  representation-equality, and output-owner-equality facts in Certified order;
- `planGeneratedEncoding`, a polymorphic construction plan preserving exact
  encoder implementation, representation, and output-owner coordinates;
- `decideEncodingCanonicality`, directly over the Certified canonicality and
  encoding-form enums; and
- `decideBoundarySerializationByFacts`, directly over the Certified
  serialization-basis enum plus reflected representation and subject equality.

The Rocq correspondence proves acceptance requires the exact reflected facts,
preserves every rejection precedence, proves the generated-evidence plan is
coordinate-exact, covers all canonicality cases, and characterizes successful
serialization as checked-wire plus exact representation and subject.

## Native bridge boundary

Production remains responsible for reflecting concrete facts:

- whether the encoder's already-checked provider qualification admits it;
- equality of concrete encoder implementation, `BoundaryRepresentationId`, and
  output-owner `Name` values;
- truth of the concrete encoding form/canonicality classification;
- truth of the concrete serialization basis; and
- equality of the concrete serialization representation and semantic subject.

The later production binding must retain the existing detailed Haskell
expected/actual diagnostics and concrete evidence/public API types. The
extracted kernel owns semantic accept/reject choice, order, and exact
construction coordinates only.

No claim is made here about encoder implementation correctness, exact emitted
bytes, cryptographic properties, grammar parser/recognizer correspondence,
provider competence truth, actual wire I/O, ABI/layout equivalence, or
zero-copy realization. Those remain explicit separate boundaries.

## Staging verification

The existing `Phase 1 Boundary Encoding Proofs` workflow is extended additively
to:

1. compile the Certified theorem and this implementation correspondence;
2. fresh-extract `BoundaryEncodingKernel.hs`;
3. strict-typecheck the extracted kernel under `-Wall -Werror`;
4. run direct controls for all qualified-encoding gates, exact generated-plan
   construction, all canonicality cases, and all serialization rejection/
   acceptance classes;
5. strict-typecheck unchanged BND-008–010 production and tests; and
6. rerun the unchanged 12-case BND-008–010 conformance corpus.

The workflow records exact SHA-256 identities for the extracted kernel,
unchanged production sources, unchanged corpus, direct harness, correspondence
proof, and this note.

## Status discipline

A green staging run is mechanized implementation-correspondence evidence only.
Production is unchanged, so `PHIL-BND-ENCODE-001` remains `Discharged /
Certified`. A separate exact-kernel production-binding closeout is required
before the ledger may move to `Discharged / Implementation Refined`.
