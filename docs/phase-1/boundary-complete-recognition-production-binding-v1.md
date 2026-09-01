# Phase 1 boundary complete-recognition production binding v1

Obligation: `PHIL-BND-COMPLETE-001`

This closes the bounded implementation-refinement step staged by PR #469.
The Certified theorem family remains `proof/Phil/Core/BoundaryCompleteRecognition.v`.
The staging proof `BoundaryCompleteRecognitionImplementation.v` proved that the
reflected four-fact decision is exactly the Certified `checkCompleteExtent`
classification.

## Exact extracted kernel

Production checks in the exact Rocq-extracted kernel at:

`src/BoundaryCompleteRecognitionKernel.hs`

Harvested SHA-256:

`e97fd09b8067c47783f2e8dbfcae84adec816185d36b1131460888a5eff332fe`

The production-binding workflow fresh-extracts the kernel and requires byte-for-byte
identity with this checked-in file before any Haskell correspondence check runs.

## Production binding

`src/Phil/Core/BoundaryRecognition.hs` retains the concrete
`RecognitionExtent` representation and computes four native `Int` comparison facts:

1. declared extent is negative;
2. consumed extent is negative;
3. consumed extent is before declared extent;
4. declared extent is before consumed extent.

Those facts are passed to `decideCompleteExtentByFacts`. The extracted kernel owns
the ordered final classification:

- invalid extent;
- trailing bytes;
- consumed past frame;
- exact complete extent.

The existing public `CompleteRecognitionError` values are reconstructed from that
classification without changing their payloads.

## Preserved predecessor boundaries

This closeout does not move the following authority into the extracted kernel:

- concrete Haskell `Int` representation, comparison, or overflow behavior;
- frame-length observation and framing-source correctness;
- `Name`, `GrammarId`, and `FrameId` representation;
- `ResourceContext` and shared-loan correspondence;
- raw-view validation;
- parser / recognizer implementation competence;
- exact parsed-witness and recognition-failure construction;
- pending-state consumption on recognition failure;
- diagnostic payload representation.

Exact witness/failure provenance and failure finalization remain composed Certified
predecessor recognition obligations. The incremental semantic authority of
`PHIL-BND-COMPLETE-001` bound here is the complete-frame extent classifier.

## Closeout gate

The dedicated workflow must:

- compile the Certified and implementation-correspondence Rocq proofs;
- fresh-extract `BoundaryCompleteRecognitionKernel.hs`;
- compare it byte-for-byte with the production kernel and assert the harvested SHA;
- strict-typecheck both extracted and production kernel copies;
- execute the direct extent-decision controls against the production kernel;
- strict-typecheck the bound `BoundaryRecognition.hs` path;
- rerun the unchanged BND-001–003 complete/trailing/malformed corpus; and
- record exact closeout identities as artifacts.

A green exact-head closeout permits the ledger row to move from
`Discharged / Certified` to `Discharged / Implementation Refined`.
