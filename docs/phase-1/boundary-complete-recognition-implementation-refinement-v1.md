# PHIL-BND-COMPLETE-001 implementation-refinement staging v1

This staging slice extracts the incremental executable decision owned by the already-Certified `PHIL-BND-COMPLETE-001` obligation without changing production.

## Certified incremental seam

The complete-recognition layer adds an ordered extent classification before the existing recognition machinery may produce either a successful recognized witness or a malformed-recognition failure:

1. a negative declared frame extent rejects as invalid;
2. otherwise a negative consumed extent rejects as invalid;
3. otherwise consumption short of the declared frame rejects as trailing bytes;
4. otherwise consumption past the declared frame rejects as over-consumption;
5. otherwise the extent is exactly complete and recognition/failure construction may proceed.

`proof/Phil/Core/BoundaryCompleteRecognitionImplementation.v` defines the representation-neutral Boolean-reflection kernel `decideCompleteExtentByFacts` and proves that, when its four facts are supplied by the Certified `Z.ltb` comparisons, its result is definitionally identical to `BoundaryCompleteRecognition.checkCompleteExtent`. It also composes that equality with `check_complete_extent_complete_iff`, so the extracted `ExtentComplete` result is equivalent to the Certified `CompleteExtent` proposition.

## What remains native

This slice deliberately does not move concrete `Int` representation or comparison into Rocq. Production still owns:

- `Int` representation, comparison, and overflow behavior;
- construction of exact `CompleteRecognitionError` diagnostics;
- `Name`, `GrammarId`, `FrameId`, `Text`, and `ResourceContext` representations;
- active raw-loan validation and resource-context correspondence;
- parser/recognizer implementation competence and framing-source correctness.

The exact success/failure provenance and failure-finalization portions of the Certified theorem compose with the predecessor recognition obligations (`PHIL-RECOG-GATE-001`, `PHIL-RECOG-COMMIT-001`, and `PHIL-RECOG-FAIL-001`). This refinement does not duplicate or widen those predecessor authorities.

## Validation

The dedicated Phase 1 Boundary Complete Recognition workflow fresh-extracts `BoundaryCompleteRecognitionKernel.hs`, strict-typechecks it, runs direct controls over the decision precedence, strict-typechecks the unchanged production boundary/recognition modules, and reruns the unchanged BND-001–003 complete/trailing/malformed correspondence corpus.

A green staging PR leaves `PHIL-BND-COMPLETE-001` at `Discharged / Certified`. A separate closeout must check in the exact extracted kernel and bind `Phil.Core.BoundaryRecognition`'s extent classification to it before the ledger can move to `Implementation Refined`.
