# Phase 1 complete boundary recognition proof v1

Status: proof slice for `PHIL-BND-COMPLETE-001` over BND-001–003.

## Certified semantic boundary

`proof/Phil/Core/BoundaryCompleteRecognition.v` certifies the bounded complete-recognition layer above the existing recognition machinery:

- a recognition extent is complete exactly when declared and consumed byte counts are nonnegative and equal;
- a valid prefix that consumes fewer bytes than the declared frame is classified as trailing bytes and cannot produce a success witness;
- consuming past the declared frame cannot produce a success witness;
- negative recognition extents reject as invalid;
- successful complete recognition preserves the exact pending owner, grammar, complete frame, and produced value identity;
- malformed complete-frame recognition preserves the exact pending owner, grammar, frame, and failure detail; and
- failure finalization consumes the pending recognition path without manufacturing a success successor/artifact.

The proof deliberately separates complete-frame recognition from later boundary representation, encoding, and protocol progression obligations.

## Executable correspondence

The dedicated workflow rechecks the unchanged production modules:

- `src/Phil/Core/Recognition.hs`
- `src/Phil/Core/BoundaryRecognition.hs`

and reruns the unchanged BND-001–003 corpus:

- `test/Phase1CompleteRecognitionMain.hs` — 2 cases;
- `test/Phase1TrailingBytesMain.hs` — 2 cases;
- `test/Phase1MalformedRecognitionMain.hs` — 2 cases.

The focused correspondence corpus therefore contains **6 unchanged cases**.

## Residual boundary

This is semantic certification, not implementation refinement. Concrete Haskell `Int` arithmetic/overflow behavior, `Name`/`GrammarId`/`FrameId` representation, `ResourceContext`/loan implementation correspondence, parser/recognizer implementation competence, framing-source correctness, exact diagnostics, and Haskell implementation equivalence remain explicit boundaries unless separately refined or certified.

The theorem does not certify boundary representation mappings (`PHIL-BND-REP-001`), encoding (`PHIL-BND-ENCODE-001`), or typed boundary protocol progression (`PHIL-BND-PROGRESS-001`).
