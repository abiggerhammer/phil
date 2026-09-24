# Phase 1 audit: evidence-consumer event-origin correspondence

This defensive proof-correspondence slice continues the D-RES-SUPPORT-01 / D-RES-TREE-01 closeout after complete same-event final-use and subject-occurrence coverage.

The existing correspondence chain establishes that every represented actual evidence use is classified, reaches the same final consuming event, and represents every relevant subject occurrence with legal stable/rebased subject transport. That still leaves one producer-origin premise explicit: matching event metadata does not by itself prove that the event identity came from an approved original checking event.

This matters especially for residual-free results. A caller supplying a `ResidualSpec`, or any other event-shaped metadata, must not be treated as evidence that an independently produced original event exists. The exact event already used by same-event final-use correspondence must itself have approved producer origin.

`EvidenceConsumerEventOriginCorrespondence.v` therefore adds a small composition layer over the landed subject-occurrence model:

- every actual evidence use keeps its existing exact event identity;
- that same event must be marked as originating from an approved producer;
- an unrelated approved event is insufficient;
- complete closed-use correspondence remains valid without fabricated subjects when the exact event has approved origin; and
- complete multi-subject occurrence coverage remains valid when the exact event has approved origin.

The negative witnesses deliberately preserve the already-proved lower layers. One has complete closed-use/final-use/subject-occurrence correspondence but no approved producer event. A second has a different approved producer event. Both fail the new origin boundary.

## Native correspondence boundary

The proof does not discover or manufacture the Haskell producer relationship. The native implementation still owns faithful reflection of actual check/evidence uses, exact event maps, final consumers, complete subject occurrence inventory, and the approved producer relation. In particular, it must not infer event origin solely from `ResidualSpec` presence or other caller-supplied metadata.

This slice does not modify production Haskell, source admission, ownership/loan semantics, native lowering, packaging, LLVM, or any other Phase 1 trusted-computing-base boundary. LLVM remains trusted in Phase 1.

## Acceptance cases

1. Complete lower-layer correspondence without approved producer origin is insufficient.
2. Approval of a different event is insufficient.
3. A checked closed use with no subject occurrences remains valid when its exact event has approved producer origin.
4. A two-subject use retaining both subject occurrences remains valid when its exact event has approved producer origin.

The workflow compiles the complete dependency chain plus the new module under Rocq 9.2.0 and records exact source/object digests as audit evidence.
