# Phase 1 audit: recognized-occurrence encoding authority boundary

Status: defensive proof-correspondence slice for `D-RECOGNIZED-OCCURRENCE-ENCODING-01`.

## Question

`Phil.Core.Recognition.recognizedOccurrenceTerm` currently builds one opaque `Frame` term by concatenating four supplied identity components — pending owner, grammar ID, frame ID and parsed value name — with `:` separators.

The latest independent audit replay produced two legitimate trusted Core recognition witnesses through `receiveFrame`, `beginRawLoan` and `trustedRecognitionSuccess` whose component tuples differ while their rendered opaque occurrence terms are equal. That is a supplied-domain observation, not an ordinary Surface-admission finding and not a refutation of the local session/recognition proofs.

The correspondence question is narrower: when later proofs or consumers treat equality of the opaque occurrence term as equality of the underlying recognized occurrence, what authority establishes that the rendering is injective on the admitted component domain?

## Proof slice

`proof/Phil/Assurance/RecognizedOccurrenceEncodingBoundary.v` separates three facts:

- the underlying four-component occurrence identity;
- an explicit admitted component domain; and
- injectivity of the chosen encoding on that domain.

It records a concrete collision for unrestricted delimiter concatenation: moving one separator-bearing fragment across a field boundary changes the component tuple without changing the rendered atom sequence. Therefore equality of the current style of rendered payload cannot, by itself, recover exact component identity over an unrestricted supplied domain.

The same file gives a structurally framed representation of the four fields and proves that representation injective for the unrestricted model. This is a proof-side witness of the kind of authority a native representation can supply; it is not a claim that production Haskell already uses structural framing.

## Native correspondence

For Phase 1, the accepting recognition path needs one of two bounded justifications before opaque occurrence equality can stand for exact occurrence identity:

1. use an injective structural/framed encoding of the four identity components; or
2. name and enforce an admitted native component domain on which the existing textual rendering is proved injective.

A downstream theorem which merely assumes or compares the rendered term cannot establish that producer-domain property retrospectively. Likewise, successful ordinary-source controls do not prove a global invariant for arbitrary public `FrameId`/`Name` values.

This proof slice intentionally does not select the implementation repair. That belongs to the implementation-remediation lane together with the existing Q01 regression and positive recognition/re-entry controls.

## Boundaries

This work changes no Haskell implementation, recognition API, source grammar, session semantics, LLVM integration or Phase 1 trusted-computing-base component. It adds no Phase 2 requirement and does not weaken the already positive bounded verdict for the examined nonlegacy recognition route. It only makes the missing producer-domain/injective-encoding premise explicit and machine-checked.
