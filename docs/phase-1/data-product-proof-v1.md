# PHIL-DATA-PRODUCT-001 — finite product ownership proof

This proof certifies the Phase 1 ordinary finite-product ownership boundary over the already implemented DATA-015 slice landed in #320.

## Certified semantic core

`proof/Phil/Core/DataProduct.v` composes the existing Certified aggregate-mode and Core ownership semantics and proves:

- a finite product's structural mode is the strongest/LUB of its ordered element modes;
- every element mode is bounded by the resulting product mode, and any linear element makes the whole product linear;
- product formation uses the same restricted-occurrence discipline as aggregate construction: one affine/linear occurrence can occupy at most one owning product position;
- duplicating one restricted source occurrence into two product slots is rejected;
- consuming product elimination requires exact arity between element contracts and successor names;
- successor names are unique;
- every source element position has exactly one successor position and retains its exact mode/type contract;
- no successor position can be fabricated without a corresponding element contract;
- consuming a linear product removes the product owner and cannot consume that same owner twice; and
- a live linear product binding cannot satisfy the proof-level completed-resource predicate, so it cannot be silently dropped.

The product restoration plan is structural and ordered. It deliberately does not infer nominal identity from product shape; products remain non-nominal in this Phase 1 slice.

## Correspondence gate

The dedicated `Phase 1 Data Product Proofs` workflow compiles the theorem under Rocq 9.2.0, records exact source and `.vo` identities, typechecks the unchanged product implementation paths under `-Wall -Werror`, and reruns the unchanged seven-case DATA-015 corpus:

- product mode derives from owned elements;
- formation transfers restricted owners;
- duplicate restricted source rejects;
- elimination restores exact elements;
- missing successor rejects;
- duplicate successor rejects; and
- a live linear product cannot be silently dropped.

## Residual assumptions / non-claims

This is semantic certification, not implementation refinement. The following remain explicit correspondence or trust boundaries:

- concrete Haskell list/order and `ProductElementType` / `ProductValue` / `TyProduct` representation;
- source-to-Core product syntax/value elaboration;
- exact correspondence of concrete affine consumption with the normalized restricted-occurrence theorem;
- concrete product formation/elimination orchestration and diagnostics;
- Haskell implementation equivalence; and
- Rocq kernel/toolchain correctness.

`PHIL-DATA-MODE-001` supplies the Certified strongest-mode and construction discipline. `PHIL-DATA-ELIM-001` supplies the broader consuming-elimination ownership boundary; this proof specializes the product-specific exact positional restoration contract.
