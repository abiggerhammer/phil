# PHIL-CALL-MODE-STRENGTHEN-001 — explicit closure-mode strengthening proof v1

This proof certifies the normalized semantic rule implemented by Matrix `CALL-017`.

`PHIL-CALL-MODE-001` remains the authority for deriving a closure's minimum structural mode from its exact capture set. This successor theorem covers only the declaration layer placed on top of that already-Certified minimum.

An omitted closure-mode declaration selects the exact capture-derived minimum. An explicit declaration may select the same mode without a strengthening justification. An explicit stricter mode is accepted only when it does not weaken the capture minimum and carries an explicit semantic lifecycle or authority justification bound to the exact callable contract with nonempty detail.

Target implementation facts cannot strengthen source closure mode. A wrong-contract lifecycle/authority reason cannot justify strengthening, an empty semantic reason cannot justify strengthening, and a declaration below the capture-derived minimum cannot certify. Selecting a mode never rewrites or reclassifies the capture-derived minimum itself.

The dedicated workflow recompiles `PHIL-CALL-MODE-001` and `PHIL-CALL-MODE-STRENGTHEN-001` under Rocq 9.2.0, strictly typechecks the production CALL-017 implementation/corpus under `-Wall -Werror`, and reruns all eight unchanged focused cases.

## Boundary

Concrete Haskell `InterfaceRevision`/`Text` representation and equality, source elaboration, capture discovery, and truth of the referenced lifecycle/authority obligation remain explicit correspondence or predecessor boundaries. Target closure-environment layout and backend implementation facts remain outside the source semantic strengthening rule.
