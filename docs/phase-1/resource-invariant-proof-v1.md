# PHIL-RES-INVARIANT-001 — join/loop invariant establishment proof v1

This proof certifies the semantic core of RES-013 over the already implemented `ControlStateInvariant` checker.

The lower resource layer is not duplicated. `PHIL-RES-JOIN-001` owns structural projection/resource conservation; `PHIL-RES-LOOP-001` owns one declared loop-state telescope and explicit propositional transport; `PHIL-RES-OBL-001` owns unresolved-obligation preservation. This proof adds only the logical invariant gate above those layers.

## Certified claims

For every relevant join predecessor, loop initial entry, and loop backedge admitted by one invariant boundary:

- the ordinary Certified structural resource projection must already succeed;
- the predecessor exposes exactly the declared post/header state-slot witness domain;
- every declared slot has a predecessor-specific witness and undeclared slots cannot be synthesized;
- the declared invariant is instantiated for that exact predecessor and must be established independently there;
- structural state compatibility plus exact witnesses is insufficient if that instantiated proposition is not established;
- evidence available on one predecessor cannot substitute for missing evidence on another;
- loop initial entry and every backedge pass the same logical gate; and
- multiple continuing join predecessors likewise establish independently.

The theorem deliberately does **not** infer logical truth from resource/state compatibility.

## Correspondence to RES-013

The unchanged Haskell checker in `src/Phil/Systems/ControlStateInvariant.hs` follows the same layering:

1. run `checkStateBoundaryProjections` first;
2. require exact invariant/boundary and slot-binder domains;
3. require exactly the same predecessor-key domain as the structural projections;
4. verify each predecessor's exact slot value witnesses against its structural projection;
5. instantiate the invariant with that predecessor's terms; and
6. establish the instantiated proposition from that predecessor's own `CheckState` evidence/decision authority.

The unchanged six-case `test/Phase1JoinLoopInvariantMain.hs` corpus covers:

1. every join predecessor establishes the exact invariant;
2. structural join compatibility without required evidence rejects;
3. path-local join evidence cannot leak to another predecessor;
4. loop initial entry and backedge both establish the exact invariant;
5. a structurally valid backedge without invariant evidence rejects; and
6. a definitionally trivial invariant requires no fabricated evidence.

## Residual boundary

This is semantic certification, not implementation refinement. Rocq kernel/toolchain correctness remains trusted. Concrete `Map`/`Set` representation, source-to-Systems state-slot and predecessor identity correspondence, exact proposition/term representation and substitution, focusing/decision-procedure correctness outside their already owned obligations, evidence producer truth/competence, diagnostic ordering, and Haskell implementation equivalence remain explicit boundaries.

Automatic synthesis of nontrivial invariants is outside this theorem: Phil checks declared/provided invariants and their evidence.
