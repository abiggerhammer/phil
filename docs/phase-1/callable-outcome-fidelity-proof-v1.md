# Phase 1 callable outcome fidelity proof v1

## Obligation

`PHIL-CALL-OUTCOME-001` certifies the bounded CALL-018 semantic rule that a checked callable interface preserves the exact caller-visible outcome domain and the exact branch-sensitive semantic categories attached to each outcome.

The proof is intentionally normalized. It starts after concrete list normalization has produced one exact outcome-class domain, and represents each branch-sensitive semantic category by a canonical identity. This makes the semantic theorem independent of Haskell container implementation details while preserving the distinctions that CALL-018 exists to protect.

## Certified claims

`proof/Phil/Core/CallableOutcomeFidelity.v` proves that:

- a different normalized outcome-class domain rejects exactly rather than reclassifying a branch;
- an exact class domain delegates to the branch checker unchanged;
- branch-sensitive state identity must match exactly;
- the callee transition must match exactly;
- a missing residual obligation found in another semantic bucket rejects as an exact reclassification into postconditions, assumptions, effects, or discharged facts;
- a missing residual obligation not accounted for by such a reclassification still rejects as a residual-obligation mismatch;
- even an `ResidualExact` disposition requires exact residual-set identity;
- postconditions, assumptions, effects, and discharged facts remain distinct exact categories and each mismatches independently;
- an exact branch is accepted; and
- any successful branch check implies exact state, transition, residual disposition, residual obligations, postconditions, assumptions, effects, and discharged facts.

This composes with the already Certified `PHIL-CALL-LIFE-001` callee-lifecycle semantics and `PHIL-RES-OBL-001` obligation-preservation semantics. It does not widen either predecessor theorem.

## Correspondence pressure

The dedicated workflow also typechecks the unchanged production checker and reruns the unchanged 10-case CALL-018 corpus in `test/Phase1CallableOutcomeFidelityMain.hs`. Those cases exercise exact outcome-domain preservation, branch state, callee transition, postconditions, all four residual-obligation laundering destinations, and silent residual dropping.

## Explicit residual boundary

This is semantic certification, not implementation refinement. The following remain explicit correspondence or TCB boundaries:

- Rocq kernel and toolchain correctness;
- concrete Haskell `CallableOutcomeClass`, `CallableFailure`, `CallableOutcomeState`, `CallableOutcomeAtom`, `CalleeTransition`, `Text`, and `Outcome` equality/representation;
- list normalization and duplicate-outcome detection;
- `Data.Map` / `Data.Set` membership, ordering, and extensional semantics;
- concrete computation of the first missing residual obligation and its exact reclassification bucket;
- exact Haskell diagnostic reconstruction and precedence;
- correspondence of the production Haskell checker to this normalized model; and
- truth and competence of propositions/evidence carried by the preserved semantic categories.

No production Haskell behavior is changed by this proof tranche.

Baseline: `c184f909943789e52f519fb9d3b1165a231c717b`.
