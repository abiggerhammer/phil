# PHIL-SURFACE-BINDER-SCOPE-001 aggregate closeout and production binding

This closeout binds the complete Grammar-v1 binder-scope obligation to the production Surface implementation.

## Why an aggregate is necessary

The bounded SURF-009 proof work was intentionally split by lexical lifetime rule rather than forced into one large theorem. The final obligation is therefore the conjunction of all bounded tranches plus an independent check that the production binder inventory has not grown beyond those tranches.

The aggregate Rocq theorem imports and requires all of:

- term/local binder core;
- generic-static binder identity/resolution;
- let/pattern binders;
- match/decide/offer case-arm binders;
- borrow-view binders;
- join-state binders;
- loop-state binders;
- semantic refinement binders;
- protocol message/branch-payload binders; and
- callable outcome-state binders.

## Production `GrammarV1BinderKind` inventory

The production enum currently contains exactly fourteen term-binder constructors:

1. `GrammarV1FunctionParameterBinder`
2. `GrammarV1CallableParameterBinder`
3. `GrammarV1CallableOutcomeStateBinder`
4. `GrammarV1ClaimParameterBinder`
5. `GrammarV1ComponentParameterBinder`
6. `GrammarV1ClosureParameterBinder`
7. `GrammarV1RefinementBinder`
8. `GrammarV1LetPatternBinder`
9. `GrammarV1MatchArmBinder`
10. `GrammarV1BorrowViewBinder`
11. `GrammarV1JoinStateBinder`
12. `GrammarV1LoopStateBinder`
13. `GrammarV1ProtocolMessageBinder`
14. `GrammarV1ProtocolBranchPayloadBinder`

`Phase1GrammarV1BinderScopeAggregateMain.hs` maps every constructor exhaustively to one certified bounded tranche. The closeout gate compiles that mapping with `-Wincomplete-patterns -Werror`. A future constructor added to `GrammarV1BinderKind` therefore fails the permanent closeout gate until a corresponding proof/production-binding decision is made.

Generic-static binders are deliberately absent from that enum because they inhabit the separate `GenericStaticParameterKey` identity domain. The aggregate imports `SurfaceGenericBinderScope.v` and replays the generic binder plus generic/term composition corpora separately.

## Production-binding gate

The permanent closeout workflow:

1. recompiles `BindingSemantics.v`;
2. compiles every SURF-009 bounded Rocq tranche in dependency order;
3. compiles the aggregate theorem;
4. strict-typechecks the production binder authorities and the exhaustive constructor inventory;
5. replays the permanent focused corpora for:
   - term/closure/header binders;
   - generic-static and generic/term scope composition;
   - let/pattern binders;
   - case arms;
   - borrow views;
   - join/loop state;
   - semantic refinements;
   - protocol binders; and
   - callable outcome state;
6. records SHA-256 identities for the aggregate proof, all bounded proof sources, the production binder authorities, and the aggregate inventory test.

The existing Phase 1 surface-grammar workflow remains the broader parser/elaboration regression gate. This closeout workflow is the narrow permanent production-binding gate for `PHIL-SURFACE-BINDER-SCOPE-001`.

## Certified claim

Subject to the explicit correspondence/TCB boundaries of the imported tranches, every current Grammar-v1 production binder family is covered by a bounded SURF-009 proof, uses the declaration-rooted monotonic identity discipline where applicable, and is tied to its focused executable regression corpus.

The aggregate does **not** claim parser correctness, category-specific semantic checker truth, resource/loan semantics, protocol duality, proposition focusing correctness, GHC correctness, or Rocq kernel/toolchain correctness beyond their existing independent authorities.

## Status

On a fully green exact head, `PHIL-SURFACE-BINDER-SCOPE-001` may be treated as **Certified / production-bound**. Any future production binder-kind addition must reopen this inventory or fail the closeout gate.
