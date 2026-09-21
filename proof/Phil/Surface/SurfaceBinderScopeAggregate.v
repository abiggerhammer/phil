From Phil.Surface Require Import
  SurfaceBinderScopeCore
  SurfaceGenericBinderScope
  SurfaceLetPatternScope
  SurfaceCaseArmScope
  SurfaceBorrowViewScope
  SurfaceJoinStateScope
  SurfaceLoopStateScope
  SurfaceRefinementBinderScope
  SurfaceProtocolBinderScope
  SurfaceCallableOutcomeStateScope.

(*
  PHIL-SURFACE-BINDER-SCOPE-001 aggregate closeout.

  Each imported module owns one bounded Surface binder-scope tranche.  This
  aggregate does not weaken or reinterpret those theorem boundaries; it states
  that SURF-009 closeout requires every tranche simultaneously, including the
  separate generic-static identity domain.

  Concrete Haskell constructor coverage is bound by the companion exhaustive
  production inventory test.  New production binder kinds therefore cannot be
  silently admitted merely because this Rocq record remains unchanged.
*)

Record SurfaceBinderScopeAggregateFacts : Type :=
  mkSurfaceBinderScopeAggregateFacts {
    aggregateTermBinderFacts : SurfaceTermBinderScopeFacts;
    aggregateGenericBinderFacts : SurfaceGenericBinderScopeFacts;
    aggregateLetPatternFacts : SurfaceLetPatternScopeFacts;
    aggregateCaseArmFacts : SurfaceCaseArmScopeFacts;
    aggregateBorrowViewFacts : SurfaceBorrowViewScopeFacts;
    aggregateJoinStateFacts : SurfaceJoinStateScopeFacts;
    aggregateLoopStateFacts : SurfaceLoopStateScopeFacts;
    aggregateRefinementFacts : SurfaceRefinementBinderScopeFacts;
    aggregateProtocolFacts : SurfaceProtocolBinderScopeFacts;
    aggregateCallableOutcomeStateFacts : SurfaceCallableOutcomeStateScopeFacts
  }.

Definition SurfaceBinderScopeAggregateValid
  (facts : SurfaceBinderScopeAggregateFacts) : Prop :=
  SurfaceTermBinderScopeValid (aggregateTermBinderFacts facts) /\
  SurfaceGenericBinderScopeValid (aggregateGenericBinderFacts facts) /\
  SurfaceLetPatternScopeValid (aggregateLetPatternFacts facts) /\
  SurfaceCaseArmScopeValid (aggregateCaseArmFacts facts) /\
  SurfaceBorrowViewScopeValid (aggregateBorrowViewFacts facts) /\
  SurfaceJoinStateScopeValid (aggregateJoinStateFacts facts) /\
  SurfaceLoopStateScopeValid (aggregateLoopStateFacts facts) /\
  SurfaceRefinementBinderScopeValid (aggregateRefinementFacts facts) /\
  SurfaceProtocolBinderScopeValid (aggregateProtocolFacts facts) /\
  SurfaceCallableOutcomeStateScopeValid
    (aggregateCallableOutcomeStateFacts facts).

Theorem surface_binder_scope_aggregate_requires_every_bounded_tranche :
  forall facts,
    SurfaceBinderScopeAggregateValid facts ->
    SurfaceTermBinderScopeValid (aggregateTermBinderFacts facts) /\
    SurfaceGenericBinderScopeValid (aggregateGenericBinderFacts facts) /\
    SurfaceLetPatternScopeValid (aggregateLetPatternFacts facts) /\
    SurfaceCaseArmScopeValid (aggregateCaseArmFacts facts) /\
    SurfaceBorrowViewScopeValid (aggregateBorrowViewFacts facts) /\
    SurfaceJoinStateScopeValid (aggregateJoinStateFacts facts) /\
    SurfaceLoopStateScopeValid (aggregateLoopStateFacts facts) /\
    SurfaceRefinementBinderScopeValid (aggregateRefinementFacts facts) /\
    SurfaceProtocolBinderScopeValid (aggregateProtocolFacts facts) /\
    SurfaceCallableOutcomeStateScopeValid
      (aggregateCallableOutcomeStateFacts facts).
Proof.
  intros facts Hvalid.
  exact Hvalid.
Qed.

Theorem surface_binder_scope_aggregate_constructs_only_from_all_tranches :
  forall termFacts genericFacts letFacts caseFacts borrowFacts
         joinFacts loopFacts refinementFacts protocolFacts outcomeFacts,
    SurfaceTermBinderScopeValid termFacts ->
    SurfaceGenericBinderScopeValid genericFacts ->
    SurfaceLetPatternScopeValid letFacts ->
    SurfaceCaseArmScopeValid caseFacts ->
    SurfaceBorrowViewScopeValid borrowFacts ->
    SurfaceJoinStateScopeValid joinFacts ->
    SurfaceLoopStateScopeValid loopFacts ->
    SurfaceRefinementBinderScopeValid refinementFacts ->
    SurfaceProtocolBinderScopeValid protocolFacts ->
    SurfaceCallableOutcomeStateScopeValid outcomeFacts ->
    SurfaceBinderScopeAggregateValid
      (mkSurfaceBinderScopeAggregateFacts
        termFacts
        genericFacts
        letFacts
        caseFacts
        borrowFacts
        joinFacts
        loopFacts
        refinementFacts
        protocolFacts
        outcomeFacts).
Proof.
  intros.
  repeat split; assumption.
Qed.
