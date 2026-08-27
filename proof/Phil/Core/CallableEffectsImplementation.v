From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import CallableEffects.

(*
  Executable correspondence layer for PHIL-CALL-EFFECT-001.

  Concrete SemanticEffect identity and finite-set representation remain outside
  this extracted kernel. Production supplies native Set membership/subset facts;
  the kernel owns the semantic decisions made from those facts. This avoids any
  fake serialization of Text effect identities through the normalized Rocq model.
*)

Inductive CallableUseEffectKind : Type :=
| PossessEffectUse
| PassEffectUse
| StoreEffectUse
| ReturnEffectUse
| InvokeEffectUse.

Definition callableUseEffectKind
  (use : CallableUse) : CallableUseEffectKind :=
  match use with
  | PossessCallable _ => PossessEffectUse
  | PassCallable _ => PassEffectUse
  | StoreCallable _ => StoreEffectUse
  | ReturnCallable _ => ReturnEffectUse
  | InvokeCallable _ => InvokeEffectUse
  end.

Definition callableUseEffectKindContributesPublicBound
  (kind : CallableUseEffectKind) : bool :=
  match kind with
  | InvokeEffectUse => true
  | PossessEffectUse => false
  | PassEffectUse => false
  | StoreEffectUse => false
  | ReturnEffectUse => false
  end.

Definition callableUsePublicBound
  (use : CallableUse) : EffectSet :=
  match use with
  | PossessCallable publicBound => publicBound
  | PassCallable publicBound => publicBound
  | StoreCallable publicBound => publicBound
  | ReturnCallable publicBound => publicBound
  | InvokeCallable publicBound => publicBound
  end.

Theorem callable_use_contribution_decision_agrees_with_certified :
  forall effects use effect,
    addCallableUse effects use effect =
    if callableUseEffectKindContributesPublicBound (callableUseEffectKind use)
    then effectUnion effects (callableUsePublicBound use) effect
    else effects effect.
Proof.
  intros effects use effect.
  destruct use; reflexivity.
Qed.

Inductive CallableEffectBoundDecision : Type :=
| CallableEffectBoundAccepted
| CallableEffectBoundExceeded.

Definition decideCallableEffectBound
  (subsetFact : bool) : CallableEffectBoundDecision :=
  if subsetFact
  then CallableEffectBoundAccepted
  else CallableEffectBoundExceeded.

Theorem effect_bound_decision_accepts_iff_reflected_subset :
  forall inferred public subsetFact,
    (subsetFact = true <-> effectSubset inferred public) ->
    (decideCallableEffectBound subsetFact = CallableEffectBoundAccepted <->
      effectSubset inferred public).
Proof.
  intros inferred public subsetFact Hreflect.
  split.
  - intro Hdecision.
    destruct subsetFact eqn:Hsubset; cbn in Hdecision.
    + apply (proj1 Hreflect).
      reflexivity.
    + discriminate.
  - intro Hsubset.
    assert (Hfact : subsetFact = true).
    { apply (proj2 Hreflect). exact Hsubset. }
    unfold decideCallableEffectBound.
    rewrite Hfact.
    reflexivity.
Qed.

Theorem accepted_effect_bound_decision_constructs_certified_result :
  forall interface inferred public subsetFact,
    (subsetFact = true <-> effectSubset inferred public) ->
    decideCallableEffectBound subsetFact = CallableEffectBoundAccepted ->
    checkedEffectBoundAllowed interface inferred public
      (mkCheckedEffectBound interface inferred public).
Proof.
  intros interface inferred public subsetFact Hreflect Hdecision.
  apply subset_footprint_constructs_checked_effect_bound.
  apply (proj1
    (effect_bound_decision_accepts_iff_reflected_subset
      inferred public subsetFact Hreflect)).
  exact Hdecision.
Qed.

Theorem rejected_effect_bound_decision_means_not_subset :
  forall inferred public subsetFact,
    (subsetFact = true <-> effectSubset inferred public) ->
    decideCallableEffectBound subsetFact = CallableEffectBoundExceeded ->
    ~ effectSubset inferred public.
Proof.
  intros inferred public subsetFact Hreflect Hdecision Hsubset.
  pose proof
    (proj2
      (effect_bound_decision_accepts_iff_reflected_subset
        inferred public subsetFact Hreflect)
      Hsubset) as Haccepted.
  rewrite Hdecision in Haccepted.
  discriminate.
Qed.

Definition effectDeltaBit
  (inferredPresent publicPresent : bool) : bool :=
  andb inferredPresent (negb publicPresent).

Theorem effect_delta_bit_agrees_with_certified :
  forall inferred public effect,
    effectDeltaBit (inferred effect) (public effect) =
    effectDelta inferred public effect.
Proof.
  reflexivity.
Qed.

Theorem effect_delta_bit_true_iff_undeclared :
  forall inferred public effect,
    effectDeltaBit (inferred effect) (public effect) = true <->
    inferred effect = true /\ public effect = false.
Proof.
  intros inferred public effect.
  rewrite effect_delta_bit_agrees_with_certified.
  apply effect_delta_is_exact_undeclared_set.
Qed.
