From Stdlib Require Import Bool.Bool Lists.List.

Import ListNotations.

(*
  PHIL-CALL-EFFECT-001 — callable invocation effect propagation and public bound.

  Effects are modeled extensionally as predicates over opaque semantic effect
  identities. Merely possessing, passing, storing, or returning a callable is
  effect-neutral; reachable invocation unions the callable's public may-effect
  bound into the enclosing footprint. A checked implementation footprint may be
  narrower than its stabilized public bound but may never exceed it.

  Concrete Text effect keys, Haskell Set union/difference/canonicalization,
  traversal ordering, and exact diagnostics remain correspondence boundaries.
*)

Definition EffectSet : Type := nat -> bool.

Definition emptyEffectSet : EffectSet := fun _ => false.

Definition effectUnion (first second : EffectSet) : EffectSet :=
  fun effect => orb (first effect) (second effect).

Definition effectSubset (smaller larger : EffectSet) : Prop :=
  forall effect,
    smaller effect = true ->
    larger effect = true.

Definition sameEffectSet (first second : EffectSet) : Prop :=
  forall effect, first effect = second effect.

Definition effectDelta (inferred public : EffectSet) : EffectSet :=
  fun effect => andb (inferred effect) (negb (public effect)).

Inductive CallableUse : Type :=
| PossessCallable : EffectSet -> CallableUse
| PassCallable : EffectSet -> CallableUse
| StoreCallable : EffectSet -> CallableUse
| ReturnCallable : EffectSet -> CallableUse
| InvokeCallable : EffectSet -> CallableUse.

Definition addCallableUse
  (effects : EffectSet)
  (use : CallableUse) : EffectSet :=
  match use with
  | InvokeCallable publicBound => effectUnion effects publicBound
  | PossessCallable _ => effects
  | PassCallable _ => effects
  | StoreCallable _ => effects
  | ReturnCallable _ => effects
  end.

Definition inferReachableCallableEffects
  (uses : list CallableUse) : EffectSet :=
  fold_left addCallableUse uses emptyEffectSet.

Record CheckedEffectBound : Type := mkCheckedEffectBound {
  checkedEffectInterface : nat;
  checkedInferredEffects : EffectSet;
  checkedPublicEffects : EffectSet
}.

Definition checkedEffectBoundAllowed
  (interface : nat)
  (inferred public : EffectSet)
  (checked : CheckedEffectBound) : Prop :=
  checkedEffectInterface checked = interface /\
  sameEffectSet (checkedInferredEffects checked) inferred /\
  sameEffectSet (checkedPublicEffects checked) public /\
  effectSubset inferred public.

Theorem possession_is_effect_neutral :
  forall publicBound effect,
    inferReachableCallableEffects [PossessCallable publicBound] effect = false.
Proof.
  reflexivity.
Qed.

Theorem pass_store_return_are_effect_neutral :
  forall publicBound effect,
    inferReachableCallableEffects
      [ PassCallable publicBound
      ; StoreCallable publicBound
      ; ReturnCallable publicBound
      ] effect = false.
Proof.
  reflexivity.
Qed.

Theorem reachable_invocation_adds_exact_public_bound :
  forall publicBound,
    sameEffectSet
      (inferReachableCallableEffects [InvokeCallable publicBound])
      publicBound.
Proof.
  intros publicBound effect.
  unfold inferReachableCallableEffects, addCallableUse, effectUnion, emptyEffectSet.
  simpl.
  destruct (publicBound effect); reflexivity.
Qed.

Theorem repeated_invocation_is_idempotent :
  forall publicBound,
    sameEffectSet
      (inferReachableCallableEffects
        [InvokeCallable publicBound; InvokeCallable publicBound])
      publicBound.
Proof.
  intros publicBound effect.
  unfold inferReachableCallableEffects, addCallableUse, effectUnion, emptyEffectSet.
  simpl.
  destruct (publicBound effect); reflexivity.
Qed.

Theorem two_invocation_effect_union_is_order_independent :
  forall firstBound secondBound,
    sameEffectSet
      (inferReachableCallableEffects
        [InvokeCallable firstBound; InvokeCallable secondBound])
      (inferReachableCallableEffects
        [InvokeCallable secondBound; InvokeCallable firstBound]).
Proof.
  intros firstBound secondBound effect.
  unfold inferReachableCallableEffects, addCallableUse, effectUnion, emptyEffectSet.
  simpl.
  destruct (firstBound effect), (secondBound effect); reflexivity.
Qed.

Theorem effect_union_is_commutative :
  forall first second,
    sameEffectSet (effectUnion first second) (effectUnion second first).
Proof.
  intros first second effect.
  unfold effectUnion.
  destruct (first effect), (second effect); reflexivity.
Qed.

Theorem effect_union_is_associative :
  forall first second third,
    sameEffectSet
      (effectUnion (effectUnion first second) third)
      (effectUnion first (effectUnion second third)).
Proof.
  intros first second third effect.
  unfold effectUnion.
  destruct (first effect), (second effect), (third effect); reflexivity.
Qed.

Theorem every_effect_set_is_subset_of_itself :
  forall effects,
    effectSubset effects effects.
Proof.
  intros effects effect Hpresent.
  exact Hpresent.
Qed.

Theorem empty_footprint_is_subset_of_every_public_bound :
  forall public,
    effectSubset emptyEffectSet public.
Proof.
  intros public effect Hpresent.
  discriminate.
Qed.

Theorem subset_footprint_constructs_checked_effect_bound :
  forall interface inferred public,
    effectSubset inferred public ->
    checkedEffectBoundAllowed interface inferred public
      (mkCheckedEffectBound interface inferred public).
Proof.
  intros interface inferred public Hsubset.
  unfold checkedEffectBoundAllowed.
  split.
  - reflexivity.
  - split.
    + intros effect. reflexivity.
    + split.
      * intros effect. reflexivity.
      * exact Hsubset.
Qed.

Theorem accepted_effect_check_preserves_interface_identity :
  forall interface inferred public checked,
    checkedEffectBoundAllowed interface inferred public checked ->
    checkedEffectInterface checked = interface.
Proof.
  intros interface inferred public checked Hchecked.
  unfold checkedEffectBoundAllowed in Hchecked.
  destruct Hchecked as [Hinterface _].
  exact Hinterface.
Qed.

Theorem accepted_effect_check_preserves_inferred_footprint :
  forall interface inferred public checked,
    checkedEffectBoundAllowed interface inferred public checked ->
    sameEffectSet (checkedInferredEffects checked) inferred.
Proof.
  intros interface inferred public checked Hchecked.
  unfold checkedEffectBoundAllowed in Hchecked.
  destruct Hchecked as [_ [Hinferred _]].
  exact Hinferred.
Qed.

Theorem accepted_effect_check_preserves_stabilized_public_bound :
  forall interface inferred public checked,
    checkedEffectBoundAllowed interface inferred public checked ->
    sameEffectSet (checkedPublicEffects checked) public.
Proof.
  intros interface inferred public checked Hchecked.
  unfold checkedEffectBoundAllowed in Hchecked.
  destruct Hchecked as [_ [_ [Hpublic _]]].
  exact Hpublic.
Qed.

Theorem narrower_body_may_satisfy_wider_public_bound :
  exists inferred public : EffectSet,
    effectSubset inferred public /\
    exists effect, inferred effect = false /\ public effect = true.
Proof.
  exists emptyEffectSet, (fun _ => true).
  split.
  - apply empty_footprint_is_subset_of_every_public_bound.
  - exists 0.
    split; reflexivity.
Qed.

Theorem undeclared_effect_witness_rejects_bound :
  forall inferred public effect,
    inferred effect = true ->
    public effect = false ->
    ~ effectSubset inferred public.
Proof.
  intros inferred public effect Hinferred Hpublic Hsubset.
  specialize (Hsubset effect Hinferred).
  rewrite Hpublic in Hsubset.
  discriminate.
Qed.

Theorem effect_delta_is_exact_undeclared_set :
  forall inferred public effect,
    effectDelta inferred public effect = true <->
    inferred effect = true /\ public effect = false.
Proof.
  intros inferred public effect.
  split.
  - intro Hdelta.
    unfold effectDelta in Hdelta.
    apply andb_true_iff in Hdelta as [Hinferred HnotPublic].
    apply negb_true_iff in HnotPublic.
    split; assumption.
  - intros [Hinferred Hpublic].
    unfold effectDelta.
    apply andb_true_iff.
    split.
    + exact Hinferred.
    + apply negb_true_iff.
      exact Hpublic.
Qed.

Theorem effect_neutral_higher_order_use_fits_pure_bound :
  forall publicBound,
    effectSubset
      (inferReachableCallableEffects
        [ PossessCallable publicBound
        ; PassCallable publicBound
        ; StoreCallable publicBound
        ; ReturnCallable publicBound
        ])
      emptyEffectSet.
Proof.
  intros publicBound effect Hpresent.
  discriminate.
Qed.

Theorem invocation_widening_cannot_silently_revise_enclosing_bound :
  forall invokedBound enclosingBound effect,
    invokedBound effect = true ->
    enclosingBound effect = false ->
    ~ effectSubset
      (inferReachableCallableEffects [InvokeCallable invokedBound])
      enclosingBound.
Proof.
  intros invokedBound enclosingBound effect Hinvoked Henclosing Hsubset.
  apply (undeclared_effect_witness_rejects_bound
    (inferReachableCallableEffects [InvokeCallable invokedBound])
    enclosingBound effect).
  - unfold inferReachableCallableEffects, addCallableUse, effectUnion, emptyEffectSet.
    simpl.
    rewrite Hinvoked.
    reflexivity.
  - exact Henclosing.
  - exact Hsubset.
Qed.
