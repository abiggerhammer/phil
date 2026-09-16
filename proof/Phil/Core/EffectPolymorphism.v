From Stdlib Require Import Lists.List.

From Phil.Core Require Import EffectSubject.

Import ListNotations.

(*
  PHIL-EFFECT-POLY-001 — bounded effect-set polymorphism.

  This proof owns only semantic bounded instantiation of an Effects parameter.
  Callable latency/invocation remains imported from the already certified
  CALL-EFFECT path.  Effect members are whole subject-aware
  SemanticEffectIdentity values from PHIL-EFFECT-SUBJECT-001, so membership and
  subset reasoning cannot silently erase or retarget subjects.
*)

Definition SemanticEffectSet : Type := list SemanticEffectIdentity.

Definition semanticEffectSetSubset
  (actual upper : SemanticEffectSet) : Prop :=
  forall effect,
    In effect actual ->
    In effect upper.

Record SemanticEffectSetParameterBound : Type := {
  semanticEffectSetParameterKey : nat;
  semanticEffectSetUpper : SemanticEffectSet
}.

Record CheckedSemanticEffectSetInstantiation : Type := {
  checkedEffectSetParameterKey : nat;
  checkedEffectSetActual : SemanticEffectSet;
  checkedEffectSetUpper : SemanticEffectSet
}.

Inductive CheckedBoundedEffectSetInstantiation
  : SemanticEffectSetParameterBound -> nat -> SemanticEffectSet ->
    CheckedSemanticEffectSetInstantiation -> Prop :=
| CheckedBoundedEffectSetInstantiationAccepted :
    forall bound actualKey actual,
      actualKey = semanticEffectSetParameterKey bound ->
      semanticEffectSetSubset actual (semanticEffectSetUpper bound) ->
      CheckedBoundedEffectSetInstantiation
        bound actualKey actual
        {| checkedEffectSetParameterKey := semanticEffectSetParameterKey bound;
           checkedEffectSetActual := actual;
           checkedEffectSetUpper := semanticEffectSetUpper bound |}.

Theorem checked_effect_set_parameter_identity_exact :
  forall bound actualKey actual checked,
    CheckedBoundedEffectSetInstantiation bound actualKey actual checked ->
    checkedEffectSetParameterKey checked =
      semanticEffectSetParameterKey bound.
Proof.
  intros bound actualKey actual checked Hchecked.
  inversion Hchecked; subst.
  reflexivity.
Qed.

Theorem checked_effect_set_actual_is_exact :
  forall bound actualKey actual checked,
    CheckedBoundedEffectSetInstantiation bound actualKey actual checked ->
    checkedEffectSetActual checked = actual.
Proof.
  intros bound actualKey actual checked Hchecked.
  inversion Hchecked; subst.
  reflexivity.
Qed.

Theorem checked_effect_set_upper_bound_is_preserved :
  forall bound actualKey actual checked,
    CheckedBoundedEffectSetInstantiation bound actualKey actual checked ->
    checkedEffectSetUpper checked = semanticEffectSetUpper bound.
Proof.
  intros bound actualKey actual checked Hchecked.
  inversion Hchecked; subst.
  reflexivity.
Qed.

Theorem checked_effect_set_never_widens :
  forall bound actualKey actual checked,
    CheckedBoundedEffectSetInstantiation bound actualKey actual checked ->
    semanticEffectSetSubset
      (checkedEffectSetActual checked)
      (semanticEffectSetUpper bound).
Proof.
  intros bound actualKey actual checked Hchecked.
  inversion Hchecked; subst.
  assumption.
Qed.

Theorem exact_upper_bound_instantiation_is_accepted :
  forall bound,
    CheckedBoundedEffectSetInstantiation
      bound
      (semanticEffectSetParameterKey bound)
      (semanticEffectSetUpper bound)
      {| checkedEffectSetParameterKey := semanticEffectSetParameterKey bound;
         checkedEffectSetActual := semanticEffectSetUpper bound;
         checkedEffectSetUpper := semanticEffectSetUpper bound |}.
Proof.
  intros bound.
  constructor.
  - reflexivity.
  - intros effect Heffect.
    exact Heffect.
Qed.

Theorem narrower_effect_set_instantiation_is_accepted :
  forall bound actual,
    semanticEffectSetSubset actual (semanticEffectSetUpper bound) ->
    CheckedBoundedEffectSetInstantiation
      bound
      (semanticEffectSetParameterKey bound)
      actual
      {| checkedEffectSetParameterKey := semanticEffectSetParameterKey bound;
         checkedEffectSetActual := actual;
         checkedEffectSetUpper := semanticEffectSetUpper bound |}.
Proof.
  intros bound actual Hsubset.
  constructor.
  - reflexivity.
  - exact Hsubset.
Qed.

Theorem widening_effect_set_instantiation_is_rejected :
  forall bound actualKey actual effect,
    In effect actual ->
    ~ In effect (semanticEffectSetUpper bound) ->
    ~ exists checked,
        CheckedBoundedEffectSetInstantiation bound actualKey actual checked.
Proof.
  intros bound actualKey actual effect Hactual HnotUpper [checked Hchecked].
  pose proof
    (checked_effect_set_never_widens
      bound actualKey actual checked Hchecked)
    as Hsubset.
  pose proof
    (checked_effect_set_actual_is_exact
      bound actualKey actual checked Hchecked)
    as HactualExact.
  apply HnotUpper.
  apply Hsubset.
  rewrite HactualExact.
  exact Hactual.
Qed.

Theorem checked_effect_member_preserves_full_semantic_identity :
  forall bound actualKey actual checked effect,
    CheckedBoundedEffectSetInstantiation bound actualKey actual checked ->
    In effect (checkedEffectSetActual checked) ->
    exists upperEffect,
      In upperEffect (semanticEffectSetUpper bound) /\
      semanticEffectLabel upperEffect = semanticEffectLabel effect /\
      semanticEffectSubjects upperEffect = semanticEffectSubjects effect.
Proof.
  intros bound actualKey actual checked effect Hchecked Heffect.
  pose proof
    (checked_effect_set_never_widens
      bound actualKey actual checked Hchecked)
    as Hsubset.
  exists effect.
  repeat split.
  - apply Hsubset.
    exact Heffect.
  - reflexivity.
  - reflexivity.
Qed.

Definition instantiatedEffectSetOccurrence
  (checked : CheckedSemanticEffectSetInstantiation)
  (effect : SemanticEffectIdentity) : Prop :=
  In effect (checkedEffectSetActual checked).

Theorem instantiated_effect_occurrence_cannot_invent_subject_identity :
  forall bound actualKey actual checked effect,
    CheckedBoundedEffectSetInstantiation bound actualKey actual checked ->
    instantiatedEffectSetOccurrence checked effect ->
    exists upperEffect,
      In upperEffect (semanticEffectSetUpper bound) /\
      semanticEffectLabel upperEffect = semanticEffectLabel effect /\
      semanticEffectSubjects upperEffect = semanticEffectSubjects effect.
Proof.
  intros bound actualKey actual checked effect Hchecked Hoccurs.
  unfold instantiatedEffectSetOccurrence in Hoccurs.
  eapply checked_effect_member_preserves_full_semantic_identity; eauto.
Qed.
