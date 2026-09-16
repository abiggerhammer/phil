From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import EffectPolymorphism.

(*
  PHIL-EFFECT-POLY-001 — executable implementation correspondence.

  Concrete GenericStaticParameterKey equality, GenericEffectsKind recognition,
  SemanticForm decoding, finite-set representation, and diagnostics remain
  native facts.  This file owns only the ordered admission decision reflected by
  Phil.Core.EffectPolymorphism.checkBoundedEffectSetInstantiation.
*)

Inductive EffectSetInstantiationDecision : Type :=
| EffectSetInstantiationAccepted
| EffectSetInstantiationParameterKeyMismatch
| EffectSetInstantiationKindMismatch
| EffectSetInstantiationSemanticFormMalformed
| EffectSetInstantiationBoundExceeded.

Definition decideEffectSetInstantiation
  (parameterKeyMatches kindIsEffects semanticFormCanonical subsetOfUpper : bool)
  : EffectSetInstantiationDecision :=
  if parameterKeyMatches then
    if kindIsEffects then
      if semanticFormCanonical then
        if subsetOfUpper then EffectSetInstantiationAccepted
        else EffectSetInstantiationBoundExceeded
      else EffectSetInstantiationSemanticFormMalformed
    else EffectSetInstantiationKindMismatch
  else EffectSetInstantiationParameterKeyMismatch.

Definition effectSetInstantiationFactsAccepted
  (parameterKeyMatches kindIsEffects semanticFormCanonical subsetOfUpper : bool)
  : bool :=
  andb parameterKeyMatches
    (andb kindIsEffects
      (andb semanticFormCanonical subsetOfUpper)).

Definition effectSetInstantiationDecisionAccepted
  (decision : EffectSetInstantiationDecision) : bool :=
  match decision with
  | EffectSetInstantiationAccepted => true
  | _ => false
  end.

Theorem effect_set_instantiation_decision_accept_iff_all_facts :
  forall parameterKeyMatches kindIsEffects semanticFormCanonical subsetOfUpper,
    effectSetInstantiationDecisionAccepted
      (decideEffectSetInstantiation
        parameterKeyMatches kindIsEffects semanticFormCanonical subsetOfUpper)
      = true <->
    effectSetInstantiationFactsAccepted
      parameterKeyMatches kindIsEffects semanticFormCanonical subsetOfUpper
      = true.
Proof.
  intros parameterKeyMatches kindIsEffects semanticFormCanonical subsetOfUpper.
  destruct parameterKeyMatches, kindIsEffects, semanticFormCanonical, subsetOfUpper;
    simpl; split; intro H; try reflexivity; discriminate H.
Qed.

Theorem parameter_key_mismatch_rejects_first :
  forall kindIsEffects semanticFormCanonical subsetOfUpper,
    decideEffectSetInstantiation
      false kindIsEffects semanticFormCanonical subsetOfUpper =
      EffectSetInstantiationParameterKeyMismatch.
Proof.
  reflexivity.
Qed.

Theorem kind_mismatch_rejects_second :
  forall semanticFormCanonical subsetOfUpper,
    decideEffectSetInstantiation true false semanticFormCanonical subsetOfUpper =
      EffectSetInstantiationKindMismatch.
Proof.
  reflexivity.
Qed.

Theorem malformed_effect_set_rejects_before_bound_check :
  forall subsetOfUpper,
    decideEffectSetInstantiation true true false subsetOfUpper =
      EffectSetInstantiationSemanticFormMalformed.
Proof.
  reflexivity.
Qed.

Theorem widening_decision_rejects :
  decideEffectSetInstantiation true true true false =
    EffectSetInstantiationBoundExceeded.
Proof.
  reflexivity.
Qed.

Theorem exact_or_narrower_decision_accepts :
  decideEffectSetInstantiation true true true true =
    EffectSetInstantiationAccepted.
Proof.
  reflexivity.
Qed.

Theorem accepted_decision_constructs_checked_instantiation :
  forall bound actualKey actual,
    actualKey = semanticEffectSetParameterKey bound ->
    semanticEffectSetSubset actual (semanticEffectSetUpper bound) ->
    decideEffectSetInstantiation true true true true =
      EffectSetInstantiationAccepted ->
    CheckedBoundedEffectSetInstantiation
      bound actualKey actual
      {| checkedEffectSetParameterKey := semanticEffectSetParameterKey bound;
         checkedEffectSetActual := actual;
         checkedEffectSetUpper := semanticEffectSetUpper bound |}.
Proof.
  intros bound actualKey actual Hkey Hsubset Hdecision.
  constructor.
  - exact Hkey.
  - exact Hsubset.
Qed.

Theorem accepted_decision_cannot_widen_subject_aware_effects :
  forall bound actualKey actual checked effect,
    CheckedBoundedEffectSetInstantiation bound actualKey actual checked ->
    decideEffectSetInstantiation true true true true =
      EffectSetInstantiationAccepted ->
    In effect (checkedEffectSetActual checked) ->
    exists upperEffect,
      In upperEffect (semanticEffectSetUpper bound) /\
      semanticEffectLabel upperEffect = semanticEffectLabel effect /\
      semanticEffectSubjects upperEffect = semanticEffectSubjects effect.
Proof.
  intros bound actualKey actual checked effect Hchecked Hdecision Heffect.
  eapply checked_effect_member_preserves_full_semantic_identity.
  - exact Hchecked.
  - exact Heffect.
Qed.
