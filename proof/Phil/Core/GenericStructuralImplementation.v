From Stdlib Require Import Bool.Bool Lists.List.

From Phil.Core Require Import GenericStructural.

(*
  PHIL-GEN-STRUCT-IMPL-001 — executable GEN-001–003 production kernel.

  The certified PHIL-GEN-STRUCT-001 model is already executable: abstract-value
  uses accumulate exactly two structural permissions and concrete modes either
  satisfy those permissions or do not.  This refinement layer therefore does
  not introduce a second semantic relation.  It adds only the exact diagnostic
  decision needed by production and proves that acceptance is equivalent to
  the certified modeSatisfiesRequirements predicate.

  Production GenericValueParameterKey/Text identity, multi-parameter Map
  grouping, and Set representation remain explicit bridge obligations for the
  later binding tranche.  Those bridges may only reject; they may not turn an
  extracted rejection into acceptance.
*)

Inductive GenericStructuralActualDecision : Type :=
| GenericStructuralActualAccepted
| GenericStructuralActualMissingWeakening
| GenericStructuralActualMissingContraction.

Definition decideGenericStructuralActual
  (mode : Mode)
  (requirements : GenericStructuralRequirements)
  : GenericStructuralActualDecision :=
  if andb
      (requiresWeakening requirements)
      (negb (modeAllowsStructuralPermission mode WeakeningPermission))
  then GenericStructuralActualMissingWeakening
  else if andb
      (requiresContraction requirements)
      (negb (modeAllowsStructuralPermission mode ContractionPermission))
  then GenericStructuralActualMissingContraction
  else GenericStructuralActualAccepted.

Definition genericStructuralActualAcceptedb
  (decision : GenericStructuralActualDecision) : bool :=
  match decision with
  | GenericStructuralActualAccepted => true
  | _ => false
  end.

Theorem generic_structural_actual_acceptedb_true_iff :
  forall decision,
    genericStructuralActualAcceptedb decision = true <->
    decision = GenericStructuralActualAccepted.
Proof.
  intros decision.
  destruct decision; cbn; split; intro H; try reflexivity; try discriminate.
Qed.

Theorem generic_structural_decision_accept_iff_certified_satisfaction :
  forall mode requirements,
    decideGenericStructuralActual mode requirements =
      GenericStructuralActualAccepted <->
    modeSatisfiesRequirements mode requirements = true.
Proof.
  intros mode [weakening contraction].
  destruct mode, weakening, contraction; cbn; split; intro H;
    try reflexivity; try discriminate.
Qed.

Theorem generic_structural_decision_reject_iff_not_certified_satisfaction :
  forall mode requirements,
    decideGenericStructuralActual mode requirements <>
      GenericStructuralActualAccepted <->
    modeSatisfiesRequirements mode requirements <> true.
Proof.
  intros mode requirements.
  split.
  - intros Hreject Hsatisfies.
    apply Hreject.
    apply (proj2
      (generic_structural_decision_accept_iff_certified_satisfaction
        mode requirements)).
    exact Hsatisfies.
  - intros Hnot Haccept.
    apply Hnot.
    apply (proj1
      (generic_structural_decision_accept_iff_certified_satisfaction
        mode requirements)).
    exact Haccept.
Qed.

Theorem generic_structural_missing_weakening_is_exact :
  forall mode requirements,
    decideGenericStructuralActual mode requirements =
      GenericStructuralActualMissingWeakening ->
    requiresWeakening requirements = true /\
    modeAllowsStructuralPermission mode WeakeningPermission = false.
Proof.
  intros mode [weakening contraction].
  destruct mode, weakening, contraction; cbn; intro H;
    try discriminate; split; reflexivity.
Qed.

Theorem generic_structural_missing_contraction_is_exact :
  forall mode requirements,
    decideGenericStructuralActual mode requirements =
      GenericStructuralActualMissingContraction ->
    requiresContraction requirements = true /\
    modeAllowsStructuralPermission mode ContractionPermission = false /\
    (requiresWeakening requirements = false \/
      modeAllowsStructuralPermission mode WeakeningPermission = true).
Proof.
  intros mode [weakening contraction].
  destruct mode, weakening, contraction; cbn; intro H;
    try discriminate; repeat split; try reflexivity; try (left; reflexivity);
    try (right; reflexivity).
Qed.

Theorem extracted_transfer_inference_is_certified :
  inferGenericStructuralRequirements [TransferGenericValue] = emptyRequirements.
Proof.
  exact transfer_only_has_empty_requirements.
Qed.

Theorem extracted_discard_inference_is_certified :
  inferGenericStructuralRequirements [DiscardGenericValue] =
    mkRequirements true false.
Proof.
  exact discard_requires_exactly_weakening_from_empty.
Qed.

Theorem extracted_duplicate_inference_is_certified :
  inferGenericStructuralRequirements [DuplicateGenericValue] =
    mkRequirements false true.
Proof.
  exact duplication_requires_exactly_contraction_from_empty.
Qed.

Theorem extracted_combined_inference_is_certified :
  inferGenericStructuralRequirements
    [DuplicateGenericValue; DiscardGenericValue] =
    mkRequirements true true.
Proof.
  exact duplicate_and_discard_require_both_permissions.
Qed.

Theorem extracted_two_use_inference_is_order_independent :
  forall first second,
    inferGenericStructuralRequirements [first; second] =
    inferGenericStructuralRequirements [second; first].
Proof.
  exact two_use_inference_is_order_independent.
Qed.
