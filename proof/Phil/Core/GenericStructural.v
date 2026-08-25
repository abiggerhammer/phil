From Stdlib Require Import Lists.List Bool.Bool.

Import ListNotations.

(*
  PHIL-GEN-STRUCT-001 — generic structural polymorphism.

  This normalized model captures the structural algebra implemented by
  Phil.Core.Generic for one already-resolved abstract value parameter.
  Transfer requires no additional structural permission; discard requires
  weakening; duplication requires contraction. Requirements accumulate as a
  canonical set (represented here by two booleans), and a concrete structural
  mode must satisfy every induced permission.

  Concrete Haskell GenericValueParameterKey/Text identity, Map/Set
  normalization and traversal, and correspondence from checked Core use events
  to this normalized model remain explicit implementation boundaries.
*)

Inductive Mode : Type :=
| Unrestricted
| Affine
| Linear.

Inductive StructuralPermission : Type :=
| WeakeningPermission
| ContractionPermission.

Inductive GenericStructuralUse : Type :=
| TransferGenericValue
| DiscardGenericValue
| DuplicateGenericValue.

Record GenericStructuralRequirements : Type := mkRequirements {
  requiresWeakening : bool;
  requiresContraction : bool
}.

Definition emptyRequirements : GenericStructuralRequirements :=
  mkRequirements false false.

Definition addStructuralUse
  (use : GenericStructuralUse)
  (requirements : GenericStructuralRequirements)
  : GenericStructuralRequirements :=
  match use with
  | TransferGenericValue => requirements
  | DiscardGenericValue =>
      mkRequirements true (requiresContraction requirements)
  | DuplicateGenericValue =>
      mkRequirements (requiresWeakening requirements) true
  end.

Definition inferGenericStructuralRequirements
  (uses : list GenericStructuralUse) : GenericStructuralRequirements :=
  fold_left (fun requirements use => addStructuralUse use requirements)
    uses emptyRequirements.

Definition modeAllowsStructuralPermission
  (mode : Mode)
  (permission : StructuralPermission) : bool :=
  match mode, permission with
  | Unrestricted, _ => true
  | Affine, WeakeningPermission => true
  | Affine, ContractionPermission => false
  | Linear, _ => false
  end.

Definition modeSatisfiesRequirements
  (mode : Mode)
  (requirements : GenericStructuralRequirements) : bool :=
  andb
    (if requiresWeakening requirements
     then modeAllowsStructuralPermission mode WeakeningPermission
     else true)
    (if requiresContraction requirements
     then modeAllowsStructuralPermission mode ContractionPermission
     else true).

Theorem transfer_requires_no_structural_permission :
  forall requirements,
    addStructuralUse TransferGenericValue requirements = requirements.
Proof.
  reflexivity.
Qed.

Theorem discard_induces_weakening :
  forall requirements,
    requiresWeakening
      (addStructuralUse DiscardGenericValue requirements) = true.
Proof.
  reflexivity.
Qed.

Theorem duplication_induces_contraction :
  forall requirements,
    requiresContraction
      (addStructuralUse DuplicateGenericValue requirements) = true.
Proof.
  reflexivity.
Qed.

Theorem transfer_only_has_empty_requirements :
  inferGenericStructuralRequirements [TransferGenericValue] = emptyRequirements.
Proof.
  reflexivity.
Qed.

Theorem linear_actual_satisfies_pure_transfer :
  modeSatisfiesRequirements Linear
    (inferGenericStructuralRequirements [TransferGenericValue]) = true.
Proof.
  reflexivity.
Qed.

Theorem discard_requires_exactly_weakening_from_empty :
  inferGenericStructuralRequirements [DiscardGenericValue] =
    mkRequirements true false.
Proof.
  reflexivity.
Qed.

Theorem unrestricted_satisfies_weakening :
  modeSatisfiesRequirements Unrestricted (mkRequirements true false) = true.
Proof.
  reflexivity.
Qed.

Theorem affine_satisfies_weakening :
  modeSatisfiesRequirements Affine (mkRequirements true false) = true.
Proof.
  reflexivity.
Qed.

Theorem linear_rejects_weakening :
  modeSatisfiesRequirements Linear (mkRequirements true false) = false.
Proof.
  reflexivity.
Qed.

Theorem duplication_requires_exactly_contraction_from_empty :
  inferGenericStructuralRequirements [DuplicateGenericValue] =
    mkRequirements false true.
Proof.
  reflexivity.
Qed.

Theorem unrestricted_satisfies_contraction :
  modeSatisfiesRequirements Unrestricted (mkRequirements false true) = true.
Proof.
  reflexivity.
Qed.

Theorem affine_rejects_contraction :
  modeSatisfiesRequirements Affine (mkRequirements false true) = false.
Proof.
  reflexivity.
Qed.

Theorem linear_rejects_contraction :
  modeSatisfiesRequirements Linear (mkRequirements false true) = false.
Proof.
  reflexivity.
Qed.

Theorem duplicate_and_discard_require_both_permissions :
  inferGenericStructuralRequirements
    [DuplicateGenericValue; DiscardGenericValue] =
    mkRequirements true true.
Proof.
  reflexivity.
Qed.

Theorem unrestricted_satisfies_both_permissions :
  modeSatisfiesRequirements Unrestricted (mkRequirements true true) = true.
Proof.
  reflexivity.
Qed.

Theorem affine_rejects_both_permissions :
  modeSatisfiesRequirements Affine (mkRequirements true true) = false.
Proof.
  reflexivity.
Qed.

Theorem linear_rejects_both_permissions :
  modeSatisfiesRequirements Linear (mkRequirements true true) = false.
Proof.
  reflexivity.
Qed.

Theorem structural_use_accumulation_commutes :
  forall first second requirements,
    addStructuralUse first (addStructuralUse second requirements) =
    addStructuralUse second (addStructuralUse first requirements).
Proof.
  intros first second [weakening contraction].
  destruct first, second; reflexivity.
Qed.

Theorem two_use_inference_is_order_independent :
  forall first second,
    inferGenericStructuralRequirements [first; second] =
    inferGenericStructuralRequirements [second; first].
Proof.
  intros first second.
  unfold inferGenericStructuralRequirements.
  simpl.
  apply structural_use_accumulation_commutes.
Qed.

Theorem unrestricted_satisfies_every_structural_requirement :
  forall requirements,
    modeSatisfiesRequirements Unrestricted requirements = true.
Proof.
  intros [weakening contraction].
  destruct weakening, contraction; reflexivity.
Qed.

Theorem linear_satisfies_only_empty_structural_requirements :
  forall requirements,
    modeSatisfiesRequirements Linear requirements = true ->
    requirements = emptyRequirements.
Proof.
  intros [weakening contraction] H.
  destruct weakening, contraction; simpl in H; try discriminate; reflexivity.
Qed.

Theorem affine_satisfaction_excludes_contraction :
  forall requirements,
    modeSatisfiesRequirements Affine requirements = true ->
    requiresContraction requirements = false.
Proof.
  intros [weakening contraction] H.
  destruct weakening, contraction; simpl in H; try discriminate; reflexivity.
Qed.
