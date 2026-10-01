From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsExpressionFallbackBaseChoiceSpine
  GrammarAstGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine.

Import ListNotations.

(*
  Lift the completed shift-refined generic_requirement carrier through
  generic_requirements and its optional wrapper.

  A single explicit fuel value is shared across every list entry. Each entry
  delegates to the full thirteen-way shift-refined generic_requirement
  normalizer from the preceding slice, while the enclosing requires/{...}
  structure is preserved exactly.

  Structural Rocq surface correspondence only. This does not yet prove a
  shared derivation-driven fuel bound for generic_requirements lists, advance
  declaration consumers, change Grammar-v1, Haskell/runtime behavior,
  evaluation semantics, or make broader parser soundness/completeness claims.
  It continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1491.
*)

Fixpoint
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel
  (fuel : nat)
  (requirements :
    list Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceSpine)
  : option
      (list
        Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine) :=
  match requirements with
  | [] => Some []
  | requirement :: rest =>
      match
        phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
          fuel requirement,
        phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel
          fuel rest
      with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel_round_trip :
  forall fuel requirements refined,
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel
      fuel requirements = Some refined ->
    map
      phase1_surface_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
    map
      phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
      requirements.
Proof.
  intros fuel requirements.
  induction requirements as [|requirement rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel requirement)
      as [actual |] eqn:Hrequirement; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel
        fuel rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip.
      exact Hrequirement.
    + eapply IH.
      exact Hrest.
Qed.

Record
  Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedSpine
  : Type := {
  phase1_generic_requirements_expression_fallback_base_choice_shift_refined_spine_entries :
    list
      Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine
}.

Definition
  phase1_surface_generic_requirements_expression_fallback_base_choice_shift_refined_spine_tree
  (requirements :
    Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  PTNonterminal "generic_requirements"
    (PTSequence
      [ PTLiteral "requires";
        PTLiteral "{";
        PTRepetition
          (map
            phase1_surface_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
            (phase1_generic_requirements_expression_fallback_base_choice_shift_refined_spine_entries
              requirements));
        PTLiteral "}"
      ]).

Definition
  phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel
  (fuel : nat)
  (requirements :
    Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine)
  : option
      Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel
      fuel
      (phase1_generic_requirements_expression_fallback_base_choice_spine_entries
        requirements)
  with
  | Some entries =>
      Some
        {| phase1_generic_requirements_expression_fallback_base_choice_shift_refined_spine_entries :=
             entries |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip :
  forall fuel requirements refined,
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel requirements = Some refined ->
    phase1_surface_generic_requirements_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
    phase1_surface_generic_requirements_expression_fallback_base_choice_spine_tree
      requirements.
Proof.
  intros fuel [entries] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel
      fuel entries)
    as [actual |] eqn:Hentries; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel_round_trip
      fuel entries actual Hentries).
  reflexivity.
Qed.

Definition
  phase1_surface_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree
  (requirements :
    option
      Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  match requirements with
  | None => PTOptionalNone
  | Some value =>
      PTOptionalSome
        (phase1_surface_generic_requirements_expression_fallback_base_choice_shift_refined_spine_tree
          value)
  end.

Definition
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel
  (fuel : nat)
  (requirements :
    option Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine)
  : option
      (option
        Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedSpine) :=
  match requirements with
  | None => Some None
  | Some value =>
      match
        phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel
          fuel value
      with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel_round_trip :
  forall fuel requirements refined,
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel
      fuel requirements = Some refined ->
    phase1_surface_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree
      refined =
    phase1_surface_optional_generic_requirements_expression_fallback_base_choice_tree
      requirements.
Proof.
  intros fuel [requirements |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel requirements)
      as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip
        fuel requirements actual Hrequirements).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition
  phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option
      Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_tree
      tree
  with
  | Some requirements =>
      phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel requirements
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_generic_requirements_expression_fallback_base_choice_shift_refined_spine_tree
      refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_tree
      tree)
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  transitivity
    (phase1_surface_generic_requirements_expression_fallback_base_choice_spine_tree
      requirements).
  - eapply
      phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_tree_round_trip.
    exact Hrequirements.
Qed.

Definition
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option
      (option
        Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedSpine) :=
  match
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_tree
      tree
  with
  | Some requirements =>
      phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel
        fuel requirements
  | None => None
  end.

Theorem
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree
      refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_tree
      tree)
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  transitivity
    (phase1_surface_optional_generic_requirements_expression_fallback_base_choice_tree
      requirements).
  - eapply
      phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_tree_round_trip.
    exact Hrequirements.
Qed.
