From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsExpressionOuterSpine
  GrammarAstGenericRequirementExpressionFallbackBaseChoiceSpine.

Import ListNotations.

(*
  Lift the fallback/base-choice-refined generic-requirement carrier through
  generic_requirements and its optional wrapper while preserving the exact
  surface parse tree.
*)

Fixpoint
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_values
  (requirements : list Phase1SurfaceGenericRequirementExpressionOuterSpine)
  : option
      (list Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceSpine) :=
  match requirements with
  | [] => Some []
  | requirement :: rest =>
      match
        phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_spine
          requirement,
        phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_values
          rest
      with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_values_round_trip :
  forall requirements refined,
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_values
      requirements = Some refined ->
    map
      phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
      refined =
      map phase1_surface_generic_requirement_expression_outer_spine_tree
        requirements.
Proof.
  intros requirements.
  induction requirements as [|requirement rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_spine
        requirement)
      as [actual |] eqn:Hrequirement; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_values
        rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_spine_round_trip.
      exact Hrequirement.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine : Type := {
  phase1_generic_requirements_expression_fallback_base_choice_spine_entries :
    list Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceSpine
}.

Definition
  phase1_surface_generic_requirements_expression_fallback_base_choice_spine_tree
  (requirements : Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine)
  : ParseTree :=
  PTNonterminal "generic_requirements"
    (PTSequence
      [ PTLiteral "requires";
        PTLiteral "{";
        PTRepetition
          (map
            phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
            (phase1_generic_requirements_expression_fallback_base_choice_spine_entries
              requirements));
        PTLiteral "}"
      ]).

Definition
  phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_spine
  (requirements : Phase1SurfaceGenericRequirementsExpressionOuterSpine)
  : option Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine :=
  match
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_values
      (phase1_generic_requirements_expression_outer_spine_entries requirements)
  with
  | Some entries =>
      Some
        {| phase1_generic_requirements_expression_fallback_base_choice_spine_entries :=
             entries |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_spine_round_trip :
  forall requirements refined,
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_spine
      requirements = Some refined ->
    phase1_surface_generic_requirements_expression_fallback_base_choice_spine_tree
      refined =
      phase1_surface_generic_requirements_expression_outer_spine_tree requirements.
Proof.
  intros [entries] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_values
      entries)
    as [actual |] eqn:Hentries; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_values_round_trip
      entries actual Hentries).
  reflexivity.
Qed.

Definition
  phase1_surface_optional_generic_requirements_expression_fallback_base_choice_tree
  (requirements :
    option Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine)
  : ParseTree :=
  match requirements with
  | None => PTOptionalNone
  | Some value =>
      PTOptionalSome
        (phase1_surface_generic_requirements_expression_fallback_base_choice_spine_tree
          value)
  end.

Definition
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice
  (requirements : option Phase1SurfaceGenericRequirementsExpressionOuterSpine)
  : option
      (option Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine) :=
  match requirements with
  | None => Some None
  | Some value =>
      match
        phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_spine
          value
      with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_round_trip :
  forall requirements refined,
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice
      requirements = Some refined ->
    phase1_surface_optional_generic_requirements_expression_fallback_base_choice_tree
      refined =
      phase1_surface_optional_generic_requirements_expression_outer_tree
        requirements.
Proof.
  intros [requirements |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_spine
        requirements)
      as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_spine_round_trip
        requirements actual Hrequirements).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition
  phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_tree
  (tree : ParseTree)
  : option Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine :=
  match phase1_surface_normalize_generic_requirements_expression_outer_tree tree with
  | Some requirements =>
      phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_spine
        requirements
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_tree
      tree = Some refined ->
    phase1_surface_generic_requirements_expression_fallback_base_choice_spine_tree
      refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold
    phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_generic_requirements_expression_outer_tree tree)
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  transitivity
    (phase1_surface_generic_requirements_expression_outer_spine_tree requirements).
  - eapply
      phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirements_expression_outer_tree_round_trip.
    exact Hrequirements.
Qed.

Definition
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_tree
  (tree : ParseTree)
  : option
      (option Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine) :=
  match
    phase1_surface_normalize_optional_generic_requirements_expression_outer_tree
      tree
  with
  | Some requirements =>
      phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice
        requirements
  | None => None
  end.

Theorem
  phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_tree
      tree = Some refined ->
    phase1_surface_optional_generic_requirements_expression_fallback_base_choice_tree
      refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_generic_requirements_expression_outer_tree
      tree)
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  transitivity
    (phase1_surface_optional_generic_requirements_expression_outer_tree requirements).
  - eapply
      phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_optional_generic_requirements_expression_outer_tree_round_trip.
    exact Hrequirements.
Qed.
