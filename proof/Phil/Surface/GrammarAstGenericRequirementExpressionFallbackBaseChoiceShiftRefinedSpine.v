From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementExpressionFallbackBaseChoiceSpine
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the completed shift-refined effect_set_expression carrier through the
  generic_requirement choice while preserving the other twelve alternatives
  exactly.

  Only alternative 6 ("effects ... within ...;") advances from
  Phase1SurfaceEffectSetExpressionFallbackBaseChoiceSpine to
  Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine. One
  explicit fuel value is threaded into that payload refinement.

  Structural Rocq surface correspondence only. This does not change Grammar-v1,
  Haskell/runtime behavior, evaluation semantics, or make broader production
  parser soundness/completeness claims. It continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Inductive
  Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine
  : Type :=
| Phase1GenericStructuralExpressionFallbackBaseChoiceShiftRefinedRequirement
    (selected : ParseTree)
| Phase1GenericPropositionExpressionFallbackBaseChoiceShiftRefinedRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericProviderExpressionFallbackBaseChoiceShiftRefinedRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericCallableExpressionFallbackBaseChoiceShiftRefinedRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryExpressionFallbackBaseChoiceShiftRefinedRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericArchitectureExpressionFallbackBaseChoiceShiftRefinedRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericEffectsExpressionFallbackBaseChoiceShiftRefinedRequirement
    (name_tree : ParseTree)
    (effects :
      Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine)
| Phase1GenericAuthorityExpressionFallbackBaseChoiceShiftRefinedRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryRepresentationExpressionFallbackBaseChoiceShiftRefinedRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericRepresentationExpressionFallbackBaseChoiceShiftRefinedRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericPlacementExpressionFallbackBaseChoiceShiftRefinedRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericCostExpressionFallbackBaseChoiceShiftRefinedRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericEnvironmentExpressionFallbackBaseChoiceShiftRefinedRequirement
    (proposition : Phase1SurfacePropositionSpine).

Definition
  phase1_surface_generic_requirement_expression_fallback_base_choice_shift_refined_spine_index
  (requirement :
    Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine)
  : nat :=
  match requirement with
  | Phase1GenericStructuralExpressionFallbackBaseChoiceShiftRefinedRequirement _ =>
      0
  | Phase1GenericPropositionExpressionFallbackBaseChoiceShiftRefinedRequirement _ =>
      1
  | Phase1GenericProviderExpressionFallbackBaseChoiceShiftRefinedRequirement _ _ =>
      2
  | Phase1GenericCallableExpressionFallbackBaseChoiceShiftRefinedRequirement _ _ =>
      3
  | Phase1GenericBoundaryExpressionFallbackBaseChoiceShiftRefinedRequirement _ _ =>
      4
  | Phase1GenericArchitectureExpressionFallbackBaseChoiceShiftRefinedRequirement _ _ =>
      5
  | Phase1GenericEffectsExpressionFallbackBaseChoiceShiftRefinedRequirement _ _ =>
      6
  | Phase1GenericAuthorityExpressionFallbackBaseChoiceShiftRefinedRequirement _ =>
      7
  | Phase1GenericBoundaryRepresentationExpressionFallbackBaseChoiceShiftRefinedRequirement _ =>
      8
  | Phase1GenericRepresentationExpressionFallbackBaseChoiceShiftRefinedRequirement _ =>
      9
  | Phase1GenericPlacementExpressionFallbackBaseChoiceShiftRefinedRequirement _ =>
      10
  | Phase1GenericCostExpressionFallbackBaseChoiceShiftRefinedRequirement _ =>
      11
  | Phase1GenericEnvironmentExpressionFallbackBaseChoiceShiftRefinedRequirement _ =>
      12
  end.

Definition
  phase1_surface_generic_requirement_expression_fallback_base_choice_shift_refined_selected_tree
  (requirement :
    Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  match requirement with
  | Phase1GenericStructuralExpressionFallbackBaseChoiceShiftRefinedRequirement
      selected =>
      selected
  | Phase1GenericPropositionExpressionFallbackBaseChoiceShiftRefinedRequirement
      proposition =>
      PTSequence
        [ PTLiteral "proposition";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericProviderExpressionFallbackBaseChoiceShiftRefinedRequirement
      name_tree type_value =>
      PTSequence
        [ PTLiteral "provider";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericCallableExpressionFallbackBaseChoiceShiftRefinedRequirement
      name_tree type_value =>
      PTSequence
        [ PTLiteral "callable";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryExpressionFallbackBaseChoiceShiftRefinedRequirement
      name_tree type_value =>
      PTSequence
        [ PTLiteral "boundary";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericArchitectureExpressionFallbackBaseChoiceShiftRefinedRequirement
      name_tree type_value =>
      PTSequence
        [ PTLiteral "architecture";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericEffectsExpressionFallbackBaseChoiceShiftRefinedRequirement
      name_tree effects =>
      PTSequence
        [ PTLiteral "effects";
          name_tree;
          PTLiteral "within";
          phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_spine_tree
            effects;
          PTLiteral ";"
        ]
  | Phase1GenericAuthorityExpressionFallbackBaseChoiceShiftRefinedRequirement
      type_value =>
      PTSequence
        [ PTLiteral "authority";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryRepresentationExpressionFallbackBaseChoiceShiftRefinedRequirement
      type_value =>
      PTSequence
        [ PTLiteral "boundary";
          PTLiteral "representation";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericRepresentationExpressionFallbackBaseChoiceShiftRefinedRequirement
      proposition =>
      PTSequence
        [ PTLiteral "representation";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericPlacementExpressionFallbackBaseChoiceShiftRefinedRequirement
      proposition =>
      PTSequence
        [ PTLiteral "placement";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericCostExpressionFallbackBaseChoiceShiftRefinedRequirement
      proposition =>
      PTSequence
        [ PTLiteral "cost";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericEnvironmentExpressionFallbackBaseChoiceShiftRefinedRequirement
      proposition =>
      PTSequence
        [ PTLiteral "environment";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  end.

Definition
  phase1_surface_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
  (requirement :
    Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  PTNonterminal "generic_requirement"
    (PTAlternative
      (phase1_surface_generic_requirement_expression_fallback_base_choice_shift_refined_spine_index
        requirement)
      (phase1_surface_generic_requirement_expression_fallback_base_choice_shift_refined_selected_tree
        requirement)).

Definition
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
  (fuel : nat)
  (requirement :
    Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceSpine)
  : option
      Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match requirement with
  | Phase1GenericStructuralExpressionFallbackBaseChoiceRequirement selected =>
      Some
        (Phase1GenericStructuralExpressionFallbackBaseChoiceShiftRefinedRequirement
          selected)
  | Phase1GenericPropositionExpressionFallbackBaseChoiceRequirement proposition =>
      Some
        (Phase1GenericPropositionExpressionFallbackBaseChoiceShiftRefinedRequirement
          proposition)
  | Phase1GenericProviderExpressionFallbackBaseChoiceRequirement
      name_tree type_value =>
      Some
        (Phase1GenericProviderExpressionFallbackBaseChoiceShiftRefinedRequirement
          name_tree type_value)
  | Phase1GenericCallableExpressionFallbackBaseChoiceRequirement
      name_tree type_value =>
      Some
        (Phase1GenericCallableExpressionFallbackBaseChoiceShiftRefinedRequirement
          name_tree type_value)
  | Phase1GenericBoundaryExpressionFallbackBaseChoiceRequirement
      name_tree type_value =>
      Some
        (Phase1GenericBoundaryExpressionFallbackBaseChoiceShiftRefinedRequirement
          name_tree type_value)
  | Phase1GenericArchitectureExpressionFallbackBaseChoiceRequirement
      name_tree type_value =>
      Some
        (Phase1GenericArchitectureExpressionFallbackBaseChoiceShiftRefinedRequirement
          name_tree type_value)
  | Phase1GenericEffectsExpressionFallbackBaseChoiceRequirement name_tree effects =>
      match
        phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
          fuel effects
      with
      | Some refined =>
          Some
            (Phase1GenericEffectsExpressionFallbackBaseChoiceShiftRefinedRequirement
              name_tree refined)
      | None => None
      end
  | Phase1GenericAuthorityExpressionFallbackBaseChoiceRequirement type_value =>
      Some
        (Phase1GenericAuthorityExpressionFallbackBaseChoiceShiftRefinedRequirement
          type_value)
  | Phase1GenericBoundaryRepresentationExpressionFallbackBaseChoiceRequirement
      type_value =>
      Some
        (Phase1GenericBoundaryRepresentationExpressionFallbackBaseChoiceShiftRefinedRequirement
          type_value)
  | Phase1GenericRepresentationExpressionFallbackBaseChoiceRequirement proposition =>
      Some
        (Phase1GenericRepresentationExpressionFallbackBaseChoiceShiftRefinedRequirement
          proposition)
  | Phase1GenericPlacementExpressionFallbackBaseChoiceRequirement proposition =>
      Some
        (Phase1GenericPlacementExpressionFallbackBaseChoiceShiftRefinedRequirement
          proposition)
  | Phase1GenericCostExpressionFallbackBaseChoiceRequirement proposition =>
      Some
        (Phase1GenericCostExpressionFallbackBaseChoiceShiftRefinedRequirement
          proposition)
  | Phase1GenericEnvironmentExpressionFallbackBaseChoiceRequirement proposition =>
      Some
        (Phase1GenericEnvironmentExpressionFallbackBaseChoiceShiftRefinedRequirement
          proposition)
  end.

Theorem
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip :
  forall fuel requirement refined,
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel requirement = Some refined ->
    phase1_surface_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
    phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
      requirement.
Proof.
  intros fuel requirement refined Hnormalize.
  destruct requirement; cbn in Hnormalize.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct
      (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel effects)
      as [actual |] eqn:Heffects; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip
        fuel effects actual Heffects).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option
      Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_tree
      tree
  with
  | Some requirement =>
      phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel requirement
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
      refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_tree
      tree)
    as [requirement |] eqn:Hrequirement; try discriminate Hnormalize.
  transitivity
    (phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
      requirement).
  - eapply
      phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_tree_round_trip.
    exact Hrequirement.
Qed.
