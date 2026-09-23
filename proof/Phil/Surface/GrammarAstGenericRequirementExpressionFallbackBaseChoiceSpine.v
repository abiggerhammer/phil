From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementExpressionOuterSpine
  GrammarAstEffectSetExpressionFallbackBaseChoiceSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the fallback/base-choice-refined effect-set carrier into the generic
  effects requirement while preserving the other twelve requirement
  alternatives exactly.

  Only the effects branch advances from
  Phase1SurfaceEffectSetExpressionOuterSpine to
  Phase1SurfaceEffectSetExpressionFallbackBaseChoiceSpine.
*)

Inductive Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceSpine : Type :=
| Phase1GenericStructuralExpressionFallbackBaseChoiceRequirement
    (selected : ParseTree)
| Phase1GenericPropositionExpressionFallbackBaseChoiceRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericProviderExpressionFallbackBaseChoiceRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericCallableExpressionFallbackBaseChoiceRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryExpressionFallbackBaseChoiceRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericArchitectureExpressionFallbackBaseChoiceRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericEffectsExpressionFallbackBaseChoiceRequirement
    (name_tree : ParseTree)
    (effects : Phase1SurfaceEffectSetExpressionFallbackBaseChoiceSpine)
| Phase1GenericAuthorityExpressionFallbackBaseChoiceRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryRepresentationExpressionFallbackBaseChoiceRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericRepresentationExpressionFallbackBaseChoiceRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericPlacementExpressionFallbackBaseChoiceRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericCostExpressionFallbackBaseChoiceRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericEnvironmentExpressionFallbackBaseChoiceRequirement
    (proposition : Phase1SurfacePropositionSpine).

Definition phase1_surface_generic_requirement_expression_fallback_base_choice_spine_index
  (requirement : Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceSpine)
  : nat :=
  match requirement with
  | Phase1GenericStructuralExpressionFallbackBaseChoiceRequirement _ => 0
  | Phase1GenericPropositionExpressionFallbackBaseChoiceRequirement _ => 1
  | Phase1GenericProviderExpressionFallbackBaseChoiceRequirement _ _ => 2
  | Phase1GenericCallableExpressionFallbackBaseChoiceRequirement _ _ => 3
  | Phase1GenericBoundaryExpressionFallbackBaseChoiceRequirement _ _ => 4
  | Phase1GenericArchitectureExpressionFallbackBaseChoiceRequirement _ _ => 5
  | Phase1GenericEffectsExpressionFallbackBaseChoiceRequirement _ _ => 6
  | Phase1GenericAuthorityExpressionFallbackBaseChoiceRequirement _ => 7
  | Phase1GenericBoundaryRepresentationExpressionFallbackBaseChoiceRequirement _ => 8
  | Phase1GenericRepresentationExpressionFallbackBaseChoiceRequirement _ => 9
  | Phase1GenericPlacementExpressionFallbackBaseChoiceRequirement _ => 10
  | Phase1GenericCostExpressionFallbackBaseChoiceRequirement _ => 11
  | Phase1GenericEnvironmentExpressionFallbackBaseChoiceRequirement _ => 12
  end.

Definition phase1_surface_generic_requirement_expression_fallback_base_choice_selected_tree
  (requirement : Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceSpine)
  : ParseTree :=
  match requirement with
  | Phase1GenericStructuralExpressionFallbackBaseChoiceRequirement selected =>
      selected
  | Phase1GenericPropositionExpressionFallbackBaseChoiceRequirement proposition =>
      PTSequence
        [ PTLiteral "proposition";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericProviderExpressionFallbackBaseChoiceRequirement
      name_tree type_value =>
      PTSequence
        [ PTLiteral "provider";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericCallableExpressionFallbackBaseChoiceRequirement
      name_tree type_value =>
      PTSequence
        [ PTLiteral "callable";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryExpressionFallbackBaseChoiceRequirement
      name_tree type_value =>
      PTSequence
        [ PTLiteral "boundary";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericArchitectureExpressionFallbackBaseChoiceRequirement
      name_tree type_value =>
      PTSequence
        [ PTLiteral "architecture";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericEffectsExpressionFallbackBaseChoiceRequirement
      name_tree effects =>
      PTSequence
        [ PTLiteral "effects";
          name_tree;
          PTLiteral "within";
          phase1_surface_effect_set_expression_fallback_base_choice_spine_tree
            effects;
          PTLiteral ";"
        ]
  | Phase1GenericAuthorityExpressionFallbackBaseChoiceRequirement type_value =>
      PTSequence
        [ PTLiteral "authority";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryRepresentationExpressionFallbackBaseChoiceRequirement
      type_value =>
      PTSequence
        [ PTLiteral "boundary";
          PTLiteral "representation";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericRepresentationExpressionFallbackBaseChoiceRequirement
      proposition =>
      PTSequence
        [ PTLiteral "representation";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericPlacementExpressionFallbackBaseChoiceRequirement proposition =>
      PTSequence
        [ PTLiteral "placement";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericCostExpressionFallbackBaseChoiceRequirement proposition =>
      PTSequence
        [ PTLiteral "cost";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericEnvironmentExpressionFallbackBaseChoiceRequirement
      proposition =>
      PTSequence
        [ PTLiteral "environment";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  end.

Definition phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
  (requirement : Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceSpine)
  : ParseTree :=
  PTNonterminal "generic_requirement"
    (PTAlternative
      (phase1_surface_generic_requirement_expression_fallback_base_choice_spine_index
        requirement)
      (phase1_surface_generic_requirement_expression_fallback_base_choice_selected_tree
        requirement)).

Definition phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_spine
  (requirement : Phase1SurfaceGenericRequirementExpressionOuterSpine)
  : option Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceSpine :=
  match requirement with
  | Phase1GenericStructuralExpressionOuterRequirement selected =>
      Some
        (Phase1GenericStructuralExpressionFallbackBaseChoiceRequirement selected)
  | Phase1GenericPropositionExpressionOuterRequirement proposition =>
      Some
        (Phase1GenericPropositionExpressionFallbackBaseChoiceRequirement
          proposition)
  | Phase1GenericProviderExpressionOuterRequirement name_tree type_value =>
      Some
        (Phase1GenericProviderExpressionFallbackBaseChoiceRequirement
          name_tree type_value)
  | Phase1GenericCallableExpressionOuterRequirement name_tree type_value =>
      Some
        (Phase1GenericCallableExpressionFallbackBaseChoiceRequirement
          name_tree type_value)
  | Phase1GenericBoundaryExpressionOuterRequirement name_tree type_value =>
      Some
        (Phase1GenericBoundaryExpressionFallbackBaseChoiceRequirement
          name_tree type_value)
  | Phase1GenericArchitectureExpressionOuterRequirement name_tree type_value =>
      Some
        (Phase1GenericArchitectureExpressionFallbackBaseChoiceRequirement
          name_tree type_value)
  | Phase1GenericEffectsExpressionOuterRequirement name_tree effects =>
      match
        phase1_surface_normalize_effect_set_expression_fallback_base_choice_spine
          effects
      with
      | Some refined =>
          Some
            (Phase1GenericEffectsExpressionFallbackBaseChoiceRequirement
              name_tree refined)
      | None => None
      end
  | Phase1GenericAuthorityExpressionOuterRequirement type_value =>
      Some
        (Phase1GenericAuthorityExpressionFallbackBaseChoiceRequirement
          type_value)
  | Phase1GenericBoundaryRepresentationExpressionOuterRequirement type_value =>
      Some
        (Phase1GenericBoundaryRepresentationExpressionFallbackBaseChoiceRequirement
          type_value)
  | Phase1GenericRepresentationExpressionOuterRequirement proposition =>
      Some
        (Phase1GenericRepresentationExpressionFallbackBaseChoiceRequirement
          proposition)
  | Phase1GenericPlacementExpressionOuterRequirement proposition =>
      Some
        (Phase1GenericPlacementExpressionFallbackBaseChoiceRequirement
          proposition)
  | Phase1GenericCostExpressionOuterRequirement proposition =>
      Some
        (Phase1GenericCostExpressionFallbackBaseChoiceRequirement proposition)
  | Phase1GenericEnvironmentExpressionOuterRequirement proposition =>
      Some
        (Phase1GenericEnvironmentExpressionFallbackBaseChoiceRequirement
          proposition)
  end.

Theorem
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_spine_round_trip :
  forall requirement refined,
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_spine
      requirement = Some refined ->
    phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
      refined =
      phase1_surface_generic_requirement_expression_outer_spine_tree requirement.
Proof.
  intros requirement refined Hnormalize.
  destruct requirement; cbn in Hnormalize.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct
      (phase1_surface_normalize_effect_set_expression_fallback_base_choice_spine
        effects)
      as [actual |] eqn:Heffects; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_effect_set_expression_fallback_base_choice_spine_round_trip
        effects actual Heffects).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_tree
  (tree : ParseTree)
  : option Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceSpine :=
  match phase1_surface_normalize_generic_requirement_expression_outer_tree tree with
  | Some requirement =>
      phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_spine
        requirement
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_tree
      tree = Some refined ->
    phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
      refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold
    phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_generic_requirement_expression_outer_tree tree)
    as [requirement |] eqn:Hrequirement; try discriminate Hnormalize.
  transitivity
    (phase1_surface_generic_requirement_expression_outer_spine_tree requirement).
  - eapply
      phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirement_expression_outer_tree_round_trip.
    exact Hrequirement.
Qed.
