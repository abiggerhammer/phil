From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementEffectsSpine
  GrammarAstEffectSetExpressionOuterSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the expression-outer-refined effect-set carrier into the generic
  effects requirement while preserving the other twelve requirement
  alternatives exactly.

  Only the effects branch advances from
  Phase1SurfaceEffectSetTermArgumentsSpine to
  Phase1SurfaceEffectSetExpressionOuterSpine.
*)

Inductive Phase1SurfaceGenericRequirementExpressionOuterSpine : Type :=
| Phase1GenericStructuralExpressionOuterRequirement (selected : ParseTree)
| Phase1GenericPropositionExpressionOuterRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericProviderExpressionOuterRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericCallableExpressionOuterRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryExpressionOuterRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericArchitectureExpressionOuterRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericEffectsExpressionOuterRequirement
    (name_tree : ParseTree)
    (effects : Phase1SurfaceEffectSetExpressionOuterSpine)
| Phase1GenericAuthorityExpressionOuterRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryRepresentationExpressionOuterRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericRepresentationExpressionOuterRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericPlacementExpressionOuterRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericCostExpressionOuterRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericEnvironmentExpressionOuterRequirement
    (proposition : Phase1SurfacePropositionSpine).

Definition phase1_surface_generic_requirement_expression_outer_spine_index
  (requirement : Phase1SurfaceGenericRequirementExpressionOuterSpine) : nat :=
  match requirement with
  | Phase1GenericStructuralExpressionOuterRequirement _ => 0
  | Phase1GenericPropositionExpressionOuterRequirement _ => 1
  | Phase1GenericProviderExpressionOuterRequirement _ _ => 2
  | Phase1GenericCallableExpressionOuterRequirement _ _ => 3
  | Phase1GenericBoundaryExpressionOuterRequirement _ _ => 4
  | Phase1GenericArchitectureExpressionOuterRequirement _ _ => 5
  | Phase1GenericEffectsExpressionOuterRequirement _ _ => 6
  | Phase1GenericAuthorityExpressionOuterRequirement _ => 7
  | Phase1GenericBoundaryRepresentationExpressionOuterRequirement _ => 8
  | Phase1GenericRepresentationExpressionOuterRequirement _ => 9
  | Phase1GenericPlacementExpressionOuterRequirement _ => 10
  | Phase1GenericCostExpressionOuterRequirement _ => 11
  | Phase1GenericEnvironmentExpressionOuterRequirement _ => 12
  end.

Definition phase1_surface_generic_requirement_expression_outer_selected_tree
  (requirement : Phase1SurfaceGenericRequirementExpressionOuterSpine)
  : ParseTree :=
  match requirement with
  | Phase1GenericStructuralExpressionOuterRequirement selected => selected
  | Phase1GenericPropositionExpressionOuterRequirement proposition =>
      PTSequence
        [ PTLiteral "proposition";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericProviderExpressionOuterRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "provider";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericCallableExpressionOuterRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "callable";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryExpressionOuterRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "boundary";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericArchitectureExpressionOuterRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "architecture";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericEffectsExpressionOuterRequirement name_tree effects =>
      PTSequence
        [ PTLiteral "effects";
          name_tree;
          PTLiteral "within";
          phase1_surface_effect_set_expression_outer_spine_tree effects;
          PTLiteral ";"
        ]
  | Phase1GenericAuthorityExpressionOuterRequirement type_value =>
      PTSequence
        [ PTLiteral "authority";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryRepresentationExpressionOuterRequirement type_value =>
      PTSequence
        [ PTLiteral "boundary";
          PTLiteral "representation";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericRepresentationExpressionOuterRequirement proposition =>
      PTSequence
        [ PTLiteral "representation";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericPlacementExpressionOuterRequirement proposition =>
      PTSequence
        [ PTLiteral "placement";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericCostExpressionOuterRequirement proposition =>
      PTSequence
        [ PTLiteral "cost";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericEnvironmentExpressionOuterRequirement proposition =>
      PTSequence
        [ PTLiteral "environment";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  end.

Definition phase1_surface_generic_requirement_expression_outer_spine_tree
  (requirement : Phase1SurfaceGenericRequirementExpressionOuterSpine)
  : ParseTree :=
  PTNonterminal "generic_requirement"
    (PTAlternative
      (phase1_surface_generic_requirement_expression_outer_spine_index
        requirement)
      (phase1_surface_generic_requirement_expression_outer_selected_tree
        requirement)).

Definition phase1_surface_normalize_generic_requirement_expression_outer_spine
  (requirement : Phase1SurfaceGenericRequirementEffectsSpine)
  : option Phase1SurfaceGenericRequirementExpressionOuterSpine :=
  match requirement with
  | Phase1GenericStructuralEffectsRequirement selected =>
      Some (Phase1GenericStructuralExpressionOuterRequirement selected)
  | Phase1GenericPropositionEffectsRequirement proposition =>
      Some (Phase1GenericPropositionExpressionOuterRequirement proposition)
  | Phase1GenericProviderEffectsRequirement name_tree type_value =>
      Some
        (Phase1GenericProviderExpressionOuterRequirement name_tree type_value)
  | Phase1GenericCallableEffectsRequirement name_tree type_value =>
      Some
        (Phase1GenericCallableExpressionOuterRequirement name_tree type_value)
  | Phase1GenericBoundaryEffectsRequirement name_tree type_value =>
      Some
        (Phase1GenericBoundaryExpressionOuterRequirement name_tree type_value)
  | Phase1GenericArchitectureEffectsRequirement name_tree type_value =>
      Some
        (Phase1GenericArchitectureExpressionOuterRequirement
          name_tree type_value)
  | Phase1GenericEffectsEffectsRequirement name_tree effects =>
      match phase1_surface_normalize_effect_set_expression_outer_spine effects with
      | Some refined =>
          Some
            (Phase1GenericEffectsExpressionOuterRequirement
              name_tree refined)
      | None => None
      end
  | Phase1GenericAuthorityEffectsRequirement type_value =>
      Some (Phase1GenericAuthorityExpressionOuterRequirement type_value)
  | Phase1GenericBoundaryRepresentationEffectsRequirement type_value =>
      Some
        (Phase1GenericBoundaryRepresentationExpressionOuterRequirement
          type_value)
  | Phase1GenericRepresentationEffectsRequirement proposition =>
      Some
        (Phase1GenericRepresentationExpressionOuterRequirement proposition)
  | Phase1GenericPlacementEffectsRequirement proposition =>
      Some (Phase1GenericPlacementExpressionOuterRequirement proposition)
  | Phase1GenericCostEffectsRequirement proposition =>
      Some (Phase1GenericCostExpressionOuterRequirement proposition)
  | Phase1GenericEnvironmentEffectsRequirement proposition =>
      Some (Phase1GenericEnvironmentExpressionOuterRequirement proposition)
  end.

Theorem
  phase1_surface_normalize_generic_requirement_expression_outer_spine_round_trip :
  forall requirement refined,
    phase1_surface_normalize_generic_requirement_expression_outer_spine
      requirement = Some refined ->
    phase1_surface_generic_requirement_expression_outer_spine_tree refined =
      phase1_surface_generic_requirement_effects_spine_tree requirement.
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
      (phase1_surface_normalize_effect_set_expression_outer_spine effects)
      as [actual |] eqn:Heffects; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_effect_set_expression_outer_spine_round_trip
        effects actual Heffects).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_generic_requirement_expression_outer_tree
  (tree : ParseTree)
  : option Phase1SurfaceGenericRequirementExpressionOuterSpine :=
  match phase1_surface_normalize_generic_requirement_effects_tree tree with
  | Some requirement =>
      phase1_surface_normalize_generic_requirement_expression_outer_spine
        requirement
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_requirement_expression_outer_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_generic_requirement_expression_outer_tree tree =
      Some refined ->
    phase1_surface_generic_requirement_expression_outer_spine_tree refined =
      tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_generic_requirement_expression_outer_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_generic_requirement_effects_tree tree)
    as [requirement |] eqn:Hrequirement; try discriminate Hnormalize.
  transitivity
    (phase1_surface_generic_requirement_effects_spine_tree requirement).
  - eapply
      phase1_surface_normalize_generic_requirement_expression_outer_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirement_effects_tree_round_trip.
    exact Hrequirement.
Qed.
