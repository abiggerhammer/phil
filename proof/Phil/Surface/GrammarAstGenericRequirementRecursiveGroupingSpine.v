From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstSourceHeader
  GrammarAstTopLevelSpine
  GrammarAstGenericRequirementsSpine
  GrammarAstPropositionSpine
  GrammarAstStaticTypeArgumentCarrierSpine
  GrammarAstGenericRequirementPropositionSpine
  GrammarAstEffectSetRecursiveGroupingSpine
  GrammarAstGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the remaining opaque generic-requirement payload: the effects branch.

  All twelve non-effects alternatives are preserved exactly from the
  proposition-refined carrier. The effects alternative advances from one
  validated selected ParseTree to its identifier tree plus the fully structured
  effect-set carrier.
*)

Definition phase1_surface_normalize_generic_requirement_recursive_grouping_payload
  (tree : ParseTree)
  : option (ParseTree * Phase1SurfaceEffectSetRecursiveGroupingSpine) :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact5 items with
      | Some
          (keyword_tree, name_tree, within_tree, effects_tree, terminator_tree) =>
          match phase1_surface_expect_literal "effects" keyword_tree,
                phase1_surface_validate_named_node "identifier" name_tree,
                phase1_surface_expect_literal "within" within_tree,
                phase1_surface_normalize_effect_set_recursive_grouping_tree
                  effects_tree,
                phase1_surface_expect_literal ";" terminator_tree with
          | Some tt, Some tt, Some tt, Some effects, Some tt =>
              Some (name_tree, effects)
          | _, _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_generic_requirement_recursive_grouping_payload_round_trip :
  forall tree name_tree effects,
    phase1_surface_normalize_generic_requirement_recursive_grouping_payload tree =
      Some (name_tree, effects) ->
    PTSequence
      [ PTLiteral "effects";
        name_tree;
        PTLiteral "within";
        phase1_surface_effect_set_recursive_grouping_spine_tree effects;
        PTLiteral ";"
      ] = tree.
Proof.
  intros tree name_tree effects Hnormalize.
  unfold phase1_surface_normalize_generic_requirement_recursive_grouping_payload in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact5 items)
    as [[[[keyword_tree actual_name_tree] within_tree] effects_tree]
          terminator_tree |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "effects" keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "identifier" actual_name_tree)
    as [[] |] eqn:Hname; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "within" within_tree)
    as [[] |] eqn:Hwithin; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_effect_set_recursive_grouping_tree effects_tree)
    as [actual_effects |] eqn:Heffects; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ";" terminator_tree)
    as [[] |] eqn:Hterminator; try discriminate Hnormalize.
  inversion Hnormalize; subst name_tree effects.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite
    (phase1_surface_exact5_round_trip
      items keyword_tree actual_name_tree within_tree effects_tree
      terminator_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "effects" keyword_tree Hkeyword).
  rewrite (phase1_surface_expect_literal_round_trip
    "within" within_tree Hwithin).
  rewrite <-
    (phase1_surface_normalize_effect_set_recursive_grouping_tree_round_trip
      effects_tree actual_effects Heffects).
  rewrite (phase1_surface_expect_literal_round_trip
    ";" terminator_tree Hterminator).
  reflexivity.
Qed.

Inductive Phase1SurfaceGenericRequirementRecursiveGroupingSpine : Type :=
| Phase1GenericStructuralRecursiveGroupingRequirement (selected : ParseTree)
| Phase1GenericPropositionRecursiveGroupingRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericProviderRecursiveGroupingRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericCallableRecursiveGroupingRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryRecursiveGroupingRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericArchitectureRecursiveGroupingRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericEffectsRecursiveGroupingRequirement
    (name_tree : ParseTree)
    (effects : Phase1SurfaceEffectSetRecursiveGroupingSpine)
| Phase1GenericAuthorityRecursiveGroupingRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryRepresentationRecursiveGroupingRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericRepresentationRecursiveGroupingRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericPlacementRecursiveGroupingRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericCostRecursiveGroupingRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericEnvironmentRecursiveGroupingRequirement
    (proposition : Phase1SurfacePropositionSpine).

Definition phase1_surface_generic_requirement_recursive_grouping_spine_index
  (requirement : Phase1SurfaceGenericRequirementRecursiveGroupingSpine) : nat :=
  match requirement with
  | Phase1GenericStructuralRecursiveGroupingRequirement _ => 0
  | Phase1GenericPropositionRecursiveGroupingRequirement _ => 1
  | Phase1GenericProviderRecursiveGroupingRequirement _ _ => 2
  | Phase1GenericCallableRecursiveGroupingRequirement _ _ => 3
  | Phase1GenericBoundaryRecursiveGroupingRequirement _ _ => 4
  | Phase1GenericArchitectureRecursiveGroupingRequirement _ _ => 5
  | Phase1GenericEffectsRecursiveGroupingRequirement _ _ => 6
  | Phase1GenericAuthorityRecursiveGroupingRequirement _ => 7
  | Phase1GenericBoundaryRepresentationRecursiveGroupingRequirement _ => 8
  | Phase1GenericRepresentationRecursiveGroupingRequirement _ => 9
  | Phase1GenericPlacementRecursiveGroupingRequirement _ => 10
  | Phase1GenericCostRecursiveGroupingRequirement _ => 11
  | Phase1GenericEnvironmentRecursiveGroupingRequirement _ => 12
  end.

Definition phase1_surface_generic_requirement_recursive_grouping_selected_tree
  (requirement : Phase1SurfaceGenericRequirementRecursiveGroupingSpine) : ParseTree :=
  match requirement with
  | Phase1GenericStructuralRecursiveGroupingRequirement selected => selected
  | Phase1GenericPropositionRecursiveGroupingRequirement proposition =>
      PTSequence
        [ PTLiteral "proposition";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericProviderRecursiveGroupingRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "provider";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericCallableRecursiveGroupingRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "callable";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryRecursiveGroupingRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "boundary";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericArchitectureRecursiveGroupingRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "architecture";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericEffectsRecursiveGroupingRequirement name_tree effects =>
      PTSequence
        [ PTLiteral "effects";
          name_tree;
          PTLiteral "within";
          phase1_surface_effect_set_recursive_grouping_spine_tree effects;
          PTLiteral ";"
        ]
  | Phase1GenericAuthorityRecursiveGroupingRequirement type_value =>
      PTSequence
        [ PTLiteral "authority";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryRepresentationRecursiveGroupingRequirement type_value =>
      PTSequence
        [ PTLiteral "boundary";
          PTLiteral "representation";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericRepresentationRecursiveGroupingRequirement proposition =>
      PTSequence
        [ PTLiteral "representation";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericPlacementRecursiveGroupingRequirement proposition =>
      PTSequence
        [ PTLiteral "placement";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericCostRecursiveGroupingRequirement proposition =>
      PTSequence
        [ PTLiteral "cost";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericEnvironmentRecursiveGroupingRequirement proposition =>
      PTSequence
        [ PTLiteral "environment";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  end.

Definition phase1_surface_generic_requirement_recursive_grouping_spine_tree
  (requirement : Phase1SurfaceGenericRequirementRecursiveGroupingSpine) : ParseTree :=
  PTNonterminal "generic_requirement"
    (PTAlternative
      (phase1_surface_generic_requirement_recursive_grouping_spine_index requirement)
      (phase1_surface_generic_requirement_recursive_grouping_selected_tree requirement)).

Definition phase1_surface_normalize_generic_requirement_recursive_grouping_spine
  (requirement : Phase1SurfaceGenericRequirementPropositionSpine)
  : option Phase1SurfaceGenericRequirementRecursiveGroupingSpine :=
  match requirement with
  | Phase1GenericStructuralPropositionRequirement selected =>
      Some (Phase1GenericStructuralRecursiveGroupingRequirement selected)
  | Phase1GenericPropositionPropositionRequirement proposition =>
      Some (Phase1GenericPropositionRecursiveGroupingRequirement proposition)
  | Phase1GenericProviderPropositionRequirement name_tree type_value =>
      Some (Phase1GenericProviderRecursiveGroupingRequirement name_tree type_value)
  | Phase1GenericCallablePropositionRequirement name_tree type_value =>
      Some (Phase1GenericCallableRecursiveGroupingRequirement name_tree type_value)
  | Phase1GenericBoundaryPropositionRequirement name_tree type_value =>
      Some (Phase1GenericBoundaryRecursiveGroupingRequirement name_tree type_value)
  | Phase1GenericArchitecturePropositionRequirement name_tree type_value =>
      Some (Phase1GenericArchitectureRecursiveGroupingRequirement name_tree type_value)
  | Phase1GenericEffectsPropositionRequirement selected =>
      match phase1_surface_normalize_generic_requirement_recursive_grouping_payload selected with
      | Some (name_tree, effects) =>
          Some (Phase1GenericEffectsRecursiveGroupingRequirement name_tree effects)
      | None => None
      end
  | Phase1GenericAuthorityPropositionRequirement type_value =>
      Some (Phase1GenericAuthorityRecursiveGroupingRequirement type_value)
  | Phase1GenericBoundaryRepresentationPropositionRequirement type_value =>
      Some (Phase1GenericBoundaryRepresentationRecursiveGroupingRequirement type_value)
  | Phase1GenericRepresentationPropositionRequirement proposition =>
      Some (Phase1GenericRepresentationRecursiveGroupingRequirement proposition)
  | Phase1GenericPlacementPropositionRequirement proposition =>
      Some (Phase1GenericPlacementRecursiveGroupingRequirement proposition)
  | Phase1GenericCostPropositionRequirement proposition =>
      Some (Phase1GenericCostRecursiveGroupingRequirement proposition)
  | Phase1GenericEnvironmentPropositionRequirement proposition =>
      Some (Phase1GenericEnvironmentRecursiveGroupingRequirement proposition)
  end.

Theorem
  phase1_surface_normalize_generic_requirement_recursive_grouping_spine_round_trip :
  forall requirement refined,
    phase1_surface_normalize_generic_requirement_recursive_grouping_spine requirement =
      Some refined ->
    phase1_surface_generic_requirement_recursive_grouping_spine_tree refined =
      phase1_surface_generic_requirement_proposition_spine_tree requirement.
Proof.
  intros requirement refined Hnormalize.
  destruct requirement; cbn in Hnormalize.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct (phase1_surface_normalize_generic_requirement_recursive_grouping_payload selected)
      as [[name_tree effects] |] eqn:Heffects;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_generic_requirement_recursive_grouping_payload_round_trip
        selected name_tree effects Heffects).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_generic_requirement_recursive_grouping_tree
  (tree : ParseTree)
  : option Phase1SurfaceGenericRequirementRecursiveGroupingSpine :=
  match phase1_surface_normalize_generic_requirement_proposition_tree tree with
  | Some requirement =>
      phase1_surface_normalize_generic_requirement_recursive_grouping_spine requirement
  | None => None
  end.

Theorem phase1_surface_normalize_generic_requirement_recursive_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_generic_requirement_recursive_grouping_tree tree =
      Some refined ->
    phase1_surface_generic_requirement_recursive_grouping_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_generic_requirement_recursive_grouping_tree in Hnormalize.
  destruct (phase1_surface_normalize_generic_requirement_proposition_tree tree)
    as [requirement |] eqn:Hrequirement; try discriminate Hnormalize.
  transitivity
    (phase1_surface_generic_requirement_proposition_spine_tree requirement).
  - eapply
      phase1_surface_normalize_generic_requirement_recursive_grouping_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirement_proposition_tree_round_trip.
    exact Hrequirement.
Qed.

(* The legacy bridge matches all thirteen constructors directly. *)
Definition phase1_surface_refine_generic_requirement_recursive_grouping
  (previous :
    Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine)
  : option Phase1SurfaceGenericRequirementRecursiveGroupingSpine :=
  match previous with
  | Phase1GenericStructuralExpressionFallbackBaseChoiceShiftRefinedRequirement selected =>
      Some (Phase1GenericStructuralRecursiveGroupingRequirement selected)
  | Phase1GenericPropositionExpressionFallbackBaseChoiceShiftRefinedRequirement proposition =>
      Some (Phase1GenericPropositionRecursiveGroupingRequirement proposition)
  | Phase1GenericProviderExpressionFallbackBaseChoiceShiftRefinedRequirement name_tree type_value =>
      Some (Phase1GenericProviderRecursiveGroupingRequirement name_tree type_value)
  | Phase1GenericCallableExpressionFallbackBaseChoiceShiftRefinedRequirement name_tree type_value =>
      Some (Phase1GenericCallableRecursiveGroupingRequirement name_tree type_value)
  | Phase1GenericBoundaryExpressionFallbackBaseChoiceShiftRefinedRequirement name_tree type_value =>
      Some (Phase1GenericBoundaryRecursiveGroupingRequirement name_tree type_value)
  | Phase1GenericArchitectureExpressionFallbackBaseChoiceShiftRefinedRequirement name_tree type_value =>
      Some (Phase1GenericArchitectureRecursiveGroupingRequirement name_tree type_value)
  | Phase1GenericEffectsExpressionFallbackBaseChoiceShiftRefinedRequirement name_tree effects =>
      match phase1_surface_refine_effect_set_recursive_grouping effects with
      | Some refined =>
          Some (Phase1GenericEffectsRecursiveGroupingRequirement name_tree refined)
      | None => None
      end
  | Phase1GenericAuthorityExpressionFallbackBaseChoiceShiftRefinedRequirement type_value =>
      Some (Phase1GenericAuthorityRecursiveGroupingRequirement type_value)
  | Phase1GenericBoundaryRepresentationExpressionFallbackBaseChoiceShiftRefinedRequirement type_value =>
      Some (Phase1GenericBoundaryRepresentationRecursiveGroupingRequirement type_value)
  | Phase1GenericRepresentationExpressionFallbackBaseChoiceShiftRefinedRequirement proposition =>
      Some (Phase1GenericRepresentationRecursiveGroupingRequirement proposition)
  | Phase1GenericPlacementExpressionFallbackBaseChoiceShiftRefinedRequirement proposition =>
      Some (Phase1GenericPlacementRecursiveGroupingRequirement proposition)
  | Phase1GenericCostExpressionFallbackBaseChoiceShiftRefinedRequirement proposition =>
      Some (Phase1GenericCostRecursiveGroupingRequirement proposition)
  | Phase1GenericEnvironmentExpressionFallbackBaseChoiceShiftRefinedRequirement proposition =>
      Some (Phase1GenericEnvironmentRecursiveGroupingRequirement proposition)
  end.

Theorem phase1_surface_refine_generic_requirement_recursive_grouping_round_trip :
  forall previous refined,
    phase1_surface_refine_generic_requirement_recursive_grouping previous =
      Some refined ->
    phase1_surface_generic_requirement_recursive_grouping_spine_tree refined =
      phase1_surface_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
        previous.
Proof.
  intros previous refined Hnormalize.
  destruct previous; cbn in Hnormalize.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct (phase1_surface_refine_effect_set_recursive_grouping effects)
      as [actual |] eqn:Heffects; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_refine_effect_set_recursive_grouping_round_trip
      effects actual Heffects).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.
