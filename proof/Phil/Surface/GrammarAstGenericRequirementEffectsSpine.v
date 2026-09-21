From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementPropositionSpine
  GrammarAstEffectSetTermArgumentsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the remaining opaque generic-requirement payload: the effects branch.

  All twelve non-effects alternatives are preserved exactly from the
  proposition-refined carrier. The effects alternative advances from one
  validated selected ParseTree to its identifier tree plus the fully structured
  effect-set carrier.
*)

Definition phase1_surface_normalize_effects_requirement_payload
  (tree : ParseTree)
  : option (ParseTree * Phase1SurfaceEffectSetTermArgumentsSpine) :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact5 items with
      | Some
          (keyword_tree, name_tree, within_tree, effects_tree, terminator_tree) =>
          match phase1_surface_expect_literal "effects" keyword_tree,
                phase1_surface_validate_named_node "identifier" name_tree,
                phase1_surface_expect_literal "within" within_tree,
                phase1_surface_normalize_effect_set_term_arguments_tree
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

Theorem phase1_surface_normalize_effects_requirement_payload_round_trip :
  forall tree name_tree effects,
    phase1_surface_normalize_effects_requirement_payload tree =
      Some (name_tree, effects) ->
    PTSequence
      [ PTLiteral "effects";
        name_tree;
        PTLiteral "within";
        phase1_surface_effect_set_term_arguments_spine_tree effects;
        PTLiteral ";"
      ] = tree.
Proof.
  intros tree name_tree effects Hnormalize.
  unfold phase1_surface_normalize_effects_requirement_payload in Hnormalize.
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
    (phase1_surface_normalize_effect_set_term_arguments_tree effects_tree)
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
    (phase1_surface_normalize_effect_set_term_arguments_tree_round_trip
      effects_tree actual_effects Heffects).
  rewrite (phase1_surface_expect_literal_round_trip
    ";" terminator_tree Hterminator).
  reflexivity.
Qed.

Inductive Phase1SurfaceGenericRequirementEffectsSpine : Type :=
| Phase1GenericStructuralEffectsRequirement (selected : ParseTree)
| Phase1GenericPropositionEffectsRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericProviderEffectsRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericCallableEffectsRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryEffectsRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericArchitectureEffectsRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericEffectsEffectsRequirement
    (name_tree : ParseTree)
    (effects : Phase1SurfaceEffectSetTermArgumentsSpine)
| Phase1GenericAuthorityEffectsRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryRepresentationEffectsRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericRepresentationEffectsRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericPlacementEffectsRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericCostEffectsRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericEnvironmentEffectsRequirement
    (proposition : Phase1SurfacePropositionSpine).

Definition phase1_surface_generic_requirement_effects_spine_index
  (requirement : Phase1SurfaceGenericRequirementEffectsSpine) : nat :=
  match requirement with
  | Phase1GenericStructuralEffectsRequirement _ => 0
  | Phase1GenericPropositionEffectsRequirement _ => 1
  | Phase1GenericProviderEffectsRequirement _ _ => 2
  | Phase1GenericCallableEffectsRequirement _ _ => 3
  | Phase1GenericBoundaryEffectsRequirement _ _ => 4
  | Phase1GenericArchitectureEffectsRequirement _ _ => 5
  | Phase1GenericEffectsEffectsRequirement _ _ => 6
  | Phase1GenericAuthorityEffectsRequirement _ => 7
  | Phase1GenericBoundaryRepresentationEffectsRequirement _ => 8
  | Phase1GenericRepresentationEffectsRequirement _ => 9
  | Phase1GenericPlacementEffectsRequirement _ => 10
  | Phase1GenericCostEffectsRequirement _ => 11
  | Phase1GenericEnvironmentEffectsRequirement _ => 12
  end.

Definition phase1_surface_generic_requirement_effects_selected_tree
  (requirement : Phase1SurfaceGenericRequirementEffectsSpine) : ParseTree :=
  match requirement with
  | Phase1GenericStructuralEffectsRequirement selected => selected
  | Phase1GenericPropositionEffectsRequirement proposition =>
      PTSequence
        [ PTLiteral "proposition";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericProviderEffectsRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "provider";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericCallableEffectsRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "callable";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryEffectsRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "boundary";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericArchitectureEffectsRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "architecture";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericEffectsEffectsRequirement name_tree effects =>
      PTSequence
        [ PTLiteral "effects";
          name_tree;
          PTLiteral "within";
          phase1_surface_effect_set_term_arguments_spine_tree effects;
          PTLiteral ";"
        ]
  | Phase1GenericAuthorityEffectsRequirement type_value =>
      PTSequence
        [ PTLiteral "authority";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryRepresentationEffectsRequirement type_value =>
      PTSequence
        [ PTLiteral "boundary";
          PTLiteral "representation";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericRepresentationEffectsRequirement proposition =>
      PTSequence
        [ PTLiteral "representation";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericPlacementEffectsRequirement proposition =>
      PTSequence
        [ PTLiteral "placement";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericCostEffectsRequirement proposition =>
      PTSequence
        [ PTLiteral "cost";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericEnvironmentEffectsRequirement proposition =>
      PTSequence
        [ PTLiteral "environment";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  end.

Definition phase1_surface_generic_requirement_effects_spine_tree
  (requirement : Phase1SurfaceGenericRequirementEffectsSpine) : ParseTree :=
  PTNonterminal "generic_requirement"
    (PTAlternative
      (phase1_surface_generic_requirement_effects_spine_index requirement)
      (phase1_surface_generic_requirement_effects_selected_tree requirement)).

Definition phase1_surface_normalize_generic_requirement_effects_spine
  (requirement : Phase1SurfaceGenericRequirementPropositionSpine)
  : option Phase1SurfaceGenericRequirementEffectsSpine :=
  match requirement with
  | Phase1GenericStructuralPropositionRequirement selected =>
      Some (Phase1GenericStructuralEffectsRequirement selected)
  | Phase1GenericPropositionPropositionRequirement proposition =>
      Some (Phase1GenericPropositionEffectsRequirement proposition)
  | Phase1GenericProviderPropositionRequirement name_tree type_value =>
      Some (Phase1GenericProviderEffectsRequirement name_tree type_value)
  | Phase1GenericCallablePropositionRequirement name_tree type_value =>
      Some (Phase1GenericCallableEffectsRequirement name_tree type_value)
  | Phase1GenericBoundaryPropositionRequirement name_tree type_value =>
      Some (Phase1GenericBoundaryEffectsRequirement name_tree type_value)
  | Phase1GenericArchitecturePropositionRequirement name_tree type_value =>
      Some (Phase1GenericArchitectureEffectsRequirement name_tree type_value)
  | Phase1GenericEffectsPropositionRequirement selected =>
      match phase1_surface_normalize_effects_requirement_payload selected with
      | Some (name_tree, effects) =>
          Some (Phase1GenericEffectsEffectsRequirement name_tree effects)
      | None => None
      end
  | Phase1GenericAuthorityPropositionRequirement type_value =>
      Some (Phase1GenericAuthorityEffectsRequirement type_value)
  | Phase1GenericBoundaryRepresentationPropositionRequirement type_value =>
      Some (Phase1GenericBoundaryRepresentationEffectsRequirement type_value)
  | Phase1GenericRepresentationPropositionRequirement proposition =>
      Some (Phase1GenericRepresentationEffectsRequirement proposition)
  | Phase1GenericPlacementPropositionRequirement proposition =>
      Some (Phase1GenericPlacementEffectsRequirement proposition)
  | Phase1GenericCostPropositionRequirement proposition =>
      Some (Phase1GenericCostEffectsRequirement proposition)
  | Phase1GenericEnvironmentPropositionRequirement proposition =>
      Some (Phase1GenericEnvironmentEffectsRequirement proposition)
  end.

Theorem
  phase1_surface_normalize_generic_requirement_effects_spine_round_trip :
  forall requirement refined,
    phase1_surface_normalize_generic_requirement_effects_spine requirement =
      Some refined ->
    phase1_surface_generic_requirement_effects_spine_tree refined =
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
  - destruct (phase1_surface_normalize_effects_requirement_payload selected)
      as [[name_tree effects] |] eqn:Heffects;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_effects_requirement_payload_round_trip
        selected name_tree effects Heffects).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_generic_requirement_effects_tree
  (tree : ParseTree)
  : option Phase1SurfaceGenericRequirementEffectsSpine :=
  match phase1_surface_normalize_generic_requirement_proposition_tree tree with
  | Some requirement =>
      phase1_surface_normalize_generic_requirement_effects_spine requirement
  | None => None
  end.

Theorem phase1_surface_normalize_generic_requirement_effects_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_generic_requirement_effects_tree tree =
      Some refined ->
    phase1_surface_generic_requirement_effects_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_generic_requirement_effects_tree in Hnormalize.
  destruct (phase1_surface_normalize_generic_requirement_proposition_tree tree)
    as [requirement |] eqn:Hrequirement; try discriminate Hnormalize.
  transitivity
    (phase1_surface_generic_requirement_proposition_spine_tree requirement).
  - eapply
      phase1_surface_normalize_generic_requirement_effects_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirement_proposition_tree_round_trip.
    exact Hrequirement.
Qed.
