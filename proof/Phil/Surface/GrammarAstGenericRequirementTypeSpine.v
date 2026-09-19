From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsSpine
  GrammarAstStaticTypeArgumentCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine only the nested type_expression payloads retained by generic
  requirements.

  Proposition and effect-set payloads remain exact certified ParseTree values
  for their dedicated successor slices.
*)

Definition phase1_surface_normalize_named_type_requirement_type
  (keyword : string) (tree : ParseTree)
  : option (ParseTree * Phase1SurfaceStaticTypeArgumentsTypeSpine) :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact5 items with
      | Some (keyword_tree, name_tree, colon_tree, type_tree, terminator_tree) =>
          match phase1_surface_expect_literal keyword keyword_tree,
                phase1_surface_validate_named_node "identifier" name_tree,
                phase1_surface_expect_literal ":" colon_tree,
                phase1_surface_normalize_static_type_arguments_type_tree type_tree,
                phase1_surface_expect_literal ";" terminator_tree with
          | Some tt, Some tt, Some tt, Some type_value, Some tt =>
              Some (name_tree, type_value)
          | _, _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_named_type_requirement_type_round_trip :
  forall keyword tree name_tree type_value,
    phase1_surface_normalize_named_type_requirement_type keyword tree =
      Some (name_tree, type_value) ->
    PTSequence
      [ PTLiteral keyword;
        name_tree;
        PTLiteral ":";
        phase1_surface_static_type_arguments_type_spine_tree type_value;
        PTLiteral ";"
      ] = tree.
Proof.
  intros keyword tree name_tree type_value Hnormalize.
  unfold phase1_surface_normalize_named_type_requirement_type in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact5 items)
    as [[[[[keyword_tree actual_name] colon_tree] type_tree] terminator_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal keyword keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "identifier" actual_name)
    as [[] |] eqn:Hname; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ":" colon_tree)
    as [[] |] eqn:Hcolon; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_static_type_arguments_type_tree type_tree)
    as [actual_type |] eqn:Htype; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ";" terminator_tree)
    as [[] |] eqn:Hterminator; try discriminate Hnormalize.
  inversion Hnormalize; subst name_tree type_value.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact5_round_trip
    items keyword_tree actual_name colon_tree type_tree terminator_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    keyword keyword_tree Hkeyword).
  rewrite (phase1_surface_expect_literal_round_trip ":" colon_tree Hcolon).
  rewrite <-
    (phase1_surface_normalize_static_type_arguments_type_tree_round_trip
      type_tree actual_type Htype).
  rewrite (phase1_surface_expect_literal_round_trip
    ";" terminator_tree Hterminator).
  reflexivity.
Qed.

Definition phase1_surface_normalize_type_only_requirement_type
  (keyword : string) (tree : ParseTree)
  : option Phase1SurfaceStaticTypeArgumentsTypeSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact3 items with
      | Some (keyword_tree, type_tree, terminator_tree) =>
          match phase1_surface_expect_literal keyword keyword_tree,
                phase1_surface_normalize_static_type_arguments_type_tree type_tree,
                phase1_surface_expect_literal ";" terminator_tree with
          | Some tt, Some type_value, Some tt => Some type_value
          | _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_type_only_requirement_type_round_trip :
  forall keyword tree type_value,
    phase1_surface_normalize_type_only_requirement_type keyword tree =
      Some type_value ->
    PTSequence
      [ PTLiteral keyword;
        phase1_surface_static_type_arguments_type_spine_tree type_value;
        PTLiteral ";"
      ] = tree.
Proof.
  intros keyword tree type_value Hnormalize.
  unfold phase1_surface_normalize_type_only_requirement_type in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[keyword_tree type_tree] terminator_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal keyword keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_static_type_arguments_type_tree type_tree)
    as [actual |] eqn:Htype; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ";" terminator_tree)
    as [[] |] eqn:Hterminator; try discriminate Hnormalize.
  inversion Hnormalize; subst type_value.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items keyword_tree type_tree terminator_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    keyword keyword_tree Hkeyword).
  rewrite <-
    (phase1_surface_normalize_static_type_arguments_type_tree_round_trip
      type_tree actual Htype).
  rewrite (phase1_surface_expect_literal_round_trip
    ";" terminator_tree Hterminator).
  reflexivity.
Qed.

Definition phase1_surface_normalize_boundary_representation_requirement_type
  (tree : ParseTree) : option Phase1SurfaceStaticTypeArgumentsTypeSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact4 items with
      | Some (boundary_tree, representation_tree, type_tree, terminator_tree) =>
          match phase1_surface_expect_literal "boundary" boundary_tree,
                phase1_surface_expect_literal "representation" representation_tree,
                phase1_surface_normalize_static_type_arguments_type_tree type_tree,
                phase1_surface_expect_literal ";" terminator_tree with
          | Some tt, Some tt, Some type_value, Some tt => Some type_value
          | _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem
  phase1_surface_normalize_boundary_representation_requirement_type_round_trip :
  forall tree type_value,
    phase1_surface_normalize_boundary_representation_requirement_type tree =
      Some type_value ->
    PTSequence
      [ PTLiteral "boundary";
        PTLiteral "representation";
        phase1_surface_static_type_arguments_type_spine_tree type_value;
        PTLiteral ";"
      ] = tree.
Proof.
  intros tree type_value Hnormalize.
  unfold phase1_surface_normalize_boundary_representation_requirement_type
    in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact4 items)
    as [[[[boundary_tree representation_tree] type_tree] terminator_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "boundary" boundary_tree)
    as [[] |] eqn:Hboundary; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "representation" representation_tree)
    as [[] |] eqn:Hrepresentation; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_static_type_arguments_type_tree type_tree)
    as [actual |] eqn:Htype; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ";" terminator_tree)
    as [[] |] eqn:Hterminator; try discriminate Hnormalize.
  inversion Hnormalize; subst type_value.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact4_round_trip
    items boundary_tree representation_tree type_tree terminator_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "boundary" boundary_tree Hboundary).
  rewrite (phase1_surface_expect_literal_round_trip
    "representation" representation_tree Hrepresentation).
  rewrite <-
    (phase1_surface_normalize_static_type_arguments_type_tree_round_trip
      type_tree actual Htype).
  rewrite (phase1_surface_expect_literal_round_trip
    ";" terminator_tree Hterminator).
  reflexivity.
Qed.

Inductive Phase1SurfaceGenericRequirementTypeSpine : Type :=
| Phase1GenericStructuralRequirement (selected : ParseTree)
| Phase1GenericPropositionRequirement (selected : ParseTree)
| Phase1GenericProviderRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericCallableRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericArchitectureRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericEffectsRequirement (selected : ParseTree)
| Phase1GenericAuthorityRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryRepresentationRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericRepresentationRequirement (selected : ParseTree)
| Phase1GenericPlacementRequirement (selected : ParseTree)
| Phase1GenericCostRequirement (selected : ParseTree)
| Phase1GenericEnvironmentRequirement (selected : ParseTree).

Definition phase1_surface_generic_requirement_type_spine_index
  (requirement : Phase1SurfaceGenericRequirementTypeSpine) : nat :=
  match requirement with
  | Phase1GenericStructuralRequirement _ => 0
  | Phase1GenericPropositionRequirement _ => 1
  | Phase1GenericProviderRequirement _ _ => 2
  | Phase1GenericCallableRequirement _ _ => 3
  | Phase1GenericBoundaryRequirement _ _ => 4
  | Phase1GenericArchitectureRequirement _ _ => 5
  | Phase1GenericEffectsRequirement _ => 6
  | Phase1GenericAuthorityRequirement _ => 7
  | Phase1GenericBoundaryRepresentationRequirement _ => 8
  | Phase1GenericRepresentationRequirement _ => 9
  | Phase1GenericPlacementRequirement _ => 10
  | Phase1GenericCostRequirement _ => 11
  | Phase1GenericEnvironmentRequirement _ => 12
  end.

Definition phase1_surface_generic_requirement_type_selected_tree
  (requirement : Phase1SurfaceGenericRequirementTypeSpine) : ParseTree :=
  match requirement with
  | Phase1GenericStructuralRequirement selected => selected
  | Phase1GenericPropositionRequirement selected => selected
  | Phase1GenericProviderRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "provider";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericCallableRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "callable";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "boundary";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericArchitectureRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "architecture";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericEffectsRequirement selected => selected
  | Phase1GenericAuthorityRequirement type_value =>
      PTSequence
        [ PTLiteral "authority";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryRepresentationRequirement type_value =>
      PTSequence
        [ PTLiteral "boundary";
          PTLiteral "representation";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericRepresentationRequirement selected => selected
  | Phase1GenericPlacementRequirement selected => selected
  | Phase1GenericCostRequirement selected => selected
  | Phase1GenericEnvironmentRequirement selected => selected
  end.

Definition phase1_surface_generic_requirement_type_spine_tree
  (requirement : Phase1SurfaceGenericRequirementTypeSpine) : ParseTree :=
  PTNonterminal "generic_requirement"
    (PTAlternative
      (phase1_surface_generic_requirement_type_spine_index requirement)
      (phase1_surface_generic_requirement_type_selected_tree requirement)).

Definition phase1_surface_normalize_generic_requirement_type_spine
  (requirement : Phase1SurfaceGenericRequirementSpine)
  : option Phase1SurfaceGenericRequirementTypeSpine :=
  match phase1_generic_requirement_spine_tag requirement with
  | Phase1StructuralRequirement =>
      Some
        (Phase1GenericStructuralRequirement
          (phase1_generic_requirement_spine_selected_tree requirement))
  | Phase1PropositionRequirement =>
      Some
        (Phase1GenericPropositionRequirement
          (phase1_generic_requirement_spine_selected_tree requirement))
  | Phase1ProviderRequirement =>
      match phase1_surface_normalize_named_type_requirement_type
        "provider" (phase1_generic_requirement_spine_selected_tree requirement)
      with
      | Some (name_tree, type_value) =>
          Some (Phase1GenericProviderRequirement name_tree type_value)
      | None => None
      end
  | Phase1CallableRequirement =>
      match phase1_surface_normalize_named_type_requirement_type
        "callable" (phase1_generic_requirement_spine_selected_tree requirement)
      with
      | Some (name_tree, type_value) =>
          Some (Phase1GenericCallableRequirement name_tree type_value)
      | None => None
      end
  | Phase1BoundaryRequirement =>
      match phase1_surface_normalize_named_type_requirement_type
        "boundary" (phase1_generic_requirement_spine_selected_tree requirement)
      with
      | Some (name_tree, type_value) =>
          Some (Phase1GenericBoundaryRequirement name_tree type_value)
      | None => None
      end
  | Phase1ArchitectureRequirement =>
      match phase1_surface_normalize_named_type_requirement_type
        "architecture"
        (phase1_generic_requirement_spine_selected_tree requirement)
      with
      | Some (name_tree, type_value) =>
          Some (Phase1GenericArchitectureRequirement name_tree type_value)
      | None => None
      end
  | Phase1EffectsRequirement =>
      Some
        (Phase1GenericEffectsRequirement
          (phase1_generic_requirement_spine_selected_tree requirement))
  | Phase1AuthorityRequirement =>
      match phase1_surface_normalize_type_only_requirement_type
        "authority" (phase1_generic_requirement_spine_selected_tree requirement)
      with
      | Some type_value =>
          Some (Phase1GenericAuthorityRequirement type_value)
      | None => None
      end
  | Phase1BoundaryRepresentationRequirement =>
      match phase1_surface_normalize_boundary_representation_requirement_type
        (phase1_generic_requirement_spine_selected_tree requirement)
      with
      | Some type_value =>
          Some (Phase1GenericBoundaryRepresentationRequirement type_value)
      | None => None
      end
  | Phase1RepresentationRequirement =>
      Some
        (Phase1GenericRepresentationRequirement
          (phase1_generic_requirement_spine_selected_tree requirement))
  | Phase1PlacementRequirement =>
      Some
        (Phase1GenericPlacementRequirement
          (phase1_generic_requirement_spine_selected_tree requirement))
  | Phase1CostRequirement =>
      Some
        (Phase1GenericCostRequirement
          (phase1_generic_requirement_spine_selected_tree requirement))
  | Phase1EnvironmentRequirement =>
      Some
        (Phase1GenericEnvironmentRequirement
          (phase1_generic_requirement_spine_selected_tree requirement))
  end.

Theorem phase1_surface_normalize_generic_requirement_type_spine_round_trip :
  forall requirement refined,
    phase1_surface_normalize_generic_requirement_type_spine requirement =
      Some refined ->
    phase1_surface_generic_requirement_type_spine_tree refined =
      phase1_surface_generic_requirement_spine_tree requirement.
Proof.
  intros [tag selected] refined Hnormalize.
  destruct tag; cbn in Hnormalize.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type
        "provider" selected)
      as [[name_tree type_value] |] eqn:Htyped;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_named_type_requirement_type_round_trip
        "provider" selected name_tree type_value Htyped).
    reflexivity.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type
        "callable" selected)
      as [[name_tree type_value] |] eqn:Htyped;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_named_type_requirement_type_round_trip
        "callable" selected name_tree type_value Htyped).
    reflexivity.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type
        "boundary" selected)
      as [[name_tree type_value] |] eqn:Htyped;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_named_type_requirement_type_round_trip
        "boundary" selected name_tree type_value Htyped).
    reflexivity.
  - destruct
      (phase1_surface_normalize_named_type_requirement_type
        "architecture" selected)
      as [[name_tree type_value] |] eqn:Htyped;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_named_type_requirement_type_round_trip
        "architecture" selected name_tree type_value Htyped).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct
      (phase1_surface_normalize_type_only_requirement_type
        "authority" selected)
      as [type_value |] eqn:Htyped; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_type_only_requirement_type_round_trip
        "authority" selected type_value Htyped).
    reflexivity.
  - destruct
      (phase1_surface_normalize_boundary_representation_requirement_type
        selected)
      as [type_value |] eqn:Htyped; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_boundary_representation_requirement_type_round_trip
        selected type_value Htyped).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_generic_requirement_type_tree
  (tree : ParseTree) : option Phase1SurfaceGenericRequirementTypeSpine :=
  match phase1_surface_normalize_generic_requirement_spine tree with
  | Some requirement =>
      phase1_surface_normalize_generic_requirement_type_spine requirement
  | None => None
  end.

Theorem phase1_surface_normalize_generic_requirement_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_generic_requirement_type_tree tree = Some refined ->
    phase1_surface_generic_requirement_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_generic_requirement_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_generic_requirement_spine tree)
    as [requirement |] eqn:Hrequirement; try discriminate Hnormalize.
  transitivity (phase1_surface_generic_requirement_spine_tree requirement).
  - eapply phase1_surface_normalize_generic_requirement_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_generic_requirement_spine_round_trip.
    exact Hrequirement.
Qed.
