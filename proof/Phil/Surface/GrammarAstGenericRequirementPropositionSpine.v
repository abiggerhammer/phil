From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementTypeSpine
  GrammarAstPropositionSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the proposition payloads retained by the type-refined
  generic-requirement carrier.

  The effects requirement remains opaque at this layer.
*)

Definition phase1_surface_normalize_proposition_requirement_payload
  (keyword : string) (tree : ParseTree)
  : option Phase1SurfacePropositionSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact3 items with
      | Some (keyword_tree, proposition_tree, terminator_tree) =>
          match phase1_surface_expect_literal keyword keyword_tree,
                phase1_surface_normalize_proposition_spine proposition_tree,
                phase1_surface_expect_literal ";" terminator_tree with
          | Some tt, Some proposition, Some tt => Some proposition
          | _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_proposition_requirement_payload_round_trip :
  forall keyword tree proposition,
    phase1_surface_normalize_proposition_requirement_payload keyword tree =
      Some proposition ->
    PTSequence
      [ PTLiteral keyword;
        phase1_surface_proposition_spine_tree proposition;
        PTLiteral ";"
      ] = tree.
Proof.
  intros keyword tree proposition Hnormalize.
  unfold phase1_surface_normalize_proposition_requirement_payload in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[keyword_tree proposition_tree] terminator_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal keyword keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_proposition_spine proposition_tree)
    as [actual |] eqn:Hproposition; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ";" terminator_tree)
    as [[] |] eqn:Hterminator; try discriminate Hnormalize.
  inversion Hnormalize; subst proposition.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items keyword_tree proposition_tree terminator_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    keyword keyword_tree Hkeyword).
  rewrite <-
    (phase1_surface_normalize_proposition_spine_round_trip
      proposition_tree actual Hproposition).
  rewrite (phase1_surface_expect_literal_round_trip
    ";" terminator_tree Hterminator).
  reflexivity.
Qed.

Inductive Phase1SurfaceGenericRequirementPropositionSpine : Type :=
| Phase1GenericStructuralPropositionRequirement (selected : ParseTree)
| Phase1GenericPropositionPropositionRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericProviderPropositionRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericCallablePropositionRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryPropositionRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericArchitecturePropositionRequirement
    (name_tree : ParseTree)
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericEffectsPropositionRequirement (selected : ParseTree)
| Phase1GenericAuthorityPropositionRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryRepresentationPropositionRequirement
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericRepresentationPropositionRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericPlacementPropositionRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericCostPropositionRequirement
    (proposition : Phase1SurfacePropositionSpine)
| Phase1GenericEnvironmentPropositionRequirement
    (proposition : Phase1SurfacePropositionSpine).

Definition phase1_surface_generic_requirement_proposition_spine_index
  (requirement : Phase1SurfaceGenericRequirementPropositionSpine) : nat :=
  match requirement with
  | Phase1GenericStructuralPropositionRequirement _ => 0
  | Phase1GenericPropositionPropositionRequirement _ => 1
  | Phase1GenericProviderPropositionRequirement _ _ => 2
  | Phase1GenericCallablePropositionRequirement _ _ => 3
  | Phase1GenericBoundaryPropositionRequirement _ _ => 4
  | Phase1GenericArchitecturePropositionRequirement _ _ => 5
  | Phase1GenericEffectsPropositionRequirement _ => 6
  | Phase1GenericAuthorityPropositionRequirement _ => 7
  | Phase1GenericBoundaryRepresentationPropositionRequirement _ => 8
  | Phase1GenericRepresentationPropositionRequirement _ => 9
  | Phase1GenericPlacementPropositionRequirement _ => 10
  | Phase1GenericCostPropositionRequirement _ => 11
  | Phase1GenericEnvironmentPropositionRequirement _ => 12
  end.

Definition phase1_surface_generic_requirement_proposition_selected_tree
  (requirement : Phase1SurfaceGenericRequirementPropositionSpine) : ParseTree :=
  match requirement with
  | Phase1GenericStructuralPropositionRequirement selected => selected
  | Phase1GenericPropositionPropositionRequirement proposition =>
      PTSequence
        [ PTLiteral "proposition";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericProviderPropositionRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "provider";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericCallablePropositionRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "callable";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryPropositionRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "boundary";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericArchitecturePropositionRequirement name_tree type_value =>
      PTSequence
        [ PTLiteral "architecture";
          name_tree;
          PTLiteral ":";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericEffectsPropositionRequirement selected => selected
  | Phase1GenericAuthorityPropositionRequirement type_value =>
      PTSequence
        [ PTLiteral "authority";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericBoundaryRepresentationPropositionRequirement type_value =>
      PTSequence
        [ PTLiteral "boundary";
          PTLiteral "representation";
          phase1_surface_static_type_arguments_type_spine_tree type_value;
          PTLiteral ";"
        ]
  | Phase1GenericRepresentationPropositionRequirement proposition =>
      PTSequence
        [ PTLiteral "representation";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericPlacementPropositionRequirement proposition =>
      PTSequence
        [ PTLiteral "placement";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericCostPropositionRequirement proposition =>
      PTSequence
        [ PTLiteral "cost";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  | Phase1GenericEnvironmentPropositionRequirement proposition =>
      PTSequence
        [ PTLiteral "environment";
          phase1_surface_proposition_spine_tree proposition;
          PTLiteral ";"
        ]
  end.

Definition phase1_surface_generic_requirement_proposition_spine_tree
  (requirement : Phase1SurfaceGenericRequirementPropositionSpine) : ParseTree :=
  PTNonterminal "generic_requirement"
    (PTAlternative
      (phase1_surface_generic_requirement_proposition_spine_index requirement)
      (phase1_surface_generic_requirement_proposition_selected_tree requirement)).

Definition phase1_surface_normalize_generic_requirement_proposition_spine
  (requirement : Phase1SurfaceGenericRequirementTypeSpine)
  : option Phase1SurfaceGenericRequirementPropositionSpine :=
  match requirement with
  | Phase1GenericStructuralRequirement selected =>
      Some (Phase1GenericStructuralPropositionRequirement selected)
  | Phase1GenericPropositionRequirement selected =>
      match phase1_surface_normalize_proposition_requirement_payload
        "proposition" selected with
      | Some proposition =>
          Some (Phase1GenericPropositionPropositionRequirement proposition)
      | None => None
      end
  | Phase1GenericProviderRequirement name_tree type_value =>
      Some (Phase1GenericProviderPropositionRequirement name_tree type_value)
  | Phase1GenericCallableRequirement name_tree type_value =>
      Some (Phase1GenericCallablePropositionRequirement name_tree type_value)
  | Phase1GenericBoundaryRequirement name_tree type_value =>
      Some (Phase1GenericBoundaryPropositionRequirement name_tree type_value)
  | Phase1GenericArchitectureRequirement name_tree type_value =>
      Some
        (Phase1GenericArchitecturePropositionRequirement name_tree type_value)
  | Phase1GenericEffectsRequirement selected =>
      Some (Phase1GenericEffectsPropositionRequirement selected)
  | Phase1GenericAuthorityRequirement type_value =>
      Some (Phase1GenericAuthorityPropositionRequirement type_value)
  | Phase1GenericBoundaryRepresentationRequirement type_value =>
      Some
        (Phase1GenericBoundaryRepresentationPropositionRequirement type_value)
  | Phase1GenericRepresentationRequirement selected =>
      match phase1_surface_normalize_proposition_requirement_payload
        "representation" selected with
      | Some proposition =>
          Some (Phase1GenericRepresentationPropositionRequirement proposition)
      | None => None
      end
  | Phase1GenericPlacementRequirement selected =>
      match phase1_surface_normalize_proposition_requirement_payload
        "placement" selected with
      | Some proposition =>
          Some (Phase1GenericPlacementPropositionRequirement proposition)
      | None => None
      end
  | Phase1GenericCostRequirement selected =>
      match phase1_surface_normalize_proposition_requirement_payload
        "cost" selected with
      | Some proposition =>
          Some (Phase1GenericCostPropositionRequirement proposition)
      | None => None
      end
  | Phase1GenericEnvironmentRequirement selected =>
      match phase1_surface_normalize_proposition_requirement_payload
        "environment" selected with
      | Some proposition =>
          Some (Phase1GenericEnvironmentPropositionRequirement proposition)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_generic_requirement_proposition_spine_round_trip :
  forall requirement refined,
    phase1_surface_normalize_generic_requirement_proposition_spine requirement =
      Some refined ->
    phase1_surface_generic_requirement_proposition_spine_tree refined =
      phase1_surface_generic_requirement_type_spine_tree requirement.
Proof.
  intros requirement refined Hnormalize.
  destruct requirement; cbn in Hnormalize.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct
      (phase1_surface_normalize_proposition_requirement_payload
        "proposition" selected)
      as [proposition |] eqn:Hproposition; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_proposition_requirement_payload_round_trip
        "proposition" selected proposition Hproposition).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct
      (phase1_surface_normalize_proposition_requirement_payload
        "representation" selected)
      as [proposition |] eqn:Hproposition; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_proposition_requirement_payload_round_trip
        "representation" selected proposition Hproposition).
    reflexivity.
  - destruct
      (phase1_surface_normalize_proposition_requirement_payload
        "placement" selected)
      as [proposition |] eqn:Hproposition; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_proposition_requirement_payload_round_trip
        "placement" selected proposition Hproposition).
    reflexivity.
  - destruct
      (phase1_surface_normalize_proposition_requirement_payload
        "cost" selected)
      as [proposition |] eqn:Hproposition; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_proposition_requirement_payload_round_trip
        "cost" selected proposition Hproposition).
    reflexivity.
  - destruct
      (phase1_surface_normalize_proposition_requirement_payload
        "environment" selected)
      as [proposition |] eqn:Hproposition; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_proposition_requirement_payload_round_trip
        "environment" selected proposition Hproposition).
    reflexivity.
Qed.

Definition phase1_surface_normalize_generic_requirement_proposition_tree
  (tree : ParseTree)
  : option Phase1SurfaceGenericRequirementPropositionSpine :=
  match phase1_surface_normalize_generic_requirement_type_tree tree with
  | Some requirement =>
      phase1_surface_normalize_generic_requirement_proposition_spine requirement
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_requirement_proposition_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_generic_requirement_proposition_tree tree =
      Some refined ->
    phase1_surface_generic_requirement_proposition_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_generic_requirement_proposition_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_generic_requirement_type_tree tree)
    as [requirement |] eqn:Hrequirement; try discriminate Hnormalize.
  transitivity (phase1_surface_generic_requirement_type_spine_tree requirement).
  - eapply
      phase1_surface_normalize_generic_requirement_proposition_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_generic_requirement_type_tree_round_trip.
    exact Hrequirement.
Qed.
