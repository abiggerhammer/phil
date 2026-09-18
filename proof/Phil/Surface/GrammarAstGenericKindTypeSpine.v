From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericParamsSpine
  GrammarAstStaticTypeArgumentCarrierSpine.

Open Scope string_scope.

(*
  Open the nested type_expression payloads retained by the four typed generic
  kinds.  The five primitive generic kinds have no nested payload and are
  preserved as closed constructors.
*)

Definition phase1_surface_normalize_typed_generic_kind_type
  (keyword : string) (tree : ParseTree)
  : option Phase1SurfaceStaticTypeArgumentsTypeSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (keyword_tree, type_tree) =>
          match phase1_surface_expect_literal keyword keyword_tree,
                phase1_surface_normalize_static_type_arguments_type_tree type_tree
          with
          | Some tt, Some type_value => Some type_value
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_typed_generic_kind_type_round_trip :
  forall keyword tree type_value,
    phase1_surface_normalize_typed_generic_kind_type keyword tree =
      Some type_value ->
    PTSequence
      [ PTLiteral keyword;
        phase1_surface_static_type_arguments_type_spine_tree type_value
      ] = tree.
Proof.
  intros keyword tree type_value Hnormalize.
  unfold phase1_surface_normalize_typed_generic_kind_type in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[keyword_tree type_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal keyword keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_static_type_arguments_type_tree type_tree)
    as [actual |] eqn:Htype; try discriminate Hnormalize.
  inversion Hnormalize; subst actual.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items keyword_tree type_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    keyword keyword_tree Hkeyword).
  rewrite <-
    (phase1_surface_normalize_static_type_arguments_type_tree_round_trip
      type_tree type_value Htype).
  reflexivity.
Qed.

Inductive Phase1SurfaceGenericKindTypeSpine : Type :=
| Phase1GenericTypeKind
| Phase1GenericNatKind
| Phase1GenericSessionKind
| Phase1GenericMessageKind
| Phase1GenericEffectsKind
| Phase1GenericProviderKind
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericCallableKind
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericBoundaryKind
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine)
| Phase1GenericArchitectureKind
    (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine).

Definition phase1_surface_generic_kind_type_spine_index
  (kind : Phase1SurfaceGenericKindTypeSpine) : nat :=
  match kind with
  | Phase1GenericTypeKind => 0
  | Phase1GenericNatKind => 1
  | Phase1GenericSessionKind => 2
  | Phase1GenericMessageKind => 3
  | Phase1GenericEffectsKind => 4
  | Phase1GenericProviderKind _ => 5
  | Phase1GenericCallableKind _ => 6
  | Phase1GenericBoundaryKind _ => 7
  | Phase1GenericArchitectureKind _ => 8
  end.

Definition phase1_surface_generic_kind_type_selected_tree
  (kind : Phase1SurfaceGenericKindTypeSpine) : ParseTree :=
  match kind with
  | Phase1GenericTypeKind => PTLiteral "Type"
  | Phase1GenericNatKind => PTLiteral "Nat"
  | Phase1GenericSessionKind => PTLiteral "Session"
  | Phase1GenericMessageKind => PTLiteral "Message"
  | Phase1GenericEffectsKind => PTLiteral "Effects"
  | Phase1GenericProviderKind type_value =>
      PTSequence
        [ PTLiteral "provider";
          phase1_surface_static_type_arguments_type_spine_tree type_value
        ]
  | Phase1GenericCallableKind type_value =>
      PTSequence
        [ PTLiteral "callable";
          phase1_surface_static_type_arguments_type_spine_tree type_value
        ]
  | Phase1GenericBoundaryKind type_value =>
      PTSequence
        [ PTLiteral "boundary";
          phase1_surface_static_type_arguments_type_spine_tree type_value
        ]
  | Phase1GenericArchitectureKind type_value =>
      PTSequence
        [ PTLiteral "architecture";
          phase1_surface_static_type_arguments_type_spine_tree type_value
        ]
  end.

Definition phase1_surface_generic_kind_type_spine_tree
  (kind : Phase1SurfaceGenericKindTypeSpine) : ParseTree :=
  PTNonterminal "generic_kind"
    (PTAlternative
      (phase1_surface_generic_kind_type_spine_index kind)
      (phase1_surface_generic_kind_type_selected_tree kind)).

Definition phase1_surface_normalize_generic_kind_type_spine
  (kind : Phase1SurfaceGenericKindSpine)
  : option Phase1SurfaceGenericKindTypeSpine :=
  match phase1_generic_kind_spine_tag kind with
  | Phase1TypeGenericKind => Some Phase1GenericTypeKind
  | Phase1NatGenericKind => Some Phase1GenericNatKind
  | Phase1SessionGenericKind => Some Phase1GenericSessionKind
  | Phase1MessageGenericKind => Some Phase1GenericMessageKind
  | Phase1EffectsGenericKind => Some Phase1GenericEffectsKind
  | Phase1ProviderGenericKind =>
      match
        phase1_surface_normalize_typed_generic_kind_type
          "provider" (phase1_generic_kind_spine_selected_tree kind)
      with
      | Some type_value => Some (Phase1GenericProviderKind type_value)
      | None => None
      end
  | Phase1CallableGenericKind =>
      match
        phase1_surface_normalize_typed_generic_kind_type
          "callable" (phase1_generic_kind_spine_selected_tree kind)
      with
      | Some type_value => Some (Phase1GenericCallableKind type_value)
      | None => None
      end
  | Phase1BoundaryGenericKind =>
      match
        phase1_surface_normalize_typed_generic_kind_type
          "boundary" (phase1_generic_kind_spine_selected_tree kind)
      with
      | Some type_value => Some (Phase1GenericBoundaryKind type_value)
      | None => None
      end
  | Phase1ArchitectureGenericKind =>
      match
        phase1_surface_normalize_typed_generic_kind_type
          "architecture" (phase1_generic_kind_spine_selected_tree kind)
      with
      | Some type_value => Some (Phase1GenericArchitectureKind type_value)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_generic_kind_type_spine_round_trip :
  forall kind refined,
    phase1_surface_normalize_generic_kind_type_spine kind = Some refined ->
    phase1_surface_generic_kind_type_spine_tree refined =
      phase1_surface_generic_kind_spine_tree kind.
Proof.
  intros [tag selected] refined Hnormalize.
  destruct tag; cbn in Hnormalize.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type
        "provider" selected)
      as [type_value |] eqn:Htype; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_typed_generic_kind_type_round_trip
        "provider" selected type_value Htype).
    reflexivity.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type
        "callable" selected)
      as [type_value |] eqn:Htype; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_typed_generic_kind_type_round_trip
        "callable" selected type_value Htype).
    reflexivity.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type
        "boundary" selected)
      as [type_value |] eqn:Htype; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_typed_generic_kind_type_round_trip
        "boundary" selected type_value Htype).
    reflexivity.
  - destruct
      (phase1_surface_normalize_typed_generic_kind_type
        "architecture" selected)
      as [type_value |] eqn:Htype; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_typed_generic_kind_type_round_trip
        "architecture" selected type_value Htype).
    reflexivity.
Qed.

Definition phase1_surface_normalize_generic_kind_type_tree
  (tree : ParseTree) : option Phase1SurfaceGenericKindTypeSpine :=
  match phase1_surface_normalize_generic_kind_spine tree with
  | Some kind => phase1_surface_normalize_generic_kind_type_spine kind
  | None => None
  end.

Theorem phase1_surface_normalize_generic_kind_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_generic_kind_type_tree tree = Some refined ->
    phase1_surface_generic_kind_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_generic_kind_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_generic_kind_spine tree)
    as [kind |] eqn:Hkind; try discriminate Hnormalize.
  transitivity (phase1_surface_generic_kind_spine_tree kind).
  - eapply phase1_surface_normalize_generic_kind_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_generic_kind_spine_round_trip.
    exact Hkind.
Qed.
