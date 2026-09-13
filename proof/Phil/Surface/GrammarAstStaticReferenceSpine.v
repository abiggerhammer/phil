From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRefinementTupleTypePayloadSpine
  GrammarAstSourceHeader
  GrammarAstGenericRequirementsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Static-reference spine correspondence.

  This layer normalizes the complete dotted qualified name and the
  static_reference / named_type wrappers.  The optional static_arguments
  subtree is retained exactly for the dedicated static-argument refinement.
*)

Definition phase1_surface_optional_static_arguments_tree
  (arguments : option ParseTree) : ParseTree :=
  match arguments with
  | None => PTOptionalNone
  | Some arguments_tree => PTOptionalSome arguments_tree
  end.

Definition phase1_surface_normalize_optional_static_arguments
  (tree : ParseTree) : option (option ParseTree) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some arguments_tree) =>
      match
        phase1_surface_validate_named_node
          "static_arguments" arguments_tree
      with
      | Some tt => Some (Some arguments_tree)
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_static_arguments_round_trip :
  forall tree arguments,
    phase1_surface_normalize_optional_static_arguments tree = Some arguments ->
    phase1_surface_optional_static_arguments_tree arguments = tree.
Proof.
  intros tree arguments Hnormalize.
  unfold phase1_surface_normalize_optional_static_arguments in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[arguments_tree |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct
      (phase1_surface_validate_named_node
        "static_arguments" arguments_tree)
      as [[] |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst arguments.
    unfold phase1_surface_optional_static_arguments_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some arguments_tree) Hoptional).
    reflexivity.
  - inversion Hnormalize; subst arguments.
    unfold phase1_surface_optional_static_arguments_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceStaticReferenceSpine : Type := {
  phase1_static_reference_spine_name : Phase1SurfaceNameList;
  phase1_static_reference_spine_arguments : option ParseTree
}.

Definition phase1_surface_static_reference_spine_tree
  (reference : Phase1SurfaceStaticReferenceSpine) : ParseTree :=
  PTNonterminal "static_reference"
    (PTSequence
      [ phase1_surface_qualified_name_tree
          (phase1_static_reference_spine_name reference);
        phase1_surface_optional_static_arguments_tree
          (phase1_static_reference_spine_arguments reference)
      ]).

Definition phase1_surface_normalize_static_reference_spine
  (tree : ParseTree) : option Phase1SurfaceStaticReferenceSpine :=
  match phase1_surface_expect_nonterminal "static_reference" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (name_tree, arguments_tree) =>
              match
                phase1_surface_normalize_qualified_name name_tree,
                phase1_surface_normalize_optional_static_arguments
                  arguments_tree
              with
              | Some name, Some arguments =>
                  Some
                    {| phase1_static_reference_spine_name := name;
                       phase1_static_reference_spine_arguments := arguments |}
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_static_reference_spine_round_trip :
  forall tree reference,
    phase1_surface_normalize_static_reference_spine tree = Some reference ->
    phase1_surface_static_reference_spine_tree reference = tree.
Proof.
  intros tree reference Hnormalize.
  unfold phase1_surface_normalize_static_reference_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "static_reference" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[name_tree arguments_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_normalize_qualified_name name_tree)
    as [name |] eqn:Hname; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_optional_static_arguments arguments_tree)
    as [arguments |] eqn:Harguments; try discriminate Hnormalize.
  inversion Hnormalize; subst reference.
  pose proof
    (phase1_surface_normalize_name_list_round_trip
      "qualified_name" "." name_tree name Hname) as Hname_round_trip.
  pose proof
    (phase1_surface_normalize_optional_static_arguments_round_trip
      arguments_tree arguments Harguments) as Harguments_round_trip.
  unfold phase1_surface_static_reference_spine_tree.
  cbn.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "static_reference" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items name_tree arguments_tree Hitems).
  rewrite Hname_round_trip.
  rewrite Harguments_round_trip.
  reflexivity.
Qed.

Definition phase1_surface_named_type_spine_tree
  (reference : Phase1SurfaceStaticReferenceSpine) : ParseTree :=
  PTNonterminal "named_type"
    (phase1_surface_static_reference_spine_tree reference).

Definition phase1_surface_normalize_named_type_spine
  (tree : ParseTree) : option Phase1SurfaceStaticReferenceSpine :=
  match phase1_surface_expect_nonterminal "named_type" tree with
  | Some body => phase1_surface_normalize_static_reference_spine body
  | None => None
  end.

Theorem phase1_surface_normalize_named_type_spine_round_trip :
  forall tree reference,
    phase1_surface_normalize_named_type_spine tree = Some reference ->
    phase1_surface_named_type_spine_tree reference = tree.
Proof.
  intros tree reference Hnormalize.
  unfold phase1_surface_normalize_named_type_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "named_type" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_static_reference_spine_round_trip
      body reference Hnormalize) as Hreference.
  unfold phase1_surface_named_type_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "named_type" tree body Hnode).
  rewrite Hreference.
  reflexivity.
Qed.

Inductive Phase1SurfaceStaticReferenceTypeSpine : Type :=
| Phase1StaticReferenceNonreferenceType
    (value : Phase1SurfaceRefinementTupleNonreferenceTypeSpine)
| Phase1StaticReferenceNamedType
    (reference : Phase1SurfaceStaticReferenceSpine).

Definition phase1_surface_static_reference_type_spine_tree
  (type_value : Phase1SurfaceStaticReferenceTypeSpine) : ParseTree :=
  match type_value with
  | Phase1StaticReferenceNonreferenceType nonreference =>
      PTNonterminal "type_expression"
        (PTAlternative 0
          (phase1_surface_refinement_tuple_nonreference_type_spine_tree
            nonreference))
  | Phase1StaticReferenceNamedType reference =>
      PTNonterminal "type_expression"
        (PTAlternative 1
          (phase1_surface_named_type_spine_tree reference))
  end.

Definition phase1_surface_normalize_static_reference_type_spine
  (type_value : Phase1SurfaceRefinementTupleTypeSpine)
  : option Phase1SurfaceStaticReferenceTypeSpine :=
  match type_value with
  | Phase1RefinementTupleNonreferenceTypeSpine nonreference =>
      Some (Phase1StaticReferenceNonreferenceType nonreference)
  | Phase1RefinementTupleNamedTypeSpine named_tree =>
      match phase1_surface_normalize_named_type_spine named_tree with
      | Some reference => Some (Phase1StaticReferenceNamedType reference)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_static_reference_type_spine_round_trip :
  forall type_value refined,
    phase1_surface_normalize_static_reference_type_spine type_value =
      Some refined ->
    phase1_surface_static_reference_type_spine_tree refined =
      phase1_surface_refinement_tuple_type_spine_tree type_value.
Proof.
  intros type_value refined Hnormalize.
  destruct type_value as [nonreference | named_tree].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_named_type_spine named_tree)
      as [reference |] eqn:Hnamed; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_normalize_named_type_spine_round_trip
      named_tree reference Hnamed).
    reflexivity.
Qed.

Definition phase1_surface_normalize_static_reference_type_tree
  (tree : ParseTree) : option Phase1SurfaceStaticReferenceTypeSpine :=
  match phase1_surface_normalize_refinement_tuple_type_tree tree with
  | Some type_value =>
      phase1_surface_normalize_static_reference_type_spine type_value
  | None => None
  end.

Theorem phase1_surface_normalize_static_reference_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_static_reference_type_tree tree = Some refined ->
    phase1_surface_static_reference_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_static_reference_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_refinement_tuple_type_tree tree)
    as [type_value |] eqn:Htype; try discriminate Hnormalize.
  transitivity (phase1_surface_refinement_tuple_type_spine_tree type_value).
  - eapply phase1_surface_normalize_static_reference_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_refinement_tuple_type_tree_round_trip.
    exact Htype.
Qed.
