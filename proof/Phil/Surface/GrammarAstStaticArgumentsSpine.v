From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstStaticReferenceSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Static-argument list and category correspondence.

  The four static_argument alternatives are normalized to an explicit tag while
  retaining each selected payload exactly.  This slice also normalizes the
  bracketed optional comma-separated list and lifts it back through
  static_reference / named_type / type_expression.
*)

Inductive Phase1SurfaceStaticArgumentTag : Type :=
| Phase1StaticTypeArgument
| Phase1StaticSessionArgument
| Phase1StaticValueArgument
| Phase1StaticEffectSetArgument.

Definition phase1_surface_static_argument_tag_index
  (tag : Phase1SurfaceStaticArgumentTag) : nat :=
  match tag with
  | Phase1StaticTypeArgument => 0
  | Phase1StaticSessionArgument => 1
  | Phase1StaticValueArgument => 2
  | Phase1StaticEffectSetArgument => 3
  end.

Definition phase1_surface_static_argument_tag_name
  (tag : Phase1SurfaceStaticArgumentTag) : string :=
  match tag with
  | Phase1StaticTypeArgument => "nonreference_type_expression"
  | Phase1StaticSessionArgument => "nonreference_session_expression"
  | Phase1StaticValueArgument => "static_value_expression"
  | Phase1StaticEffectSetArgument => "effect_set_literal"
  end.

Record Phase1SurfaceStaticArgumentSpine : Type := {
  phase1_static_argument_spine_tag : Phase1SurfaceStaticArgumentTag;
  phase1_static_argument_spine_selected_tree : ParseTree
}.

Definition phase1_surface_static_argument_spine_tree
  (argument : Phase1SurfaceStaticArgumentSpine) : ParseTree :=
  PTNonterminal "static_argument"
    (PTAlternative
      (phase1_surface_static_argument_tag_index
        (phase1_static_argument_spine_tag argument))
      (phase1_static_argument_spine_selected_tree argument)).

Definition phase1_surface_validate_static_argument_selected
  (tag : Phase1SurfaceStaticArgumentTag)
  (tree : ParseTree) : option unit :=
  phase1_surface_validate_named_node
    (phase1_surface_static_argument_tag_name tag) tree.

Definition phase1_surface_normalize_static_argument_spine
  (tree : ParseTree) : option Phase1SurfaceStaticArgumentSpine :=
  match phase1_surface_expect_nonterminal "static_argument" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          match
            phase1_surface_validate_static_argument_selected
              Phase1StaticTypeArgument selected
          with
          | Some tt =>
              Some
                {| phase1_static_argument_spine_tag :=
                     Phase1StaticTypeArgument;
                   phase1_static_argument_spine_selected_tree := selected |}
          | None => None
          end
      | Some (1, selected) =>
          match
            phase1_surface_validate_static_argument_selected
              Phase1StaticSessionArgument selected
          with
          | Some tt =>
              Some
                {| phase1_static_argument_spine_tag :=
                     Phase1StaticSessionArgument;
                   phase1_static_argument_spine_selected_tree := selected |}
          | None => None
          end
      | Some (2, selected) =>
          match
            phase1_surface_validate_static_argument_selected
              Phase1StaticValueArgument selected
          with
          | Some tt =>
              Some
                {| phase1_static_argument_spine_tag :=
                     Phase1StaticValueArgument;
                   phase1_static_argument_spine_selected_tree := selected |}
          | None => None
          end
      | Some (3, selected) =>
          match
            phase1_surface_validate_static_argument_selected
              Phase1StaticEffectSetArgument selected
          with
          | Some tt =>
              Some
                {| phase1_static_argument_spine_tag :=
                     Phase1StaticEffectSetArgument;
                   phase1_static_argument_spine_selected_tree := selected |}
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_static_argument_spine_round_trip :
  forall tree argument,
    phase1_surface_normalize_static_argument_spine tree = Some argument ->
    phase1_surface_static_argument_spine_tree argument = tree.
Proof.
  intros tree argument Hnormalize.
  unfold phase1_surface_normalize_static_argument_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "static_argument" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - cbn in Hnormalize.
    destruct
      (phase1_surface_validate_static_argument_selected
        Phase1StaticTypeArgument selected)
      as [[] |] eqn:Hselected; try discriminate Hnormalize.
    inversion Hnormalize; subst argument.
    unfold phase1_surface_static_argument_spine_tree.
    cbn.
    rewrite (phase1_surface_expect_nonterminal_round_trip
      "static_argument" tree body Hnode).
    rewrite (phase1_surface_expect_alternative_round_trip
      body 0 selected Halternative).
    reflexivity.
  - destruct index as [|index].
    + cbn in Hnormalize.
      destruct
        (phase1_surface_validate_static_argument_selected
          Phase1StaticSessionArgument selected)
        as [[] |] eqn:Hselected; try discriminate Hnormalize.
      inversion Hnormalize; subst argument.
      unfold phase1_surface_static_argument_spine_tree.
      cbn.
      rewrite (phase1_surface_expect_nonterminal_round_trip
        "static_argument" tree body Hnode).
      rewrite (phase1_surface_expect_alternative_round_trip
        body 1 selected Halternative).
      reflexivity.
    + destruct index as [|index].
      * cbn in Hnormalize.
        destruct
          (phase1_surface_validate_static_argument_selected
            Phase1StaticValueArgument selected)
          as [[] |] eqn:Hselected; try discriminate Hnormalize.
        inversion Hnormalize; subst argument.
        unfold phase1_surface_static_argument_spine_tree.
        cbn.
        rewrite (phase1_surface_expect_nonterminal_round_trip
          "static_argument" tree body Hnode).
        rewrite (phase1_surface_expect_alternative_round_trip
          body 2 selected Halternative).
        reflexivity.
      * destruct index as [|index].
        -- cbn in Hnormalize.
           destruct
             (phase1_surface_validate_static_argument_selected
               Phase1StaticEffectSetArgument selected)
             as [[] |] eqn:Hselected; try discriminate Hnormalize.
           inversion Hnormalize; subst argument.
           unfold phase1_surface_static_argument_spine_tree.
           cbn.
           rewrite (phase1_surface_expect_nonterminal_round_trip
             "static_argument" tree body Hnode).
           rewrite (phase1_surface_expect_alternative_round_trip
             body 3 selected Halternative).
           reflexivity.
        -- discriminate Hnormalize.
Qed.

Definition phase1_surface_static_argument_suffix_tree
  (argument : Phase1SurfaceStaticArgumentSpine) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_static_argument_spine_tree argument
    ].

Definition phase1_surface_normalize_static_argument_suffix
  (tree : ParseTree) : option Phase1SurfaceStaticArgumentSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (comma_tree, argument_tree) =>
          match phase1_surface_expect_literal "," comma_tree with
          | Some tt => phase1_surface_normalize_static_argument_spine argument_tree
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_static_argument_suffix_round_trip :
  forall tree argument,
    phase1_surface_normalize_static_argument_suffix tree = Some argument ->
    phase1_surface_static_argument_suffix_tree argument = tree.
Proof.
  intros tree argument Hnormalize.
  unfold phase1_surface_normalize_static_argument_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[comma_tree argument_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma_tree)
    as [[] |] eqn:Hcomma; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_static_argument_spine_round_trip
      argument_tree argument Hnormalize) as Hargument.
  unfold phase1_surface_static_argument_suffix_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items comma_tree argument_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "," comma_tree Hcomma).
  rewrite Hargument.
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_static_argument_suffixes
  (trees : list ParseTree) : option (list Phase1SurfaceStaticArgumentSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_static_argument_suffix tree,
            phase1_surface_normalize_static_argument_suffixes rest with
      | Some argument, Some arguments => Some (argument :: arguments)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_static_argument_suffixes_round_trip :
  forall trees arguments,
    phase1_surface_normalize_static_argument_suffixes trees = Some arguments ->
    map phase1_surface_static_argument_suffix_tree arguments = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros arguments Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst arguments.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_static_argument_suffix tree)
      as [argument |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_static_argument_suffixes rest)
      as [rest_arguments |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst arguments.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_static_argument_suffix_round_trip.
      exact Htree.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceStaticArgumentListSpine : Type := {
  phase1_static_argument_list_spine_first : Phase1SurfaceStaticArgumentSpine;
  phase1_static_argument_list_spine_rest : list Phase1SurfaceStaticArgumentSpine
}.

Definition phase1_surface_static_argument_list_spine_tree
  (arguments : Phase1SurfaceStaticArgumentListSpine) : ParseTree :=
  PTSequence
    [ phase1_surface_static_argument_spine_tree
        (phase1_static_argument_list_spine_first arguments);
      PTRepetition
        (map phase1_surface_static_argument_suffix_tree
          (phase1_static_argument_list_spine_rest arguments))
    ].

Definition phase1_surface_normalize_static_argument_list_spine
  (tree : ParseTree) : option Phase1SurfaceStaticArgumentListSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (first_tree, rest_tree) =>
          match phase1_surface_expect_repetition rest_tree with
          | Some rest_trees =>
              match
                phase1_surface_normalize_static_argument_spine first_tree,
                phase1_surface_normalize_static_argument_suffixes rest_trees
              with
              | Some first, Some rest =>
                  Some
                    {| phase1_static_argument_list_spine_first := first;
                       phase1_static_argument_list_spine_rest := rest |}
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_static_argument_list_spine_round_trip :
  forall tree arguments,
    phase1_surface_normalize_static_argument_list_spine tree = Some arguments ->
    phase1_surface_static_argument_list_spine_tree arguments = tree.
Proof.
  intros tree arguments Hnormalize.
  unfold phase1_surface_normalize_static_argument_list_spine in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[first_tree rest_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition rest_tree)
    as [rest_trees |] eqn:Hrepetition; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_static_argument_spine first_tree)
    as [first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_static_argument_suffixes rest_trees)
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst arguments.
  unfold phase1_surface_static_argument_list_spine_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items first_tree rest_tree Hitems).
  rewrite (phase1_surface_normalize_static_argument_spine_round_trip
    first_tree first Hfirst).
  rewrite (phase1_surface_expect_repetition_round_trip
    rest_tree rest_trees Hrepetition).
  rewrite (phase1_surface_normalize_static_argument_suffixes_round_trip
    rest_trees rest Hrest).
  reflexivity.
Qed.

Definition phase1_surface_optional_static_argument_list_tree
  (arguments : option Phase1SurfaceStaticArgumentListSpine) : ParseTree :=
  match arguments with
  | None => PTOptionalNone
  | Some argument_list =>
      PTOptionalSome
        (phase1_surface_static_argument_list_spine_tree argument_list)
  end.

Definition phase1_surface_normalize_optional_static_argument_list
  (tree : ParseTree) : option (option Phase1SurfaceStaticArgumentListSpine) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some argument_list_tree) =>
      match
        phase1_surface_normalize_static_argument_list_spine argument_list_tree
      with
      | Some arguments => Some (Some arguments)
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_static_argument_list_round_trip :
  forall tree arguments,
    phase1_surface_normalize_optional_static_argument_list tree = Some arguments ->
    phase1_surface_optional_static_argument_list_tree arguments = tree.
Proof.
  intros tree arguments Hnormalize.
  unfold phase1_surface_normalize_optional_static_argument_list in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[argument_list_tree |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct
      (phase1_surface_normalize_static_argument_list_spine argument_list_tree)
      as [argument_list |] eqn:Hlist; try discriminate Hnormalize.
    inversion Hnormalize; subst arguments.
    unfold phase1_surface_optional_static_argument_list_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some argument_list_tree) Hoptional).
    rewrite (phase1_surface_normalize_static_argument_list_spine_round_trip
      argument_list_tree argument_list Hlist).
    reflexivity.
  - inversion Hnormalize; subst arguments.
    unfold phase1_surface_optional_static_argument_list_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceStaticArgumentsSpine : Type := {
  phase1_static_arguments_spine_items : option Phase1SurfaceStaticArgumentListSpine
}.

Definition phase1_surface_static_arguments_spine_tree
  (arguments : Phase1SurfaceStaticArgumentsSpine) : ParseTree :=
  PTNonterminal "static_arguments"
    (PTSequence
      [ PTLiteral "[";
        phase1_surface_optional_static_argument_list_tree
          (phase1_static_arguments_spine_items arguments);
        PTLiteral "]"
      ]).

Definition phase1_surface_normalize_static_arguments_spine
  (tree : ParseTree) : option Phase1SurfaceStaticArgumentsSpine :=
  match phase1_surface_expect_nonterminal "static_arguments" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact3 items with
          | Some (open_tree, arguments_tree, close_tree) =>
              match
                phase1_surface_expect_literal "[" open_tree,
                phase1_surface_normalize_optional_static_argument_list
                  arguments_tree,
                phase1_surface_expect_literal "]" close_tree
              with
              | Some tt, Some arguments, Some tt =>
                  Some
                    {| phase1_static_arguments_spine_items := arguments |}
              | _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_static_arguments_spine_round_trip :
  forall tree arguments,
    phase1_surface_normalize_static_arguments_spine tree = Some arguments ->
    phase1_surface_static_arguments_spine_tree arguments = tree.
Proof.
  intros tree arguments Hnormalize.
  unfold phase1_surface_normalize_static_arguments_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "static_arguments" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[open_tree arguments_tree] close_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "[" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_optional_static_argument_list arguments_tree)
    as [argument_list |] eqn:Harguments; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "]" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  inversion Hnormalize; subst arguments.
  unfold phase1_surface_static_arguments_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "static_arguments" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items open_tree arguments_tree close_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "[" open_tree Hopen).
  rewrite (phase1_surface_normalize_optional_static_argument_list_round_trip
    arguments_tree argument_list Harguments).
  rewrite (phase1_surface_expect_literal_round_trip "]" close_tree Hclose).
  reflexivity.
Qed.

Record Phase1SurfaceStaticArgumentsReferenceSpine : Type := {
  phase1_static_arguments_reference_spine_name : Phase1SurfaceNameList;
  phase1_static_arguments_reference_spine_arguments :
    option Phase1SurfaceStaticArgumentsSpine
}.

Definition phase1_surface_static_arguments_reference_spine_tree
  (reference : Phase1SurfaceStaticArgumentsReferenceSpine) : ParseTree :=
  PTNonterminal "static_reference"
    (PTSequence
      [ phase1_surface_qualified_name_tree
          (phase1_static_arguments_reference_spine_name reference);
        match phase1_static_arguments_reference_spine_arguments reference with
        | None => PTOptionalNone
        | Some arguments =>
            PTOptionalSome
              (phase1_surface_static_arguments_spine_tree arguments)
        end
      ]).

Definition phase1_surface_normalize_static_arguments_reference_spine
  (reference : Phase1SurfaceStaticReferenceSpine)
  : option Phase1SurfaceStaticArgumentsReferenceSpine :=
  match phase1_static_reference_spine_arguments reference with
  | None =>
      Some
        {| phase1_static_arguments_reference_spine_name :=
             phase1_static_reference_spine_name reference;
           phase1_static_arguments_reference_spine_arguments := None |}
  | Some arguments_tree =>
      match phase1_surface_normalize_static_arguments_spine arguments_tree with
      | Some arguments =>
          Some
            {| phase1_static_arguments_reference_spine_name :=
                 phase1_static_reference_spine_name reference;
               phase1_static_arguments_reference_spine_arguments :=
                 Some arguments |}
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_static_arguments_reference_spine_round_trip :
  forall reference refined,
    phase1_surface_normalize_static_arguments_reference_spine reference =
      Some refined ->
    phase1_surface_static_arguments_reference_spine_tree refined =
      phase1_surface_static_reference_spine_tree reference.
Proof.
  intros reference refined Hnormalize.
  destruct reference as [name [arguments_tree |]]; cbn in Hnormalize.
  - destruct (phase1_surface_normalize_static_arguments_spine arguments_tree)
      as [arguments |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_normalize_static_arguments_spine_round_trip
      arguments_tree arguments Harguments).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Inductive Phase1SurfaceStaticArgumentsTypeSpine : Type :=
| Phase1StaticArgumentsNonreferenceType
    (value : Phase1SurfaceRefinementTupleNonreferenceTypeSpine)
| Phase1StaticArgumentsNamedType
    (reference : Phase1SurfaceStaticArgumentsReferenceSpine).

Definition phase1_surface_static_arguments_type_spine_tree
  (type_value : Phase1SurfaceStaticArgumentsTypeSpine) : ParseTree :=
  match type_value with
  | Phase1StaticArgumentsNonreferenceType nonreference =>
      PTNonterminal "type_expression"
        (PTAlternative 0
          (phase1_surface_refinement_tuple_nonreference_type_spine_tree
            nonreference))
  | Phase1StaticArgumentsNamedType reference =>
      PTNonterminal "type_expression"
        (PTAlternative 1
          (PTNonterminal "named_type"
            (phase1_surface_static_arguments_reference_spine_tree reference)))
  end.

Definition phase1_surface_normalize_static_arguments_type_spine
  (type_value : Phase1SurfaceStaticReferenceTypeSpine)
  : option Phase1SurfaceStaticArgumentsTypeSpine :=
  match type_value with
  | Phase1StaticReferenceNonreferenceType nonreference =>
      Some (Phase1StaticArgumentsNonreferenceType nonreference)
  | Phase1StaticReferenceNamedType reference =>
      match phase1_surface_normalize_static_arguments_reference_spine reference with
      | Some refined => Some (Phase1StaticArgumentsNamedType refined)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_static_arguments_type_spine_round_trip :
  forall type_value refined,
    phase1_surface_normalize_static_arguments_type_spine type_value =
      Some refined ->
    phase1_surface_static_arguments_type_spine_tree refined =
      phase1_surface_static_reference_type_spine_tree type_value.
Proof.
  intros type_value refined Hnormalize.
  destruct type_value as [nonreference | reference].
  - inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_static_arguments_reference_spine reference)
      as [actual |] eqn:Hreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_static_arguments_reference_spine_round_trip
        reference actual Hreference).
    reflexivity.
Qed.

Definition phase1_surface_normalize_static_arguments_type_tree
  (tree : ParseTree) : option Phase1SurfaceStaticArgumentsTypeSpine :=
  match phase1_surface_normalize_static_reference_type_tree tree with
  | Some type_value =>
      phase1_surface_normalize_static_arguments_type_spine type_value
  | None => None
  end.

Theorem phase1_surface_normalize_static_arguments_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_static_arguments_type_tree tree = Some refined ->
    phase1_surface_static_arguments_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_static_arguments_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_static_reference_type_tree tree)
    as [type_value |] eqn:Htype; try discriminate Hnormalize.
  transitivity (phase1_surface_static_reference_type_spine_tree type_value).
  - eapply phase1_surface_normalize_static_arguments_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_static_reference_type_tree_round_trip.
    exact Htype.
Qed.
