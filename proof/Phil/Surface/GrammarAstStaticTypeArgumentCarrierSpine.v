From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstStaticTypeArgumentPayloadSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the refined type-valued static_argument payload through the existing
  comma-list / static_arguments / static_reference / type_expression carriers.
  Session, static-value, and effect-set arguments remain exact opaque trees.
*)

Definition phase1_surface_static_type_argument_suffix_tree
  (argument : Phase1SurfaceStaticTypeArgumentSpine) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_static_type_argument_spine_tree argument
    ].

Fixpoint phase1_surface_normalize_static_type_argument_values
  (arguments : list Phase1SurfaceStaticArgumentSpine)
  : option (list Phase1SurfaceStaticTypeArgumentSpine) :=
  match arguments with
  | [] => Some []
  | argument :: rest =>
      match phase1_surface_normalize_static_type_argument_spine argument,
            phase1_surface_normalize_static_type_argument_values rest with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_static_type_argument_values_round_trip :
  forall arguments refined,
    phase1_surface_normalize_static_type_argument_values arguments = Some refined ->
    map phase1_surface_static_type_argument_spine_tree refined =
      map phase1_surface_static_argument_spine_tree arguments.
Proof.
  intros arguments.
  induction arguments as [|argument rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_static_type_argument_spine argument)
      as [actual |] eqn:Hargument; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_static_type_argument_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_static_type_argument_spine_round_trip.
      exact Hargument.
    + eapply IH.
      exact Hrest.
Qed.

Theorem
  phase1_surface_normalize_static_type_argument_suffix_values_round_trip :
  forall arguments refined,
    phase1_surface_normalize_static_type_argument_values arguments = Some refined ->
    map phase1_surface_static_type_argument_suffix_tree refined =
      map phase1_surface_static_argument_suffix_tree arguments.
Proof.
  intros arguments.
  induction arguments as [|argument rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_static_type_argument_spine argument)
      as [actual |] eqn:Hargument; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_static_type_argument_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + unfold phase1_surface_static_type_argument_suffix_tree,
        phase1_surface_static_argument_suffix_tree.
      rewrite
        (phase1_surface_normalize_static_type_argument_spine_round_trip
          argument actual Hargument).
      reflexivity.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceStaticTypeArgumentListSpine : Type := {
  phase1_static_type_argument_list_spine_first :
    Phase1SurfaceStaticTypeArgumentSpine;
  phase1_static_type_argument_list_spine_rest :
    list Phase1SurfaceStaticTypeArgumentSpine
}.

Definition phase1_surface_static_type_argument_list_spine_tree
  (arguments : Phase1SurfaceStaticTypeArgumentListSpine) : ParseTree :=
  PTSequence
    [ phase1_surface_static_type_argument_spine_tree
        (phase1_static_type_argument_list_spine_first arguments);
      PTRepetition
        (map phase1_surface_static_type_argument_suffix_tree
          (phase1_static_type_argument_list_spine_rest arguments))
    ].

Definition phase1_surface_normalize_static_type_argument_list_spine
  (arguments : Phase1SurfaceStaticArgumentListSpine)
  : option Phase1SurfaceStaticTypeArgumentListSpine :=
  match
    phase1_surface_normalize_static_type_argument_spine
      (phase1_static_argument_list_spine_first arguments),
    phase1_surface_normalize_static_type_argument_values
      (phase1_static_argument_list_spine_rest arguments)
  with
  | Some first, Some rest =>
      Some
        {| phase1_static_type_argument_list_spine_first := first;
           phase1_static_type_argument_list_spine_rest := rest |}
  | _, _ => None
  end.

Theorem phase1_surface_normalize_static_type_argument_list_spine_round_trip :
  forall arguments refined,
    phase1_surface_normalize_static_type_argument_list_spine arguments =
      Some refined ->
    phase1_surface_static_type_argument_list_spine_tree refined =
      phase1_surface_static_argument_list_spine_tree arguments.
Proof.
  intros [first rest] refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_static_type_argument_spine first)
    as [actual_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_static_type_argument_values rest)
    as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_static_type_argument_spine_round_trip
      first actual_first Hfirst).
  rewrite
    (phase1_surface_normalize_static_type_argument_suffix_values_round_trip
      rest actual_rest Hrest).
  reflexivity.
Qed.

Definition phase1_surface_optional_static_type_argument_list_tree
  (arguments : option Phase1SurfaceStaticTypeArgumentListSpine) : ParseTree :=
  match arguments with
  | None => PTOptionalNone
  | Some argument_list =>
      PTOptionalSome
        (phase1_surface_static_type_argument_list_spine_tree argument_list)
  end.

Definition phase1_surface_normalize_optional_static_type_argument_list
  (arguments : option Phase1SurfaceStaticArgumentListSpine)
  : option (option Phase1SurfaceStaticTypeArgumentListSpine) :=
  match arguments with
  | None => Some None
  | Some argument_list =>
      match
        phase1_surface_normalize_static_type_argument_list_spine argument_list
      with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_static_type_argument_list_round_trip :
  forall arguments refined,
    phase1_surface_normalize_optional_static_type_argument_list arguments =
      Some refined ->
    phase1_surface_optional_static_type_argument_list_tree refined =
      phase1_surface_optional_static_argument_list_tree arguments.
Proof.
  intros [arguments |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_static_type_argument_list_spine arguments)
      as [actual |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_static_type_argument_list_spine_round_trip
        arguments actual Harguments).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Record Phase1SurfaceStaticTypeArgumentsSpine : Type := {
  phase1_static_type_arguments_spine_items :
    option Phase1SurfaceStaticTypeArgumentListSpine
}.

Definition phase1_surface_static_type_arguments_spine_tree
  (arguments : Phase1SurfaceStaticTypeArgumentsSpine) : ParseTree :=
  PTNonterminal "static_arguments"
    (PTSequence
      [ PTLiteral "[";
        phase1_surface_optional_static_type_argument_list_tree
          (phase1_static_type_arguments_spine_items arguments);
        PTLiteral "]"
      ]).

Definition phase1_surface_normalize_static_type_arguments_spine
  (arguments : Phase1SurfaceStaticArgumentsSpine)
  : option Phase1SurfaceStaticTypeArgumentsSpine :=
  match
    phase1_surface_normalize_optional_static_type_argument_list
      (phase1_static_arguments_spine_items arguments)
  with
  | Some refined =>
      Some {| phase1_static_type_arguments_spine_items := refined |}
  | None => None
  end.

Theorem phase1_surface_normalize_static_type_arguments_spine_round_trip :
  forall arguments refined,
    phase1_surface_normalize_static_type_arguments_spine arguments = Some refined ->
    phase1_surface_static_type_arguments_spine_tree refined =
      phase1_surface_static_arguments_spine_tree arguments.
Proof.
  intros [items] refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_optional_static_type_argument_list items)
    as [actual |] eqn:Hitems; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_static_type_argument_list_round_trip
      items actual Hitems).
  reflexivity.
Qed.

Record Phase1SurfaceStaticTypeArgumentsReferenceSpine : Type := {
  phase1_static_type_arguments_reference_spine_name : Phase1SurfaceNameList;
  phase1_static_type_arguments_reference_spine_arguments :
    option Phase1SurfaceStaticTypeArgumentsSpine
}.

Definition phase1_surface_static_type_arguments_reference_spine_tree
  (reference : Phase1SurfaceStaticTypeArgumentsReferenceSpine) : ParseTree :=
  PTNonterminal "static_reference"
    (PTSequence
      [ phase1_surface_qualified_name_tree
          (phase1_static_type_arguments_reference_spine_name reference);
        match phase1_static_type_arguments_reference_spine_arguments reference with
        | None => PTOptionalNone
        | Some arguments =>
            PTOptionalSome
              (phase1_surface_static_type_arguments_spine_tree arguments)
        end
      ]).

Definition phase1_surface_normalize_static_type_arguments_reference_spine
  (reference : Phase1SurfaceStaticArgumentsReferenceSpine)
  : option Phase1SurfaceStaticTypeArgumentsReferenceSpine :=
  match phase1_static_arguments_reference_spine_arguments reference with
  | None =>
      Some
        {| phase1_static_type_arguments_reference_spine_name :=
             phase1_static_arguments_reference_spine_name reference;
           phase1_static_type_arguments_reference_spine_arguments := None |}
  | Some arguments =>
      match phase1_surface_normalize_static_type_arguments_spine arguments with
      | Some refined =>
          Some
            {| phase1_static_type_arguments_reference_spine_name :=
                 phase1_static_arguments_reference_spine_name reference;
               phase1_static_type_arguments_reference_spine_arguments :=
                 Some refined |}
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_static_type_arguments_reference_spine_round_trip :
  forall reference refined,
    phase1_surface_normalize_static_type_arguments_reference_spine reference =
      Some refined ->
    phase1_surface_static_type_arguments_reference_spine_tree refined =
      phase1_surface_static_arguments_reference_spine_tree reference.
Proof.
  intros [name [arguments |]] refined Hnormalize.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_static_type_arguments_spine arguments)
      as [actual |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_static_type_arguments_spine_round_trip
        arguments actual Harguments).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Inductive Phase1SurfaceStaticTypeArgumentsTypeSpine : Type :=
| Phase1StaticTypeArgumentsNonreferenceType
    (value : Phase1SurfaceRefinementTupleNonreferenceTypeSpine)
| Phase1StaticTypeArgumentsNamedType
    (reference : Phase1SurfaceStaticTypeArgumentsReferenceSpine).

Definition phase1_surface_static_type_arguments_type_spine_tree
  (type_value : Phase1SurfaceStaticTypeArgumentsTypeSpine) : ParseTree :=
  match type_value with
  | Phase1StaticTypeArgumentsNonreferenceType nonreference =>
      PTNonterminal "type_expression"
        (PTAlternative 0
          (phase1_surface_refinement_tuple_nonreference_type_spine_tree
            nonreference))
  | Phase1StaticTypeArgumentsNamedType reference =>
      PTNonterminal "type_expression"
        (PTAlternative 1
          (PTNonterminal "named_type"
            (phase1_surface_static_type_arguments_reference_spine_tree reference)))
  end.

Definition phase1_surface_normalize_static_type_arguments_type_spine
  (type_value : Phase1SurfaceStaticArgumentsTypeSpine)
  : option Phase1SurfaceStaticTypeArgumentsTypeSpine :=
  match type_value with
  | Phase1StaticArgumentsNonreferenceType nonreference =>
      Some (Phase1StaticTypeArgumentsNonreferenceType nonreference)
  | Phase1StaticArgumentsNamedType reference =>
      match
        phase1_surface_normalize_static_type_arguments_reference_spine reference
      with
      | Some refined => Some (Phase1StaticTypeArgumentsNamedType refined)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_static_type_arguments_type_spine_round_trip :
  forall type_value refined,
    phase1_surface_normalize_static_type_arguments_type_spine type_value =
      Some refined ->
    phase1_surface_static_type_arguments_type_spine_tree refined =
      phase1_surface_static_arguments_type_spine_tree type_value.
Proof.
  intros [nonreference | reference] refined Hnormalize.
  - inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_static_type_arguments_reference_spine reference)
      as [actual |] eqn:Hreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_static_type_arguments_reference_spine_round_trip
        reference actual Hreference).
    reflexivity.
Qed.

Definition phase1_surface_normalize_static_type_arguments_type_tree
  (tree : ParseTree) : option Phase1SurfaceStaticTypeArgumentsTypeSpine :=
  match phase1_surface_normalize_static_arguments_type_tree tree with
  | Some type_value =>
      phase1_surface_normalize_static_type_arguments_type_spine type_value
  | None => None
  end.

Theorem phase1_surface_normalize_static_type_arguments_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_static_type_arguments_type_tree tree = Some refined ->
    phase1_surface_static_type_arguments_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_static_type_arguments_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_static_arguments_type_tree tree)
    as [type_value |] eqn:Htype; try discriminate Hnormalize.
  transitivity (phase1_surface_static_arguments_type_spine_tree type_value).
  - eapply phase1_surface_normalize_static_type_arguments_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_static_arguments_type_tree_round_trip.
    exact Htype.
Qed.
