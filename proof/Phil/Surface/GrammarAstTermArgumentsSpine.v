From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Reusable term_arguments spine correspondence.

  This slice opens the exact parenthesized/comma-separated argument-list shell.
  Each argument is retained as an exact certified expression ParseTree for the
  dedicated ordinary-expression Rocq refinement that follows.
*)

Definition phase1_surface_expression_node_tree
  (tree : ParseTree) : ParseTree := tree.

Definition phase1_surface_normalize_expression_node
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_validate_named_node "expression" tree with
  | Some tt => Some tree
  | None => None
  end.

Theorem phase1_surface_normalize_expression_node_round_trip :
  forall tree refined,
    phase1_surface_normalize_expression_node tree = Some refined ->
    phase1_surface_expression_node_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_expression_node in Hnormalize.
  destruct
    (phase1_surface_validate_named_node "expression" tree)
    as [[] |] eqn:Hvalidate; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  reflexivity.
Qed.

Definition phase1_surface_term_argument_suffix_tree
  (argument : ParseTree) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_expression_node_tree argument
    ].

Definition phase1_surface_normalize_term_argument_suffix
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (comma_tree, argument_tree) =>
          match phase1_surface_expect_literal "," comma_tree,
                phase1_surface_normalize_expression_node argument_tree with
          | Some tt, Some argument => Some argument
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_term_argument_suffix_round_trip :
  forall tree argument,
    phase1_surface_normalize_term_argument_suffix tree = Some argument ->
    phase1_surface_term_argument_suffix_tree argument = tree.
Proof.
  intros tree argument Hnormalize.
  unfold phase1_surface_normalize_term_argument_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[comma_tree argument_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma_tree)
    as [[] |] eqn:Hcomma; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_expression_node argument_tree)
    as [actual |] eqn:Hargument; try discriminate Hnormalize.
  inversion Hnormalize; subst argument.
  unfold phase1_surface_term_argument_suffix_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items comma_tree argument_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "," comma_tree Hcomma).
  rewrite
    (phase1_surface_normalize_expression_node_round_trip
      argument_tree actual Hargument).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_term_argument_suffixes
  (trees : list ParseTree) : option (list ParseTree) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_term_argument_suffix tree,
            phase1_surface_normalize_term_argument_suffixes rest with
      | Some argument, Some arguments => Some (argument :: arguments)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_term_argument_suffixes_round_trip :
  forall trees arguments,
    phase1_surface_normalize_term_argument_suffixes trees = Some arguments ->
    map phase1_surface_term_argument_suffix_tree arguments = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros arguments Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst arguments.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_term_argument_suffix tree)
      as [argument |] eqn:Hargument; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_term_argument_suffixes rest)
      as [arguments_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst arguments.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_term_argument_suffix_round_trip.
      exact Hargument.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_term_argument_entries_tree
  (arguments : list ParseTree) : ParseTree :=
  match arguments with
  | [] => PTOptionalNone
  | first :: rest =>
      PTOptionalSome
        (PTSequence
          [ phase1_surface_expression_node_tree first;
            PTRepetition
              (map phase1_surface_term_argument_suffix_tree rest)
          ])
  end.

Definition phase1_surface_normalize_term_argument_entries
  (tree : ParseTree) : option (list ParseTree) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some []
  | Some (Some body) =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (first_tree, rest_tree) =>
              match phase1_surface_normalize_expression_node first_tree,
                    phase1_surface_expect_repetition rest_tree with
              | Some first, Some rest_trees =>
                  match phase1_surface_normalize_term_argument_suffixes rest_trees
                  with
                  | Some rest => Some (first :: rest)
                  | None => None
                  end
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_term_argument_entries_round_trip :
  forall tree arguments,
    phase1_surface_normalize_term_argument_entries tree = Some arguments ->
    phase1_surface_term_argument_entries_tree arguments = tree.
Proof.
  intros tree arguments Hnormalize.
  unfold phase1_surface_normalize_term_argument_entries in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_expect_sequence body)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact2 items)
      as [[first_tree rest_tree] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct (phase1_surface_normalize_expression_node first_tree)
      as [first |] eqn:Hfirst; try discriminate Hnormalize.
    destruct (phase1_surface_expect_repetition rest_tree)
      as [rest_trees |] eqn:Hrepetition; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_term_argument_suffixes rest_trees)
      as [rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst arguments.
    unfold phase1_surface_term_argument_entries_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_expect_sequence_round_trip
      body items Hsequence).
    rewrite (phase1_surface_exact2_round_trip
      items first_tree rest_tree Hitems).
    rewrite
      (phase1_surface_normalize_expression_node_round_trip
        first_tree first Hfirst).
    rewrite (phase1_surface_expect_repetition_round_trip
      rest_tree rest_trees Hrepetition).
    rewrite <-
      (phase1_surface_normalize_term_argument_suffixes_round_trip
        rest_trees rest Hrest).
    reflexivity.
  - inversion Hnormalize; subst arguments.
    unfold phase1_surface_term_argument_entries_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceTermArgumentsSpine : Type := {
  phase1_term_arguments_spine_arguments : list ParseTree
}.

Definition phase1_surface_term_arguments_spine_tree
  (arguments : Phase1SurfaceTermArgumentsSpine) : ParseTree :=
  PTNonterminal "term_arguments"
    (PTSequence
      [ PTLiteral "(";
        phase1_surface_term_argument_entries_tree
          (phase1_term_arguments_spine_arguments arguments);
        PTLiteral ")"
      ]).

Definition phase1_surface_normalize_term_arguments_spine
  (tree : ParseTree) : option Phase1SurfaceTermArgumentsSpine :=
  match phase1_surface_expect_nonterminal "term_arguments" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact3 items with
          | Some (open_tree, entries_tree, close_tree) =>
              match phase1_surface_expect_literal "(" open_tree,
                    phase1_surface_normalize_term_argument_entries entries_tree,
                    phase1_surface_expect_literal ")" close_tree with
              | Some tt, Some arguments, Some tt =>
                  Some {| phase1_term_arguments_spine_arguments := arguments |}
              | _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_term_arguments_spine_round_trip :
  forall tree arguments,
    phase1_surface_normalize_term_arguments_spine tree = Some arguments ->
    phase1_surface_term_arguments_spine_tree arguments = tree.
Proof.
  intros tree arguments Hnormalize.
  unfold phase1_surface_normalize_term_arguments_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "term_arguments" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[open_tree entries_tree] close_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "(" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_term_argument_entries entries_tree)
    as [actual |] eqn:Hentries; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ")" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  inversion Hnormalize; subst arguments.
  unfold phase1_surface_term_arguments_spine_tree.
  cbn.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "term_arguments" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip
    body items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items open_tree entries_tree close_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "(" open_tree Hopen).
  rewrite
    (phase1_surface_normalize_term_argument_entries_round_trip
      entries_tree actual Hentries).
  rewrite (phase1_surface_expect_literal_round_trip
    ")" close_tree Hclose).
  reflexivity.
Qed.
