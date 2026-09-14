From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstGenericRequirementsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  First select/offer payload layer for PHIL-SURFACE-GRAMMAR-CORR-001.

  Send/receive continuation chains are now recursively closed.  This slice
  opens the remaining choice alternatives just far enough to normalize their
  nonempty branch-list shell:

      "select"/"offer", "{", session_branch,
      { "|", session_branch }, "}"

  Individual session_branch payloads remain exact certified ParseTree values
  for the next refinement layer.
*)

Inductive Phase1SurfaceSessionChoiceDirection : Type :=
| Phase1SessionSelect
| Phase1SessionOffer.

Definition phase1_surface_session_choice_keyword
  (direction : Phase1SurfaceSessionChoiceDirection) : string :=
  match direction with
  | Phase1SessionSelect => "select"
  | Phase1SessionOffer => "offer"
  end.

Definition phase1_surface_session_choice_index
  (direction : Phase1SurfaceSessionChoiceDirection) : nat :=
  match direction with
  | Phase1SessionSelect => 2
  | Phase1SessionOffer => 3
  end.

Definition phase1_surface_session_branch_suffix_tree
  (branch_tree : ParseTree) : ParseTree :=
  PTSequence
    [ PTLiteral "|";
      branch_tree
    ].

Definition phase1_surface_normalize_session_branch_suffix
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (pipe_tree, branch_tree) =>
          match phase1_surface_expect_literal "|" pipe_tree,
                phase1_surface_validate_named_node "session_branch" branch_tree with
          | Some tt, Some tt => Some branch_tree
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_session_branch_suffix_round_trip :
  forall tree branch_tree,
    phase1_surface_normalize_session_branch_suffix tree = Some branch_tree ->
    phase1_surface_session_branch_suffix_tree branch_tree = tree.
Proof.
  intros tree branch_tree Hnormalize.
  unfold phase1_surface_normalize_session_branch_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[pipe_tree selected_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "|" pipe_tree)
    as [[] |] eqn:Hpipe; try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "session_branch" selected_tree)
    as [[] |] eqn:Hbranch; try discriminate Hnormalize.
  inversion Hnormalize; subst branch_tree.
  unfold phase1_surface_session_branch_suffix_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items pipe_tree selected_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "|" pipe_tree Hpipe).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_session_branch_suffixes
  (trees : list ParseTree) : option (list ParseTree) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_session_branch_suffix tree,
            phase1_surface_normalize_session_branch_suffixes rest with
      | Some branch_tree, Some branches => Some (branch_tree :: branches)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_session_branch_suffixes_round_trip :
  forall trees branches,
    phase1_surface_normalize_session_branch_suffixes trees = Some branches ->
    map phase1_surface_session_branch_suffix_tree branches = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros branches Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst branches.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_session_branch_suffix tree)
      as [branch_tree |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_session_branch_suffixes rest)
      as [rest_branches |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst branches.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_session_branch_suffix_round_trip.
      exact Htree.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceSessionChoiceSpine : Type := {
  phase1_session_choice_direction : Phase1SurfaceSessionChoiceDirection;
  phase1_session_choice_first_branch_tree : ParseTree;
  phase1_session_choice_rest_branch_trees : list ParseTree
}.

Definition phase1_surface_session_choice_spine_tree
  (choice : Phase1SurfaceSessionChoiceSpine) : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_choice_keyword
          (phase1_session_choice_direction choice));
      PTLiteral "{";
      phase1_session_choice_first_branch_tree choice;
      PTRepetition
        (map phase1_surface_session_branch_suffix_tree
          (phase1_session_choice_rest_branch_trees choice));
      PTLiteral "}"
    ].

Definition phase1_surface_normalize_session_choice_spine
  (direction : Phase1SurfaceSessionChoiceDirection)
  (tree : ParseTree) : option Phase1SurfaceSessionChoiceSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact5 items with
      | Some (keyword_tree, open_tree, first_tree, rest_tree, close_tree) =>
          match
            phase1_surface_expect_literal
              (phase1_surface_session_choice_keyword direction) keyword_tree,
            phase1_surface_expect_literal "{" open_tree,
            phase1_surface_validate_named_node "session_branch" first_tree,
            phase1_surface_expect_repetition rest_tree,
            phase1_surface_expect_literal "}" close_tree
          with
          | Some tt, Some tt, Some tt, Some rest_trees, Some tt =>
              match phase1_surface_normalize_session_branch_suffixes rest_trees with
              | Some rest_branches =>
                  Some
                    {| phase1_session_choice_direction := direction;
                       phase1_session_choice_first_branch_tree := first_tree;
                       phase1_session_choice_rest_branch_trees := rest_branches |}
              | None => None
              end
          | _, _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_session_choice_spine_round_trip :
  forall direction tree choice,
    phase1_surface_normalize_session_choice_spine direction tree = Some choice ->
    phase1_surface_session_choice_spine_tree choice = tree.
Proof.
  intros direction tree choice Hnormalize.
  unfold phase1_surface_normalize_session_choice_spine in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact5 items)
    as [[[[[keyword_tree open_tree] first_tree] rest_tree] close_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct
    (phase1_surface_expect_literal
      (phase1_surface_session_choice_keyword direction) keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "{" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "session_branch" first_tree)
    as [[] |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition rest_tree)
    as [rest_trees |] eqn:Hrepetition; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "}" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_session_branch_suffixes rest_trees)
    as [rest_branches |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst choice.
  unfold phase1_surface_session_choice_spine_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact5_round_trip
    items keyword_tree open_tree first_tree rest_tree close_tree Hitems).
  rewrite
    (phase1_surface_expect_literal_round_trip
      (phase1_surface_session_choice_keyword direction) keyword_tree Hkeyword).
  rewrite (phase1_surface_expect_literal_round_trip "{" open_tree Hopen).
  rewrite (phase1_surface_expect_repetition_round_trip
    rest_tree rest_trees Hrepetition).
  rewrite (phase1_surface_normalize_session_branch_suffixes_round_trip
    rest_trees rest_branches Hrest).
  rewrite (phase1_surface_expect_literal_round_trip "}" close_tree Hclose).
  reflexivity.
Qed.
