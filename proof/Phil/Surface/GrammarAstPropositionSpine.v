From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionSpine
  GrammarAstGenericRequirementsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Shared proposition precedence-spine correspondence for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  This layer opens the complete proposition/or/and/not/atom shell and preserves
  exact recursive payloads at the remaining expression-bearing boundaries:
  relation operands, parenthesized propositions, claim applications, and the
  recursive child of `not`.
*)

Inductive Phase1SurfacePropositionAtomSpine : Type :=
| Phase1RelationPropositionAtom (relation_tree : ParseTree)
| Phase1ParenthesizedPropositionAtom (proposition_tree : ParseTree)
| Phase1TruePropositionAtom
| Phase1FalsePropositionAtom
| Phase1ClaimPropositionAtom (claim_tree : ParseTree).

Definition phase1_surface_proposition_atom_spine_tree
  (atom : Phase1SurfacePropositionAtomSpine) : ParseTree :=
  match atom with
  | Phase1RelationPropositionAtom relation_tree =>
      PTNonterminal "proposition_atom"
        (PTAlternative 0 relation_tree)
  | Phase1ParenthesizedPropositionAtom proposition_tree =>
      PTNonterminal "proposition_atom"
        (PTAlternative 1
          (PTSequence
            [ PTLiteral "(";
              proposition_tree;
              PTLiteral ")"
            ]))
  | Phase1TruePropositionAtom =>
      PTNonterminal "proposition_atom"
        (PTAlternative 2 (PTLiteral "true"))
  | Phase1FalsePropositionAtom =>
      PTNonterminal "proposition_atom"
        (PTAlternative 3 (PTLiteral "false"))
  | Phase1ClaimPropositionAtom claim_tree =>
      PTNonterminal "proposition_atom"
        (PTAlternative 4 claim_tree)
  end.

Definition phase1_surface_normalize_proposition_atom_spine
  (tree : ParseTree) : option Phase1SurfacePropositionAtomSpine :=
  match phase1_surface_expect_nonterminal "proposition_atom" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          match phase1_surface_validate_named_node
                  "relation_proposition" selected with
          | Some tt => Some (Phase1RelationPropositionAtom selected)
          | None => None
          end
      | Some (1, selected) =>
          match phase1_surface_expect_sequence selected with
          | Some items =>
              match phase1_surface_exact3 items with
              | Some (open_tree, proposition_tree, close_tree) =>
                  match phase1_surface_expect_literal "(" open_tree,
                        phase1_surface_validate_named_node
                          "proposition" proposition_tree,
                        phase1_surface_expect_literal ")" close_tree with
                  | Some tt, Some tt, Some tt =>
                      Some
                        (Phase1ParenthesizedPropositionAtom proposition_tree)
                  | _, _, _ => None
                  end
              | None => None
              end
          | None => None
          end
      | Some (2, selected) =>
          match phase1_surface_expect_literal "true" selected with
          | Some tt => Some Phase1TruePropositionAtom
          | None => None
          end
      | Some (3, selected) =>
          match phase1_surface_expect_literal "false" selected with
          | Some tt => Some Phase1FalsePropositionAtom
          | None => None
          end
      | Some (4, selected) =>
          match phase1_surface_validate_named_node "claim_application" selected with
          | Some tt => Some (Phase1ClaimPropositionAtom selected)
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_proposition_atom_spine_round_trip :
  forall tree atom,
    phase1_surface_normalize_proposition_atom_spine tree = Some atom ->
    phase1_surface_proposition_atom_spine_tree atom = tree.
Proof.
  intros tree atom Hnormalize.
  unfold phase1_surface_normalize_proposition_atom_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "proposition_atom" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct
      (phase1_surface_validate_named_node "relation_proposition" selected)
      as [[] |] eqn:Hrelation; try discriminate Hnormalize.
    inversion Hnormalize; subst atom.
    unfold phase1_surface_proposition_atom_spine_tree.
    rewrite (phase1_surface_expect_nonterminal_round_trip
      "proposition_atom" tree body Hnode).
    rewrite (phase1_surface_expect_alternative_round_trip
      body 0 selected Halternative).
    reflexivity.
  - destruct index as [|index].
    + destruct (phase1_surface_expect_sequence selected)
        as [items |] eqn:Hsequence; try discriminate Hnormalize.
      destruct (phase1_surface_exact3 items)
        as [[[open_tree proposition_tree] close_tree] |] eqn:Hitems;
        try discriminate Hnormalize.
      destruct (phase1_surface_expect_literal "(" open_tree)
        as [[] |] eqn:Hopen; try discriminate Hnormalize.
      destruct
        (phase1_surface_validate_named_node "proposition" proposition_tree)
        as [[] |] eqn:Hproposition; try discriminate Hnormalize.
      destruct (phase1_surface_expect_literal ")" close_tree)
        as [[] |] eqn:Hclose; try discriminate Hnormalize.
      inversion Hnormalize; subst atom.
      unfold phase1_surface_proposition_atom_spine_tree.
      rewrite (phase1_surface_expect_nonterminal_round_trip
        "proposition_atom" tree body Hnode).
      rewrite (phase1_surface_expect_alternative_round_trip
        body 1 selected Halternative).
      rewrite (phase1_surface_expect_sequence_round_trip
        selected items Hsequence).
      rewrite (phase1_surface_exact3_round_trip
        items open_tree proposition_tree close_tree Hitems).
      rewrite (phase1_surface_expect_literal_round_trip "(" open_tree Hopen).
      rewrite (phase1_surface_expect_literal_round_trip ")" close_tree Hclose).
      reflexivity.
    + destruct index as [|index].
      * destruct (phase1_surface_expect_literal "true" selected)
          as [[] |] eqn:Htrue; try discriminate Hnormalize.
        inversion Hnormalize; subst atom.
        unfold phase1_surface_proposition_atom_spine_tree.
        rewrite (phase1_surface_expect_nonterminal_round_trip
          "proposition_atom" tree body Hnode).
        rewrite (phase1_surface_expect_alternative_round_trip
          body 2 selected Halternative).
        rewrite (phase1_surface_expect_literal_round_trip "true" selected Htrue).
        reflexivity.
      * destruct index as [|index].
        -- destruct (phase1_surface_expect_literal "false" selected)
             as [[] |] eqn:Hfalse; try discriminate Hnormalize.
           inversion Hnormalize; subst atom.
           unfold phase1_surface_proposition_atom_spine_tree.
           rewrite (phase1_surface_expect_nonterminal_round_trip
             "proposition_atom" tree body Hnode).
           rewrite (phase1_surface_expect_alternative_round_trip
             body 3 selected Halternative).
           rewrite
             (phase1_surface_expect_literal_round_trip "false" selected Hfalse).
           reflexivity.
        -- destruct index as [|index].
           ++ destruct
                (phase1_surface_validate_named_node
                  "claim_application" selected)
                as [[] |] eqn:Hclaim; try discriminate Hnormalize.
              inversion Hnormalize; subst atom.
              unfold phase1_surface_proposition_atom_spine_tree.
              rewrite (phase1_surface_expect_nonterminal_round_trip
                "proposition_atom" tree body Hnode).
              rewrite (phase1_surface_expect_alternative_round_trip
                body 4 selected Halternative).
              reflexivity.
           ++ discriminate Hnormalize.
Qed.

Inductive Phase1SurfacePropositionNotSpine : Type :=
| Phase1NotPropositionSpine (child_tree : ParseTree)
| Phase1AtomPropositionSpine (atom : Phase1SurfacePropositionAtomSpine).

Definition phase1_surface_proposition_not_spine_tree
  (proposition : Phase1SurfacePropositionNotSpine) : ParseTree :=
  match proposition with
  | Phase1NotPropositionSpine child_tree =>
      PTNonterminal "proposition_not"
        (PTAlternative 0
          (PTSequence
            [ PTLiteral "not";
              child_tree
            ]))
  | Phase1AtomPropositionSpine atom =>
      PTNonterminal "proposition_not"
        (PTAlternative 1
          (phase1_surface_proposition_atom_spine_tree atom))
  end.

Definition phase1_surface_normalize_proposition_not_spine
  (tree : ParseTree) : option Phase1SurfacePropositionNotSpine :=
  match phase1_surface_expect_nonterminal "proposition_not" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          match phase1_surface_expect_sequence selected with
          | Some items =>
              match phase1_surface_exact2 items with
              | Some (not_tree, child_tree) =>
                  match phase1_surface_expect_literal "not" not_tree,
                        phase1_surface_validate_named_node
                          "proposition_not" child_tree with
                  | Some tt, Some tt =>
                      Some (Phase1NotPropositionSpine child_tree)
                  | _, _ => None
                  end
              | None => None
              end
          | None => None
          end
      | Some (1, selected) =>
          match phase1_surface_normalize_proposition_atom_spine selected with
          | Some atom => Some (Phase1AtomPropositionSpine atom)
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_proposition_not_spine_round_trip :
  forall tree proposition,
    phase1_surface_normalize_proposition_not_spine tree = Some proposition ->
    phase1_surface_proposition_not_spine_tree proposition = tree.
Proof.
  intros tree proposition Hnormalize.
  unfold phase1_surface_normalize_proposition_not_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "proposition_not" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct (phase1_surface_expect_sequence selected)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact2 items)
      as [[not_tree child_tree] |] eqn:Hitems; try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal "not" not_tree)
      as [[] |] eqn:Hnot; try discriminate Hnormalize.
    destruct
      (phase1_surface_validate_named_node "proposition_not" child_tree)
      as [[] |] eqn:Hchild; try discriminate Hnormalize.
    inversion Hnormalize; subst proposition.
    unfold phase1_surface_proposition_not_spine_tree.
    rewrite (phase1_surface_expect_nonterminal_round_trip
      "proposition_not" tree body Hnode).
    rewrite (phase1_surface_expect_alternative_round_trip
      body 0 selected Halternative).
    rewrite (phase1_surface_expect_sequence_round_trip selected items Hsequence).
    rewrite (phase1_surface_exact2_round_trip items not_tree child_tree Hitems).
    rewrite (phase1_surface_expect_literal_round_trip "not" not_tree Hnot).
    reflexivity.
  - destruct index as [|index].
    + destruct (phase1_surface_normalize_proposition_atom_spine selected)
        as [atom |] eqn:Hatom; try discriminate Hnormalize.
      inversion Hnormalize; subst proposition.
      unfold phase1_surface_proposition_not_spine_tree.
      rewrite (phase1_surface_expect_nonterminal_round_trip
        "proposition_not" tree body Hnode).
      rewrite (phase1_surface_expect_alternative_round_trip
        body 1 selected Halternative).
      rewrite (phase1_surface_normalize_proposition_atom_spine_round_trip
        selected atom Hatom).
      reflexivity.
    + discriminate Hnormalize.
Qed.

Definition phase1_surface_proposition_and_suffix_tree
  (proposition : Phase1SurfacePropositionNotSpine) : ParseTree :=
  PTSequence
    [ PTLiteral "and";
      phase1_surface_proposition_not_spine_tree proposition
    ].

Definition phase1_surface_normalize_proposition_and_suffix
  (tree : ParseTree) : option Phase1SurfacePropositionNotSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (and_tree, proposition_tree) =>
          match phase1_surface_expect_literal "and" and_tree,
                phase1_surface_normalize_proposition_not_spine proposition_tree with
          | Some tt, Some proposition => Some proposition
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_proposition_and_suffix_round_trip :
  forall tree proposition,
    phase1_surface_normalize_proposition_and_suffix tree = Some proposition ->
    phase1_surface_proposition_and_suffix_tree proposition = tree.
Proof.
  intros tree proposition Hnormalize.
  unfold phase1_surface_normalize_proposition_and_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[and_tree proposition_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "and" and_tree)
    as [[] |] eqn:Hand; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_proposition_not_spine proposition_tree)
    as [actual |] eqn:Hproposition; try discriminate Hnormalize.
  inversion Hnormalize; subst proposition.
  unfold phase1_surface_proposition_and_suffix_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip items and_tree proposition_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "and" and_tree Hand).
  rewrite (phase1_surface_normalize_proposition_not_spine_round_trip
    proposition_tree actual Hproposition).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_proposition_and_suffixes
  (trees : list ParseTree) : option (list Phase1SurfacePropositionNotSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_proposition_and_suffix tree,
            phase1_surface_normalize_proposition_and_suffixes rest with
      | Some proposition, Some propositions =>
          Some (proposition :: propositions)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_proposition_and_suffixes_round_trip :
  forall trees propositions,
    phase1_surface_normalize_proposition_and_suffixes trees = Some propositions ->
    map phase1_surface_proposition_and_suffix_tree propositions = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros propositions Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst propositions.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_proposition_and_suffix tree)
      as [proposition |] eqn:Hproposition; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_proposition_and_suffixes rest)
      as [propositions_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst propositions.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_proposition_and_suffix_round_trip.
      exact Hproposition.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfacePropositionAndSpine : Type := {
  phase1_proposition_and_spine_first : Phase1SurfacePropositionNotSpine;
  phase1_proposition_and_spine_rest : list Phase1SurfacePropositionNotSpine
}.

Definition phase1_surface_proposition_and_spine_tree
  (proposition : Phase1SurfacePropositionAndSpine) : ParseTree :=
  PTNonterminal "proposition_and"
    (PTSequence
      [ phase1_surface_proposition_not_spine_tree
          (phase1_proposition_and_spine_first proposition);
        PTRepetition
          (map phase1_surface_proposition_and_suffix_tree
            (phase1_proposition_and_spine_rest proposition))
      ]).

Definition phase1_surface_normalize_proposition_and_spine
  (tree : ParseTree) : option Phase1SurfacePropositionAndSpine :=
  match phase1_surface_expect_nonterminal "proposition_and" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (first_tree, rest_tree) =>
              match phase1_surface_expect_repetition rest_tree with
              | Some rest_trees =>
                  match phase1_surface_normalize_proposition_not_spine first_tree,
                        phase1_surface_normalize_proposition_and_suffixes rest_trees with
                  | Some first, Some rest =>
                      Some
                        {| phase1_proposition_and_spine_first := first;
                           phase1_proposition_and_spine_rest := rest |}
                  | _, _ => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_proposition_and_spine_round_trip :
  forall tree proposition,
    phase1_surface_normalize_proposition_and_spine tree = Some proposition ->
    phase1_surface_proposition_and_spine_tree proposition = tree.
Proof.
  intros tree proposition Hnormalize.
  unfold phase1_surface_normalize_proposition_and_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "proposition_and" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[first_tree rest_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition rest_tree)
    as [rest_trees |] eqn:Hrepetition; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_proposition_not_spine first_tree)
    as [first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_proposition_and_suffixes rest_trees)
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst proposition.
  unfold phase1_surface_proposition_and_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "proposition_and" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact2_round_trip items first_tree rest_tree Hitems).
  rewrite (phase1_surface_normalize_proposition_not_spine_round_trip
    first_tree first Hfirst).
  rewrite (phase1_surface_expect_repetition_round_trip
    rest_tree rest_trees Hrepetition).
  rewrite (phase1_surface_normalize_proposition_and_suffixes_round_trip
    rest_trees rest Hrest).
  reflexivity.
Qed.

Definition phase1_surface_proposition_or_suffix_tree
  (proposition : Phase1SurfacePropositionAndSpine) : ParseTree :=
  PTSequence
    [ PTLiteral "or";
      phase1_surface_proposition_and_spine_tree proposition
    ].

Definition phase1_surface_normalize_proposition_or_suffix
  (tree : ParseTree) : option Phase1SurfacePropositionAndSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (or_tree, proposition_tree) =>
          match phase1_surface_expect_literal "or" or_tree,
                phase1_surface_normalize_proposition_and_spine proposition_tree with
          | Some tt, Some proposition => Some proposition
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_proposition_or_suffix_round_trip :
  forall tree proposition,
    phase1_surface_normalize_proposition_or_suffix tree = Some proposition ->
    phase1_surface_proposition_or_suffix_tree proposition = tree.
Proof.
  intros tree proposition Hnormalize.
  unfold phase1_surface_normalize_proposition_or_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[or_tree proposition_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "or" or_tree)
    as [[] |] eqn:Hor; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_proposition_and_spine proposition_tree)
    as [actual |] eqn:Hproposition; try discriminate Hnormalize.
  inversion Hnormalize; subst proposition.
  unfold phase1_surface_proposition_or_suffix_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip items or_tree proposition_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "or" or_tree Hor).
  rewrite (phase1_surface_normalize_proposition_and_spine_round_trip
    proposition_tree actual Hproposition).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_proposition_or_suffixes
  (trees : list ParseTree) : option (list Phase1SurfacePropositionAndSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_proposition_or_suffix tree,
            phase1_surface_normalize_proposition_or_suffixes rest with
      | Some proposition, Some propositions =>
          Some (proposition :: propositions)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_proposition_or_suffixes_round_trip :
  forall trees propositions,
    phase1_surface_normalize_proposition_or_suffixes trees = Some propositions ->
    map phase1_surface_proposition_or_suffix_tree propositions = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros propositions Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst propositions.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_proposition_or_suffix tree)
      as [proposition |] eqn:Hproposition; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_proposition_or_suffixes rest)
      as [propositions_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst propositions.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_proposition_or_suffix_round_trip.
      exact Hproposition.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfacePropositionOrSpine : Type := {
  phase1_proposition_or_spine_first : Phase1SurfacePropositionAndSpine;
  phase1_proposition_or_spine_rest : list Phase1SurfacePropositionAndSpine
}.

Definition phase1_surface_proposition_or_spine_tree
  (proposition : Phase1SurfacePropositionOrSpine) : ParseTree :=
  PTNonterminal "proposition_or"
    (PTSequence
      [ phase1_surface_proposition_and_spine_tree
          (phase1_proposition_or_spine_first proposition);
        PTRepetition
          (map phase1_surface_proposition_or_suffix_tree
            (phase1_proposition_or_spine_rest proposition))
      ]).

Definition phase1_surface_normalize_proposition_or_spine
  (tree : ParseTree) : option Phase1SurfacePropositionOrSpine :=
  match phase1_surface_expect_nonterminal "proposition_or" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (first_tree, rest_tree) =>
              match phase1_surface_expect_repetition rest_tree with
              | Some rest_trees =>
                  match phase1_surface_normalize_proposition_and_spine first_tree,
                        phase1_surface_normalize_proposition_or_suffixes rest_trees with
                  | Some first, Some rest =>
                      Some
                        {| phase1_proposition_or_spine_first := first;
                           phase1_proposition_or_spine_rest := rest |}
                  | _, _ => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_proposition_or_spine_round_trip :
  forall tree proposition,
    phase1_surface_normalize_proposition_or_spine tree = Some proposition ->
    phase1_surface_proposition_or_spine_tree proposition = tree.
Proof.
  intros tree proposition Hnormalize.
  unfold phase1_surface_normalize_proposition_or_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "proposition_or" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[first_tree rest_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition rest_tree)
    as [rest_trees |] eqn:Hrepetition; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_proposition_and_spine first_tree)
    as [first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_proposition_or_suffixes rest_trees)
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst proposition.
  unfold phase1_surface_proposition_or_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "proposition_or" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact2_round_trip items first_tree rest_tree Hitems).
  rewrite (phase1_surface_normalize_proposition_and_spine_round_trip
    first_tree first Hfirst).
  rewrite (phase1_surface_expect_repetition_round_trip
    rest_tree rest_trees Hrepetition).
  rewrite (phase1_surface_normalize_proposition_or_suffixes_round_trip
    rest_trees rest Hrest).
  reflexivity.
Qed.

Record Phase1SurfacePropositionSpine : Type := {
  phase1_proposition_spine_or : Phase1SurfacePropositionOrSpine
}.

Definition phase1_surface_proposition_spine_tree
  (proposition : Phase1SurfacePropositionSpine) : ParseTree :=
  PTNonterminal "proposition"
    (phase1_surface_proposition_or_spine_tree
      (phase1_proposition_spine_or proposition)).

Definition phase1_surface_normalize_proposition_spine
  (tree : ParseTree) : option Phase1SurfacePropositionSpine :=
  match phase1_surface_expect_nonterminal "proposition" tree with
  | Some body =>
      match phase1_surface_normalize_proposition_or_spine body with
      | Some proposition_or =>
          Some {| phase1_proposition_spine_or := proposition_or |}
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_proposition_spine_round_trip :
  forall tree proposition,
    phase1_surface_normalize_proposition_spine tree = Some proposition ->
    phase1_surface_proposition_spine_tree proposition = tree.
Proof.
  intros tree proposition Hnormalize.
  unfold phase1_surface_normalize_proposition_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "proposition" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_proposition_or_spine body)
    as [proposition_or |] eqn:Hor; try discriminate Hnormalize.
  inversion Hnormalize; subst proposition.
  unfold phase1_surface_proposition_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "proposition" tree body Hnode).
  rewrite (phase1_surface_normalize_proposition_or_spine_round_trip
    body proposition_or Hor).
  reflexivity.
Qed.
