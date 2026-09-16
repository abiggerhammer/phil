From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionChoiceBranchCarrierSpine
  GrammarAstSessionBranchTotality
  GrammarAstSessionChoiceTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the structured select/offer branch carrier introduced by #1041. *)

Lemma
  phase1_surface_normalize_structured_session_branch_suffixes_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_session_branch_suffix_expression_for_totality ->
    exists raw_branches structured_branches,
      phase1_surface_normalize_session_branch_suffixes trees =
        Some raw_branches /\
      phase1_surface_normalize_session_branch_spines raw_branches =
        Some structured_branches.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [], [].
    split; reflexivity.
  - subst body.
    unfold phase1_surface_session_branch_suffix_expression_for_totality
      in Hbody.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend path AtRepetitionBody)
        [ ELiteral "|";
          ENonterminal "session_branch"
        ]
        input middle tree Hbody)
      as [suffix_trees [Htree Hitems]].
    repeat match goal with
    | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
        inversion Hseq; subst; clear Hseq
    end.
    match goal with
    | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
        inversion Hnil; subst; clear Hnil
    end.
    match goal with
    | Hpipe : Derives phase1_surface_rules _
        (ELiteral "|") _ _ ?pipe_tree,
      Hbranch : Derives phase1_surface_rules _
        (ENonterminal "session_branch") _ _ ?branch_tree |- _ =>
        destruct
          (literal_derivation_is_exact
            phase1_surface_rules _ "|" _ _ pipe_tree Hpipe)
          as [pipe_tail [_ [_ Hpipe_tree]]];
        pose proof
          (phase1_surface_validate_named_node_total_from_derivation
            "session_branch" _ _ _ branch_tree Hbranch)
          as Hbranch_validate;
        destruct
          (phase1_surface_normalize_session_branch_spine_total_from_derivation
            _ _ _ branch_tree Hbranch)
          as [branch [Hbranch_normalize Hbranch_round_trip]];
        assert (Hsuffix :
          phase1_surface_normalize_session_branch_suffix tree =
            Some branch_tree);
        [ rewrite Htree, Hpipe_tree;
          unfold phase1_surface_normalize_session_branch_suffix,
            phase1_surface_expect_sequence,
            phase1_surface_exact2,
            phase1_surface_expect_literal;
          cbn;
          rewrite Hbranch_validate;
          reflexivity
        | destruct (IHrest eq_refl)
            as [raw_branches [structured_branches
              [Hraw_branches Hstructured_branches]]];
          exists (branch_tree :: raw_branches),
            (branch :: structured_branches);
          split;
          [ cbn;
            rewrite Hsuffix;
            rewrite Hraw_branches;
            reflexivity
          | cbn;
            rewrite Hbranch_normalize;
            rewrite Hstructured_branches;
            reflexivity ] ]
    end.
Qed.

Theorem
  phase1_surface_normalize_structured_session_choice_tree_total_from_derivation :
  forall direction path input rest tree,
    Derives phase1_surface_rules path
      (phase1_surface_session_choice_expression_for_totality direction)
      input rest tree ->
    exists choice,
      phase1_surface_normalize_structured_session_choice_tree direction tree =
        Some choice /\
      phase1_surface_structured_session_choice_spine_tree choice = tree.
Proof.
  intros direction path input rest tree Hderive.
  unfold phase1_surface_session_choice_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral (phase1_surface_session_choice_keyword direction);
        ELiteral "{";
        ENonterminal "session_branch";
        ERepetition phase1_surface_session_branch_suffix_expression_for_totality;
        ELiteral "}"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral (phase1_surface_session_choice_keyword direction))
      _ _ ?keyword_tree,
    Hopen : Derives phase1_surface_rules _
      (ELiteral "{") _ _ ?open_tree,
    Hfirst : Derives phase1_surface_rules _
      (ENonterminal "session_branch") _ _ ?first_tree,
    Hrest : Derives phase1_surface_rules _
      (ERepetition phase1_surface_session_branch_suffix_expression_for_totality)
      _ _ ?rest_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral "}") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _
          (phase1_surface_session_choice_keyword direction)
          _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "{" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "session_branch" _ _ _ first_tree Hfirst) as Hfirst_validate;
      destruct
        (phase1_surface_normalize_session_branch_spine_total_from_derivation
          _ _ _ first_tree Hfirst)
        as [first_branch [Hfirst_normalize Hfirst_round_trip]];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ phase1_surface_session_branch_suffix_expression_for_totality
          _ _ rest_tree Hrest)
        as [rest_trees [Hrest_tree Hrest_derive]];
      destruct
        (phase1_surface_normalize_structured_session_branch_suffixes_total_from_repetition
          _ _ _ _ _ Hrest_derive eq_refl)
        as [raw_rest [structured_rest [Hraw_rest Hstructured_rest]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "}" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      let raw_choice := constr:(
        {| phase1_session_choice_direction := direction;
           phase1_session_choice_first_branch_tree := first_tree;
           phase1_session_choice_rest_branch_trees := raw_rest |}) in
      assert (Hraw_choice :
        phase1_surface_normalize_session_choice_spine direction tree =
          Some raw_choice);
      [ rewrite Htree, Hkeyword_tree, Hopen_tree, Hrest_tree, Hclose_tree;
        unfold phase1_surface_normalize_session_choice_spine,
          phase1_surface_expect_sequence,
          phase1_surface_exact5,
          phase1_surface_expect_literal,
          phase1_surface_expect_repetition;
        cbn;
        rewrite Hfirst_validate;
        rewrite Hraw_rest;
        reflexivity
      | let choice := constr:(
          {| phase1_structured_session_choice_direction := direction;
             phase1_structured_session_choice_first_branch := first_branch;
             phase1_structured_session_choice_rest_branches := structured_rest |}) in
        assert (Hstructured_choice :
          phase1_surface_normalize_structured_session_choice_spine raw_choice =
            Some choice);
        [ unfold phase1_surface_normalize_structured_session_choice_spine;
          cbn;
          rewrite Hfirst_normalize;
          rewrite Hstructured_rest;
          reflexivity
        | assert (Hnormalize :
            phase1_surface_normalize_structured_session_choice_tree direction tree =
              Some choice);
          [ unfold phase1_surface_normalize_structured_session_choice_tree;
            rewrite Hraw_choice;
            rewrite Hstructured_choice;
            reflexivity
          | exists choice;
            split;
            [ exact Hnormalize
            | eapply
                phase1_surface_normalize_structured_session_choice_tree_round_trip;
              exact Hnormalize ] ] ] ]
  end.
Qed.
