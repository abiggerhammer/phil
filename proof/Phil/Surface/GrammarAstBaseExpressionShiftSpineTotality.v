From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstBaseExpressionShiftSpine
  GrammarAstBaseExpressionChoiceTotality
  GrammarAstShiftExpressionSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the base-expression shift refinement introduced by #1351.

  The command_expression branch remains an exact certified ParseTree.  The
  shift_expression branch advances to Phase1SurfaceShiftExpressionSpine, and
  this file proves that normalization is total for every derivable
  base_expression tree.
*)

Theorem phase1_surface_normalize_base_expression_shift_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "base_expression")
      input rest tree ->
    exists expression,
      phase1_surface_normalize_base_expression_shift_tree tree =
        Some expression /\
      phase1_surface_base_expression_shift_spine_tree expression = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "base_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_base_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "base_expression"))
      phase1_surface_base_expression_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    pose proof
      (phase1_surface_validate_named_node_total_from_derivation
        "command_expression" _ _ _ selected Hselected)
      as Hvalidate.
    assert (Hchoice :
      phase1_surface_normalize_base_expression_choice_spine tree =
        Some (Phase1BaseExpressionCommand selected)).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_base_expression_choice_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite Hvalidate.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_base_expression_shift_tree tree =
        Some (Phase1BaseExpressionShiftSpineCommand selected)).
    {
      unfold phase1_surface_normalize_base_expression_shift_tree.
      rewrite Hchoice.
      reflexivity.
    }
    exists (Phase1BaseExpressionShiftSpineCommand selected).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_base_expression_shift_tree_round_trip.
      exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "shift_expression" _ _ _ selected Hselected)
        as Hvalidate.
      destruct
        (phase1_surface_normalize_shift_expression_spine_total_from_derivation
          _ _ _ selected Hselected)
        as [shift [Hshift Hshift_round_trip]].
      assert (Hchoice :
        phase1_surface_normalize_base_expression_choice_spine tree =
          Some (Phase1BaseExpressionShift selected)).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_base_expression_choice_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn.
        rewrite Hvalidate.
        reflexivity.
      }
      assert (Hnormalize :
        phase1_surface_normalize_base_expression_shift_tree tree =
          Some (Phase1BaseExpressionShiftSpineShift shift)).
      {
        unfold phase1_surface_normalize_base_expression_shift_tree.
        rewrite Hchoice.
        cbn.
        rewrite Hshift.
        reflexivity.
      }
      exists (Phase1BaseExpressionShiftSpineShift shift).
      split.
      * exact Hnormalize.
      * eapply phase1_surface_normalize_base_expression_shift_tree_round_trip.
        exact Hnormalize.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
