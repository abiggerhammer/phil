From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstBaseExpressionShiftRefinedSpine
  GrammarAstBaseExpressionChoiceTotality
  GrammarAstBaseExpressionShiftSpineTotality
  GrammarAstShiftExpressionRefinedSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the completed shift refinement lifted through base_expression.

  The command_expression branch remains an exact certified ParseTree. On the
  shift_expression branch, reuse the completed refined shift totality witness
  and the existing unrefined shift-spine witness so that the fuel-bounded
  base-expression refinement succeeds and reconstructs the exact certified
  base_expression tree.

  Structural surface-grammar correspondence only. This does not add evaluation
  semantics, change Grammar-v1, alter Haskell, refine the enclosing expression
  shell, or make broader production-parser soundness/completeness claims. It
  continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Theorem
  phase1_surface_normalize_base_expression_shift_refined_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "base_expression")
      input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_base_expression_shift_refined_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_base_expression_shift_refined_spine_tree refined = tree.
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
    assert (Hbase :
      phase1_surface_normalize_base_expression_shift_tree tree =
        Some (Phase1BaseExpressionShiftSpineCommand selected)).
    {
      unfold phase1_surface_normalize_base_expression_shift_tree.
      rewrite Hchoice.
      reflexivity.
    }
    assert (Hnormalize :
      phase1_surface_normalize_base_expression_shift_refined_tree_fuel
        0 tree =
        Some (Phase1BaseExpressionShiftRefinedCommand selected)).
    {
      unfold phase1_surface_normalize_base_expression_shift_refined_tree_fuel.
      rewrite Hbase.
      reflexivity.
    }
    exists 0, (Phase1BaseExpressionShiftRefinedCommand selected).
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_base_expression_shift_refined_tree_fuel_round_trip.
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
      destruct
        (phase1_surface_normalize_shift_expression_refined_tree_fuel_total_from_derivation
          _ _ _ selected Hselected)
        as [fuel [refined_shift
          [Hrefined_shift Hrefined_shift_round_trip]]].
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
      assert (Hbase :
        phase1_surface_normalize_base_expression_shift_tree tree =
          Some (Phase1BaseExpressionShiftSpineShift shift)).
      {
        unfold phase1_surface_normalize_base_expression_shift_tree.
        rewrite Hchoice.
        cbn.
        rewrite Hshift.
        reflexivity.
      }
      assert (Hnormalize :
        phase1_surface_normalize_base_expression_shift_refined_tree_fuel
          fuel tree =
          Some (Phase1BaseExpressionShiftRefinedShift refined_shift)).
      {
        unfold
          phase1_surface_normalize_base_expression_shift_refined_tree_fuel.
        rewrite Hbase.
        unfold
          phase1_surface_normalize_base_expression_shift_refined_spine_fuel.
        cbn.
        rewrite Hshift_round_trip.
        rewrite Hrefined_shift.
        reflexivity.
      }
      exists fuel, (Phase1BaseExpressionShiftRefinedShift refined_shift).
      split.
      * exact Hnormalize.
      * eapply
          phase1_surface_normalize_base_expression_shift_refined_tree_fuel_round_trip.
        exact Hnormalize.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
