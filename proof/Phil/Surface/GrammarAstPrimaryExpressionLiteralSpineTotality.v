From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionLiteralSpine
  GrammarAstPrimaryExpressionGroupingSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the closed keyword-literal refinement introduced by #1438.

  The literal-spine normalizer makes the "true", "false", and "unit"
  primary_expression alternatives explicit while preserving the already-refined
  tuple and parenthesized grouping carriers. This companion proves that every
  grammar-derived primary_expression tree is accepted by that refinement and
  reconstructed exactly.

  The result remains intentionally structural: char_literal,
  runtime_string_literal, float_literal, and integer_literal are retained as
  exact certified ParseTree values for later focused lexical slices. This does
  not claim recursive ordinary-expression normalization or semantic
  interpretation of lexical payloads.
*)

Lemma
  phase1_surface_normalize_primary_expression_literal_spine_total_from_branch_derivation :
  forall index item path input rest selected,
    nth_error phase1_surface_primary_expression_items_for_totality index =
      Some item ->
    Derives phase1_surface_rules path item input rest selected ->
    exists grouping refined,
      phase1_surface_normalize_primary_expression_grouping_spine
        {| phase1_primary_expression_spine_branch := index;
           phase1_primary_expression_spine_selected := selected |} =
        Some grouping /\
      phase1_surface_normalize_primary_expression_literal_spine grouping =
        Some refined.
Proof.
  intros index item path input rest selected Hnth Hderive.
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_tuple_expression_spine_total_from_derivation
        path input rest selected Hderive)
      as [tuple_expression [Htuple _]].
    exists
      (Phase1PrimaryExpressionTupleRefined tuple_expression),
      (Phase1PrimaryExpressionLiteralTuple tuple_expression).
    split.
    + cbn.
      rewrite Htuple.
      reflexivity.
    + reflexivity.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_parenthesized_expression_spine_total_from_derivation
          path input rest selected Hderive)
        as [parenthesized [Hparenthesized _]].
      exists
        (Phase1PrimaryExpressionParenthesizedRefined parenthesized),
        (Phase1PrimaryExpressionLiteralParenthesized parenthesized).
      split.
      * cbn.
        rewrite Hparenthesized.
        reflexivity.
      * reflexivity.
    + destruct index as [|index].
      * cbn in Hnth.
        inversion Hnth; subst item.
        destruct
          (literal_derivation_is_exact
            phase1_surface_rules path "true" input rest selected Hderive)
          as [tail [_ [_ Hselected]]].
        exists
          (Phase1PrimaryExpressionOtherRetained 2 selected),
          Phase1PrimaryExpressionTrue.
        split.
        -- reflexivity.
        -- cbn.
           rewrite Hselected.
           reflexivity.
      * destruct index as [|index].
        -- cbn in Hnth.
           inversion Hnth; subst item.
           destruct
             (literal_derivation_is_exact
               phase1_surface_rules path "false" input rest selected Hderive)
             as [tail [_ [_ Hselected]]].
           exists
             (Phase1PrimaryExpressionOtherRetained 3 selected),
             Phase1PrimaryExpressionFalse.
           split.
           ++ reflexivity.
           ++ cbn.
              rewrite Hselected.
              reflexivity.
        -- destruct index as [|index].
           ++ cbn in Hnth.
              inversion Hnth; subst item.
              destruct
                (literal_derivation_is_exact
                  phase1_surface_rules path "unit" input rest selected Hderive)
                as [tail [_ [_ Hselected]]].
              exists
                (Phase1PrimaryExpressionOtherRetained 4 selected),
                Phase1PrimaryExpressionUnit.
              split.
              ** reflexivity.
              ** cbn.
                 rewrite Hselected.
                 reflexivity.
           ++ exists
                (Phase1PrimaryExpressionOtherRetained
                  (S (S (S (S (S index))))) selected),
                (Phase1PrimaryExpressionLexicalRetained
                  (S (S (S (S (S index))))) selected).
              split; reflexivity.
Qed.

Theorem
  phase1_surface_normalize_primary_expression_literal_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "primary_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_primary_expression_literal_tree tree =
        Some refined /\
      phase1_surface_primary_expression_literal_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "primary_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_primary_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "primary_expression"))
      phase1_surface_primary_expression_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  pose proof
    (phase1_surface_primary_expression_branch_valid_total_from_derivation
      index item _ _ _ selected Hnth Hselected) as Hvalid.
  let expression := constr:(
    {| phase1_primary_expression_spine_branch := index;
       phase1_primary_expression_spine_selected := selected |}) in
  assert (Hspine :
    phase1_surface_normalize_primary_expression_spine tree =
      Some expression).
  {
    rewrite Htree, Hsubtree.
    unfold phase1_surface_normalize_primary_expression_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_alternative.
    cbn.
    rewrite Hvalid.
    reflexivity.
  }
  destruct
    (phase1_surface_normalize_primary_expression_literal_spine_total_from_branch_derivation
      index item _ _ _ selected Hnth Hselected)
    as [grouping [refined [Hgrouping Hliteral]]].
  assert (Hgrouping_tree :
    phase1_surface_normalize_primary_expression_grouping_tree tree =
      Some grouping).
  {
    unfold phase1_surface_normalize_primary_expression_grouping_tree.
    rewrite Hspine.
    exact Hgrouping.
  }
  assert (Hnormalize :
    phase1_surface_normalize_primary_expression_literal_tree tree =
      Some refined).
  {
    unfold phase1_surface_normalize_primary_expression_literal_tree.
    rewrite Hgrouping_tree.
    exact Hliteral.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_primary_expression_literal_tree_round_trip.
    exact Hnormalize.
Qed.
