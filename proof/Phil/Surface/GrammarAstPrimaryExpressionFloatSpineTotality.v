From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionFloatSpine
  GrammarAstPrimaryExpressionStringSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the float-literal refinement introduced by #1444.

  The float spine makes the float_literal branch explicit by exposing its
  DECIMAL_FLOAT lexical payload while preserving all previously refined
  primary_expression carriers. This companion proves that every
  grammar-derived primary_expression tree is accepted by that refinement and
  reconstructed exactly.

  The result remains intentionally structural: integer_literal stays retained
  for a later focused slice. Float contents are not decoded or assigned
  numeric semantics here, and nested ordinary-expression trees remain outside
  this slice.
*)

Lemma
  phase1_surface_float_literal_lookup_for_primary_expression_totality :
  lookupRule "float_literal" phase1_surface_rules =
    Some (ELexicalClass "DECIMAL_FLOAT").
Proof. vm_compute. reflexivity. Qed.

Lemma
  phase1_surface_normalize_primary_expression_float_spine_total_from_branch_derivation :
  forall index item path input rest selected,
    nth_error phase1_surface_primary_expression_items_for_totality index =
      Some item ->
    Derives phase1_surface_rules path item input rest selected ->
    exists grouping literal char string_expression refined,
      phase1_surface_normalize_primary_expression_grouping_spine
        {| phase1_primary_expression_spine_branch := index;
           phase1_primary_expression_spine_selected := selected |} =
        Some grouping /\
      phase1_surface_normalize_primary_expression_literal_spine grouping =
        Some literal /\
      phase1_surface_normalize_primary_expression_char_spine literal =
        Some char /\
      phase1_surface_normalize_primary_expression_string_spine char =
        Some string_expression /\
      phase1_surface_normalize_primary_expression_float_spine string_expression =
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
      (Phase1PrimaryExpressionLiteralTuple tuple_expression),
      (Phase1PrimaryExpressionCharPrior
        (Phase1PrimaryExpressionLiteralTuple tuple_expression)),
      (Phase1PrimaryExpressionStringPrior
        (Phase1PrimaryExpressionCharPrior
          (Phase1PrimaryExpressionLiteralTuple tuple_expression))),
      (Phase1PrimaryExpressionFloatPrior
        (Phase1PrimaryExpressionStringPrior
          (Phase1PrimaryExpressionCharPrior
            (Phase1PrimaryExpressionLiteralTuple tuple_expression)))).
    repeat split.
    + cbn.
      rewrite Htuple.
      reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
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
        (Phase1PrimaryExpressionLiteralParenthesized parenthesized),
        (Phase1PrimaryExpressionCharPrior
          (Phase1PrimaryExpressionLiteralParenthesized parenthesized)),
        (Phase1PrimaryExpressionStringPrior
          (Phase1PrimaryExpressionCharPrior
            (Phase1PrimaryExpressionLiteralParenthesized parenthesized))),
        (Phase1PrimaryExpressionFloatPrior
          (Phase1PrimaryExpressionStringPrior
            (Phase1PrimaryExpressionCharPrior
              (Phase1PrimaryExpressionLiteralParenthesized parenthesized)))).
      repeat split.
      * cbn.
        rewrite Hparenthesized.
        reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
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
          Phase1PrimaryExpressionTrue,
          (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionTrue),
          (Phase1PrimaryExpressionStringPrior
            (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionTrue)),
          (Phase1PrimaryExpressionFloatPrior
            (Phase1PrimaryExpressionStringPrior
              (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionTrue))).
        repeat split.
        -- reflexivity.
        -- cbn.
           rewrite Hselected.
           reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
      * destruct index as [|index].
        -- cbn in Hnth.
           inversion Hnth; subst item.
           destruct
             (literal_derivation_is_exact
               phase1_surface_rules path "false" input rest selected Hderive)
             as [tail [_ [_ Hselected]]].
           exists
             (Phase1PrimaryExpressionOtherRetained 3 selected),
             Phase1PrimaryExpressionFalse,
             (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionFalse),
             (Phase1PrimaryExpressionStringPrior
               (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionFalse)),
             (Phase1PrimaryExpressionFloatPrior
               (Phase1PrimaryExpressionStringPrior
                 (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionFalse))).
           repeat split.
           ++ reflexivity.
           ++ cbn.
              rewrite Hselected.
              reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
        -- destruct index as [|index].
           ++ cbn in Hnth.
              inversion Hnth; subst item.
              destruct
                (literal_derivation_is_exact
                  phase1_surface_rules path "unit" input rest selected Hderive)
                as [tail [_ [_ Hselected]]].
              exists
                (Phase1PrimaryExpressionOtherRetained 4 selected),
                Phase1PrimaryExpressionUnit,
                (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionUnit),
                (Phase1PrimaryExpressionStringPrior
                  (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionUnit)),
                (Phase1PrimaryExpressionFloatPrior
                  (Phase1PrimaryExpressionStringPrior
                    (Phase1PrimaryExpressionCharPrior Phase1PrimaryExpressionUnit))).
              repeat split.
              ** reflexivity.
              ** cbn.
                 rewrite Hselected.
                 reflexivity.
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
           ++ destruct index as [|index].
              ** cbn in Hnth.
                 inversion Hnth; subst item.
                 destruct
                   (derives_nonterminal_exposes_body
                     phase1_surface_rules path "char_literal"
                     input rest selected Hderive)
                   as [body [subtree [Hlookup [Htree Hbody]]]].
                 rewrite
                   phase1_surface_char_literal_lookup_for_primary_expression_totality
                   in Hlookup.
                 inversion Hlookup; subst body.
                 destruct
                   (lexical_derivation_is_exact
                     phase1_surface_rules
                     (descend path (AtNonterminal "char_literal"))
                     "CHAR_LITERAL" input rest subtree Hbody)
                   as [value [tail [_ [_ Hsubtree]]]].
                 exists
                   (Phase1PrimaryExpressionOtherRetained 5 selected),
                   (Phase1PrimaryExpressionLexicalRetained 5 selected),
                   (Phase1PrimaryExpressionCharRefined value),
                   (Phase1PrimaryExpressionStringPrior
                     (Phase1PrimaryExpressionCharRefined value)),
                   (Phase1PrimaryExpressionFloatPrior
                     (Phase1PrimaryExpressionStringPrior
                       (Phase1PrimaryExpressionCharRefined value))).
                 repeat split.
                 --- reflexivity.
                 --- reflexivity.
                 --- cbn.
                     rewrite Htree, Hsubtree.
                     unfold phase1_surface_expect_nonterminal,
                       phase1_surface_expect_lexical.
                     cbn.
                     repeat rewrite String.eqb_refl.
                     reflexivity.
                 --- reflexivity.
                 --- reflexivity.
              ** destruct index as [|index].
                 --- cbn in Hnth.
                     inversion Hnth; subst item.
                     destruct
                       (derives_nonterminal_exposes_body
                         phase1_surface_rules path "runtime_string_literal"
                         input rest selected Hderive)
                       as [body [subtree [Hlookup [Htree Hbody]]]].
                     rewrite
                       phase1_surface_runtime_string_literal_lookup_for_primary_expression_totality
                       in Hlookup.
                     inversion Hlookup; subst body.
                     destruct
                       (lexical_derivation_is_exact
                         phase1_surface_rules
                         (descend path (AtNonterminal "runtime_string_literal"))
                         "STRING_LITERAL" input rest subtree Hbody)
                       as [value [tail [_ [_ Hsubtree]]]].
                     exists
                       (Phase1PrimaryExpressionOtherRetained 6 selected),
                       (Phase1PrimaryExpressionLexicalRetained 6 selected),
                       (Phase1PrimaryExpressionCharPrior
                         (Phase1PrimaryExpressionLexicalRetained 6 selected)),
                       (Phase1PrimaryExpressionStringRefined value),
                       (Phase1PrimaryExpressionFloatPrior
                         (Phase1PrimaryExpressionStringRefined value)).
                     repeat split.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ cbn.
                         rewrite Htree, Hsubtree.
                         unfold phase1_surface_expect_nonterminal,
                           phase1_surface_expect_lexical.
                         cbn.
                         repeat rewrite String.eqb_refl.
                         reflexivity.
                     +++ reflexivity.
                 --- destruct index as [|index].
                     +++ cbn in Hnth.
                         inversion Hnth; subst item.
                         destruct
                           (derives_nonterminal_exposes_body
                             phase1_surface_rules path "float_literal"
                             input rest selected Hderive)
                           as [body [subtree [Hlookup [Htree Hbody]]]].
                         rewrite
                           phase1_surface_float_literal_lookup_for_primary_expression_totality
                           in Hlookup.
                         inversion Hlookup; subst body.
                         destruct
                           (lexical_derivation_is_exact
                             phase1_surface_rules
                             (descend path (AtNonterminal "float_literal"))
                             "DECIMAL_FLOAT" input rest subtree Hbody)
                           as [value [tail [_ [_ Hsubtree]]]].
                         exists
                           (Phase1PrimaryExpressionOtherRetained 7 selected),
                           (Phase1PrimaryExpressionLexicalRetained 7 selected),
                           (Phase1PrimaryExpressionCharPrior
                             (Phase1PrimaryExpressionLexicalRetained 7 selected)),
                           (Phase1PrimaryExpressionStringPrior
                             (Phase1PrimaryExpressionCharPrior
                               (Phase1PrimaryExpressionLexicalRetained 7 selected))),
                           (Phase1PrimaryExpressionFloatRefined value).
                         repeat split.
                         *** reflexivity.
                         *** reflexivity.
                         *** reflexivity.
                         *** reflexivity.
                         *** cbn.
                             rewrite Htree, Hsubtree.
                             unfold phase1_surface_expect_nonterminal,
                               phase1_surface_expect_lexical.
                             cbn.
                             repeat rewrite String.eqb_refl.
                             reflexivity.
                     +++ exists
                           (Phase1PrimaryExpressionOtherRetained
                             (S (S (S (S (S (S (S (S index)))))))) selected),
                           (Phase1PrimaryExpressionLexicalRetained
                             (S (S (S (S (S (S (S (S index)))))))) selected),
                           (Phase1PrimaryExpressionCharPrior
                             (Phase1PrimaryExpressionLexicalRetained
                               (S (S (S (S (S (S (S (S index)))))))) selected)),
                           (Phase1PrimaryExpressionStringPrior
                             (Phase1PrimaryExpressionCharPrior
                               (Phase1PrimaryExpressionLexicalRetained
                                 (S (S (S (S (S (S (S (S index)))))))) selected))),
                           (Phase1PrimaryExpressionFloatPrior
                             (Phase1PrimaryExpressionStringPrior
                               (Phase1PrimaryExpressionCharPrior
                                 (Phase1PrimaryExpressionLexicalRetained
                                   (S (S (S (S (S (S (S (S index)))))))) selected)))).
                         repeat split; reflexivity.
Qed.

Theorem
  phase1_surface_normalize_primary_expression_float_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "primary_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_primary_expression_float_tree tree =
        Some refined /\
      phase1_surface_primary_expression_float_spine_tree refined = tree.
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
    (phase1_surface_normalize_primary_expression_float_spine_total_from_branch_derivation
      index item _ _ _ selected Hnth Hselected)
    as
      [grouping
        [literal
          [char
            [string_expression
              [refined
                [Hgrouping [Hliteral [Hchar [Hstring Hfloat]]]]]]]]].
  assert (Hgrouping_tree :
    phase1_surface_normalize_primary_expression_grouping_tree tree =
      Some grouping).
  {
    unfold phase1_surface_normalize_primary_expression_grouping_tree.
    rewrite Hspine.
    exact Hgrouping.
  }
  assert (Hliteral_tree :
    phase1_surface_normalize_primary_expression_literal_tree tree =
      Some literal).
  {
    unfold phase1_surface_normalize_primary_expression_literal_tree.
    rewrite Hgrouping_tree.
    exact Hliteral.
  }
  assert (Hchar_tree :
    phase1_surface_normalize_primary_expression_char_tree tree =
      Some char).
  {
    unfold phase1_surface_normalize_primary_expression_char_tree.
    rewrite Hliteral_tree.
    exact Hchar.
  }
  assert (Hstring_tree :
    phase1_surface_normalize_primary_expression_string_tree tree =
      Some string_expression).
  {
    unfold phase1_surface_normalize_primary_expression_string_tree.
    rewrite Hchar_tree.
    exact Hstring.
  }
  assert (Hnormalize :
    phase1_surface_normalize_primary_expression_float_tree tree =
      Some refined).
  {
    unfold phase1_surface_normalize_primary_expression_float_tree.
    rewrite Hstring_tree.
    exact Hfloat.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_primary_expression_float_tree_round_trip.
    exact Hnormalize.
Qed.
