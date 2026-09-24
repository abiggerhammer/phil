From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstMultiplicativeExpressionSpine
  GrammarAstGenericRequirementsTotality
  GrammarAstSourceHeaderTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the multiplicative-expression shell refinement introduced by #1367.

  The carrier exposes the exact * / / / % operator choice and repeated suffix
  structure while retaining each unary_expression operand as an exact
  certified ParseTree.  This file proves that normalization is total for every
  derivable multiplicative_expression tree.
*)

Definition phase1_surface_multiplicative_operator_items_for_totality
  : list EbnfExpression :=
  [ ELiteral "*";
    ELiteral "/";
    ELiteral "%"
  ].

Definition phase1_surface_multiplicative_suffix_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ EAlternative phase1_surface_multiplicative_operator_items_for_totality;
      ENonterminal "unary_expression"
    ].

Lemma phase1_surface_multiplicative_expression_lookup_for_totality :
  lookupRule "multiplicative_expression" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "unary_expression";
          ERepetition phase1_surface_multiplicative_suffix_expression_for_totality
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_unary_expression_node_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "unary_expression")
      input rest tree ->
    phase1_surface_normalize_unary_expression_node tree = Some tree.
Proof.
  intros path input rest tree Hderive.
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "unary_expression" path input rest tree Hderive) as Hvalidate.
  unfold phase1_surface_normalize_unary_expression_node.
  rewrite Hvalidate.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_multiplicative_operator_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EAlternative phase1_surface_multiplicative_operator_items_for_totality)
      input rest tree ->
    exists operator,
      phase1_surface_normalize_multiplicative_operator_spine tree = Some operator /\
      phase1_surface_multiplicative_operator_spine_tree operator = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules path
      phase1_surface_multiplicative_operator_items_for_totality
      input rest tree Hderive)
    as [index [item [selected [Hnth [Htree Hselected]]]]].
  destruct index as [|index]; cbn in Hnth.
  - inversion Hnth; subst item.
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "*" _ _ selected Hselected)
      as [tail [_ [_ Hselected_tree]]].
    assert (Hnormalize :
      phase1_surface_normalize_multiplicative_operator_spine tree =
        Some Phase1SurfaceMultiplicativeOperatorMultiply).
    {
      rewrite Htree, Hselected_tree.
      reflexivity.
    }
    exists Phase1SurfaceMultiplicativeOperatorMultiply.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_multiplicative_operator_spine_round_trip.
      exact Hnormalize.
  - destruct index as [|index]; cbn in Hnth.
    + inversion Hnth; subst item.
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "/" _ _ selected Hselected)
        as [tail [_ [_ Hselected_tree]]].
      assert (Hnormalize :
        phase1_surface_normalize_multiplicative_operator_spine tree =
          Some Phase1SurfaceMultiplicativeOperatorDivide).
      {
        rewrite Htree, Hselected_tree.
        reflexivity.
      }
      exists Phase1SurfaceMultiplicativeOperatorDivide.
      split.
      * exact Hnormalize.
      * eapply phase1_surface_normalize_multiplicative_operator_spine_round_trip.
        exact Hnormalize.
    + destruct index as [|index]; cbn in Hnth.
      * inversion Hnth; subst item.
        destruct
          (literal_derivation_is_exact
            phase1_surface_rules _ "%" _ _ selected Hselected)
          as [tail [_ [_ Hselected_tree]]].
        assert (Hnormalize :
          phase1_surface_normalize_multiplicative_operator_spine tree =
            Some Phase1SurfaceMultiplicativeOperatorRemainder).
        {
          rewrite Htree, Hselected_tree.
          reflexivity.
        }
        exists Phase1SurfaceMultiplicativeOperatorRemainder.
        split.
        -- exact Hnormalize.
        -- eapply phase1_surface_normalize_multiplicative_operator_spine_round_trip.
           exact Hnormalize.
      * destruct index; cbn in Hnth; discriminate Hnth.
Qed.

Lemma phase1_surface_normalize_multiplicative_suffix_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_multiplicative_suffix_expression_for_totality
      input rest tree ->
    exists suffix,
      phase1_surface_normalize_multiplicative_suffix_spine tree = Some suffix /\
      phase1_surface_multiplicative_suffix_spine_tree suffix = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_multiplicative_suffix_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ EAlternative phase1_surface_multiplicative_operator_items_for_totality;
        ENonterminal "unary_expression"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (EAlternative phase1_surface_multiplicative_operator_items_for_totality)
      [ ENonterminal "unary_expression" ]
      input rest trees Hitems)
    as [after_operator [operator_tree [tail_trees
      [Htrees [Hoperator Htail]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "unary_expression") []
      after_operator rest tail_trees Htail)
    as [after_right [right_tree [nil_trees
      [Htail_trees [Hright Hnil]]]]].
  rewrite Htrees, Htail_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (phase1_surface_normalize_multiplicative_operator_spine_total_from_derivation
      _ _ _ operator_tree Hoperator)
    as [operator [Hoperator_normalize Hoperator_round_trip]].
  pose proof
    (phase1_surface_normalize_unary_expression_node_total_from_derivation
      _ _ _ right_tree Hright) as Hright_normalize.
  pose (suffix :=
    {| phase1_multiplicative_suffix_spine_operator := operator;
       phase1_multiplicative_suffix_spine_right := right_tree |}).
  assert (Hnormalize :
    phase1_surface_normalize_multiplicative_suffix_spine tree = Some suffix).
  {
    rewrite Htree.
    unfold phase1_surface_normalize_multiplicative_suffix_spine,
      phase1_surface_expect_sequence,
      phase1_surface_exact2.
    cbn.
    rewrite Hoperator_normalize, Hright_normalize.
    reflexivity.
  }
  exists suffix.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_multiplicative_suffix_spine_round_trip.
    exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_multiplicative_suffix_spines_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_multiplicative_suffix_expression_for_totality ->
    exists suffixes,
      phase1_surface_normalize_multiplicative_suffix_spines trees = Some suffixes.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [].
    reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_multiplicative_suffix_spine_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hitem)
      as [suffix [Hsuffix Hsuffix_round_trip]].
    destruct (IHrest eq_refl)
      as [suffixes Hsuffixes].
    exists (suffix :: suffixes).
    cbn.
    rewrite Hsuffix, Hsuffixes.
    reflexivity.
Qed.

Theorem phase1_surface_normalize_multiplicative_expression_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "multiplicative_expression")
      input rest tree ->
    exists expression,
      phase1_surface_normalize_multiplicative_expression_spine tree = Some expression /\
      phase1_surface_multiplicative_expression_spine_tree expression = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "multiplicative_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_multiplicative_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "multiplicative_expression"))
      [ ENonterminal "unary_expression";
        ERepetition phase1_surface_multiplicative_suffix_expression_for_totality
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "multiplicative_expression")) 0
      (ENonterminal "unary_expression")
      [ ERepetition phase1_surface_multiplicative_suffix_expression_for_totality ]
      input rest trees Hitems)
    as [after_first [first_tree [tail_trees
      [Htrees [Hfirst Htail]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "multiplicative_expression")) 1
      (ERepetition phase1_surface_multiplicative_suffix_expression_for_totality) []
      after_first rest tail_trees Htail)
    as [after_rest [rest_tree [nil_trees
      [Htail_trees [Hrest Hnil]]]]].
  rewrite Htrees, Htail_trees in Hsubtree.
  inversion Hnil; subst nil_trees.
  pose proof
    (phase1_surface_normalize_unary_expression_node_total_from_derivation
      _ _ _ first_tree Hfirst) as Hfirst_normalize.
  destruct
    (phase1_surface_repetition_derivation_exposes
      _ phase1_surface_multiplicative_suffix_expression_for_totality
      _ _ rest_tree Hrest)
    as [rest_trees [Hrest_tree Hrest_body]].
  destruct
    (phase1_surface_normalize_multiplicative_suffix_spines_total_from_repetition
      _ phase1_surface_multiplicative_suffix_expression_for_totality
      _ _ rest_trees Hrest_body eq_refl)
    as [rest_suffixes Hrest_normalize].
  pose (expression :=
    {| phase1_multiplicative_expression_spine_first := first_tree;
       phase1_multiplicative_expression_spine_rest := rest_suffixes |}).
  assert (Hnormalize :
    phase1_surface_normalize_multiplicative_expression_spine tree = Some expression).
  {
    rewrite Htree, Hsubtree, Hrest_tree.
    unfold phase1_surface_normalize_multiplicative_expression_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact2,
      phase1_surface_expect_repetition.
    cbn.
    rewrite Hfirst_normalize, Hrest_normalize.
    reflexivity.
  }
  exists expression.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_multiplicative_expression_spine_round_trip.
    exact Hnormalize.
Qed.
