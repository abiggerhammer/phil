From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimaryExpressionSpine
  GrammarAstSourceHeaderTotality.

Import ListNotations.
Open Scope string_scope.

Definition phase1_surface_primary_expression_items_for_totality
  : list EbnfExpression :=
  [ ENonterminal "tuple_expression";
    ENonterminal "parenthesized_expression";
    ELiteral "true";
    ELiteral "false";
    ELiteral "unit";
    ENonterminal "char_literal";
    ENonterminal "runtime_string_literal";
    ENonterminal "float_literal";
    ENonterminal "integer_literal"
  ].

Lemma phase1_surface_primary_expression_lookup_for_totality :
  lookupRule "primary_expression" phase1_surface_rules =
    Some (EAlternative phase1_surface_primary_expression_items_for_totality).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_primary_expression_branch_valid_total_from_derivation :
  forall index item path input rest selected,
    nth_error phase1_surface_primary_expression_items_for_totality index =
      Some item ->
    Derives phase1_surface_rules path item input rest selected ->
    phase1_surface_primary_expression_branch_valid index selected = Some tt.
Proof.
  intros index item path input rest selected Hnth Hderive.
  destruct index as [|index].
  - cbn in Hnth. inversion Hnth; subst item.
    exact (phase1_surface_validate_named_node_total_from_derivation
      "tuple_expression" path input rest selected Hderive).
  - destruct index as [|index].
    + cbn in Hnth. inversion Hnth; subst item.
      exact (phase1_surface_validate_named_node_total_from_derivation
        "parenthesized_expression" path input rest selected Hderive).
    + destruct index as [|index].
      * cbn in Hnth. inversion Hnth; subst item.
        destruct (literal_derivation_is_exact
          phase1_surface_rules path "true" input rest selected Hderive)
          as [tail [_ [_ Htree]]].
        rewrite Htree. cbn. rewrite String.eqb_refl. reflexivity.
      * destruct index as [|index].
        -- cbn in Hnth. inversion Hnth; subst item.
           destruct (literal_derivation_is_exact
             phase1_surface_rules path "false" input rest selected Hderive)
             as [tail [_ [_ Htree]]].
           rewrite Htree. cbn. rewrite String.eqb_refl. reflexivity.
        -- destruct index as [|index].
           ++ cbn in Hnth. inversion Hnth; subst item.
              destruct (literal_derivation_is_exact
                phase1_surface_rules path "unit" input rest selected Hderive)
                as [tail [_ [_ Htree]]].
              rewrite Htree. cbn. rewrite String.eqb_refl. reflexivity.
           ++ destruct index as [|index].
              ** cbn in Hnth. inversion Hnth; subst item.
                 exact (phase1_surface_validate_named_node_total_from_derivation
                   "char_literal" path input rest selected Hderive).
              ** destruct index as [|index].
                 --- cbn in Hnth. inversion Hnth; subst item.
                     exact (phase1_surface_validate_named_node_total_from_derivation
                       "runtime_string_literal" path input rest selected Hderive).
                 --- destruct index as [|index].
                     +++ cbn in Hnth. inversion Hnth; subst item.
                         exact (phase1_surface_validate_named_node_total_from_derivation
                           "float_literal" path input rest selected Hderive).
                     +++ destruct index as [|index].
                         *** cbn in Hnth. inversion Hnth; subst item.
                             exact (phase1_surface_validate_named_node_total_from_derivation
                               "integer_literal" path input rest selected Hderive).
                         *** cbn in Hnth. discriminate Hnth.
Qed.

Theorem phase1_surface_normalize_primary_expression_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "primary_expression")
      input rest tree ->
    exists expression,
      phase1_surface_normalize_primary_expression_spine tree = Some expression /\
      phase1_surface_primary_expression_spine_tree expression = tree.
Proof.
  intros path input rest tree Hderive.
  destruct (derives_nonterminal_exposes_body
    phase1_surface_rules path "primary_expression" input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_primary_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct (alternative_derivation_names_exact_branch
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
  assert (Hnormalize :
    phase1_surface_normalize_primary_expression_spine tree = Some expression).
  {
    rewrite Htree, Hsubtree.
    unfold phase1_surface_normalize_primary_expression_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_alternative.
    cbn. rewrite Hvalid. reflexivity.
  }
  exists expression. split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_primary_expression_spine_round_trip.
    exact Hnormalize.
Qed.
