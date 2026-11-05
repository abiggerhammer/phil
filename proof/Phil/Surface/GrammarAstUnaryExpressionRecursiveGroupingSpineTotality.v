From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String Lia.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstRecordTotality
  GrammarAstUnaryExpressionSpine
  GrammarAstUnaryExpressionSpineTotality
  GrammarAstUnaryExpressionRecursiveRefinedSpine
  GrammarAstPostfixExpressionRefinedSpine
  GrammarAstPostfixExpressionRecursiveGroupingSpine
  GrammarAstPostfixExpressionRecursiveGroupingSpineTotality
  GrammarAstRecursiveGroupingTotality
  GrammarAstUnaryExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001.
   Grammar derivations supply the child derivation at each unary constructor.
   The legacy adapter is structurally recursive. The raw decoder is total
   with the input tree's computable node count as fuel; no caller-supplied
   normalization-success or fuel premise is exposed by the public entry. *)

Lemma phase1_surface_unary_recursive_grouping_negate_derivation :
  forall path input rest operand,
    Derives phase1_surface_rules path (ENonterminal "unary_expression")
      input rest
      (phase1_surface_unary_expression_spine_tree
        (Phase1SurfaceUnaryExpressionNegate operand)) ->
    exists operand_path operand_input,
      Derives phase1_surface_rules operand_path
        (ENonterminal "unary_expression") operand_input rest operand.
Proof.
  intros path input rest operand Hderive.
  destruct (derives_nonterminal_exposes_body phase1_surface_rules path
    "unary_expression" input rest _ Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_unary_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  cbn in Htree. inversion Htree; subst subtree.
  destruct (alternative_derivation_names_exact_branch phase1_surface_rules _
    phase1_surface_unary_expression_items_for_totality input rest _ Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  inversion Hsubtree; subst index selected.
  cbn in Hnth. inversion Hnth; subst item.
  destruct (derives_sequence_expression_exposes_items phase1_surface_rules _
    [ELiteral "-"; ENonterminal "unary_expression"] input rest _ Hselected)
    as [trees [Hselected_tree Hitems]].
  inversion Hselected_tree; subst trees.
  destruct (derives_sequence_cons_exposes_head_exact phase1_surface_rules _ 0
    (ELiteral "-") [ENonterminal "unary_expression"] input rest _ Hitems)
    as [after_minus [minus_tree [tail_trees [Htrees [Hminus Htail]]]]].
  inversion Htrees; subst minus_tree tail_trees.
  destruct (derives_sequence_cons_exposes_head_exact phase1_surface_rules _ 1
    (ENonterminal "unary_expression") [] after_minus rest _ Htail)
    as [after_operand [operand_tree [nil_trees
      [Htail_trees [Hoperand Hnil]]]]].
  inversion Htail_trees; subst operand_tree nil_trees.
  inversion Hnil; subst.
  do 2 eexists. exact Hoperand.
Qed.

Lemma phase1_surface_unary_recursive_grouping_postfix_derivation :
  forall path input rest postfix,
    Derives phase1_surface_rules path (ENonterminal "unary_expression")
      input rest
      (phase1_surface_unary_expression_spine_tree
        (Phase1SurfaceUnaryExpressionPostfix postfix)) ->
    exists postfix_path,
      Derives phase1_surface_rules postfix_path
        (ENonterminal "postfix_expression") input rest postfix.
Proof.
  intros path input rest postfix Hderive.
  destruct (derives_nonterminal_exposes_body phase1_surface_rules path
    "unary_expression" input rest _ Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_unary_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  cbn in Htree. inversion Htree; subst subtree.
  destruct (alternative_derivation_names_exact_branch phase1_surface_rules _
    phase1_surface_unary_expression_items_for_totality input rest _ Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  inversion Hsubtree; subst index selected.
  cbn in Hnth. inversion Hnth; subst item.
  eexists. exact Hselected.
Qed.

Theorem phase1_surface_refine_unary_expression_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "unary_expression")
      input rest
      (phase1_surface_unary_expression_recursive_refined_spine_tree previous) ->
    exists expression,
      phase1_surface_refine_unary_expression_recursive_grouping previous =
        Some expression /\
      phase1_surface_unary_expression_recursive_grouping_spine_tree expression =
        phase1_surface_unary_expression_recursive_refined_spine_tree previous.
Proof.
  intros path input rest previous. revert path input rest.
  induction previous as [operand IH | postfix];
    intros path input rest Hderive.
  - destruct (phase1_surface_unary_recursive_grouping_negate_derivation
      path input rest
      (phase1_surface_unary_expression_recursive_refined_spine_tree operand)
      Hderive) as [operand_path [operand_input Hoperand]].
    destruct (IH operand_path operand_input rest Hoperand)
      as [refined [Hrefine _]].
    assert (Hresult :
      phase1_surface_refine_unary_expression_recursive_grouping
        (Phase1SurfaceUnaryExpressionNegateRecursiveRefined operand) =
      Some (Phase1UnaryGroupingNegate refined)).
    { cbn. rewrite Hrefine. reflexivity. }
    exists (Phase1UnaryGroupingNegate refined). split.
    + exact Hresult.
    + eapply phase1_surface_refine_unary_expression_recursive_grouping_round_trip.
      exact Hresult.
  - destruct (phase1_surface_unary_recursive_grouping_postfix_derivation
      path input rest (phase1_surface_postfix_expression_refined_spine_tree postfix)
      Hderive) as [postfix_path Hpostfix].
    destruct
      (phase1_surface_refine_postfix_expression_recursive_grouping_total_from_derivation
        postfix_path input rest postfix Hpostfix)
      as [refined [Hrefine _]].
    assert (Hresult :
      phase1_surface_refine_unary_expression_recursive_grouping
        (Phase1SurfaceUnaryExpressionPostfixRecursiveRefined postfix) =
      Some (Phase1UnaryGroupingPostfix refined)).
    { cbn. rewrite Hrefine. reflexivity. }
    exists (Phase1UnaryGroupingPostfix refined). split.
    + exact Hresult.
    + eapply phase1_surface_refine_unary_expression_recursive_grouping_round_trip.
      exact Hresult.
Qed.

Theorem
  phase1_surface_unary_expression_recursive_grouping_sufficient_fuel_from_derivation :
  forall fuel path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "unary_expression")
      input rest tree ->
    phase1_surface_grouping_tree_size tree <= fuel ->
    exists expression,
      phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel
        fuel tree = Some expression /\
      phase1_surface_unary_expression_recursive_grouping_spine_tree expression =
        tree.
Proof.
  induction fuel as [|fuel IH]; intros path input rest tree Hderive Hbound.
  - pose proof (phase1_surface_grouping_tree_size_positive tree). lia.
  - destruct (phase1_surface_normalize_unary_expression_spine_total_from_derivation
      path input rest tree Hderive)
      as [[operand | postfix] [Hshell Htree]].
    + rewrite <- Htree in Hderive.
      destruct (phase1_surface_unary_recursive_grouping_negate_derivation
        path input rest operand Hderive)
        as [operand_path [operand_input Hoperand]].
      assert (Hoperand_bound : phase1_surface_grouping_tree_size operand <= fuel).
      {
        rewrite <- Htree in Hbound.
        change
          (S (S (S (S (phase1_surface_grouping_tree_size operand + 0)))) <=
            S fuel) in Hbound.
        lia.
      }
      destruct (IH operand_path operand_input rest operand Hoperand Hoperand_bound)
        as [refined [Hnormalize _]].
      assert (Hresult :
        phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel
          (S fuel) tree = Some (Phase1UnaryGroupingNegate refined)).
      {
        cbn -[phase1_surface_normalize_unary_expression_spine].
        rewrite Hshell, Hnormalize. reflexivity.
      }
      exists (Phase1UnaryGroupingNegate refined). split.
      * exact Hresult.
      * eapply
          phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel_round_trip.
        exact Hresult.
    + rewrite <- Htree in Hderive.
      destruct (phase1_surface_unary_recursive_grouping_postfix_derivation
        path input rest postfix Hderive) as [postfix_path Hpostfix].
      destruct
        (phase1_surface_normalize_postfix_expression_recursive_grouping_tree_total_from_derivation
          postfix_path input rest postfix Hpostfix)
        as [refined [Hnormalize _]].
      assert (Hresult :
        phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel
          (S fuel) tree = Some (Phase1UnaryGroupingPostfix refined)).
      {
        cbn -[phase1_surface_normalize_unary_expression_spine
          phase1_surface_normalize_postfix_expression_recursive_grouping_tree].
        rewrite Hshell, Hnormalize. reflexivity.
      }
      exists (Phase1UnaryGroupingPostfix refined). split.
      * exact Hresult.
      * eapply
          phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel_round_trip.
        exact Hresult.
Qed.

Theorem
  phase1_surface_normalize_unary_expression_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "unary_expression")
      input rest tree ->
    exists expression,
      phase1_surface_normalize_unary_expression_recursive_grouping_tree tree =
        Some expression /\
      phase1_surface_unary_expression_recursive_grouping_spine_tree expression =
        tree.
Proof.
  intros path input rest tree Hderive.
  exact
    (phase1_surface_unary_expression_recursive_grouping_sufficient_fuel_from_derivation
      (phase1_surface_grouping_tree_size tree) path input rest tree
      Hderive (Nat.le_refl _)).
Qed.
