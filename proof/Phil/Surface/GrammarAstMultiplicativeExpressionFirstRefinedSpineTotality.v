From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstMultiplicativeExpressionFirstRefinedSpine
  GrammarAstMultiplicativeExpressionSpineTotality
  GrammarAstUnaryExpressionRecursiveRefinedSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the first-operand multiplicative-expression refinement introduced
  after the recursive unary-expression carrier was completed.

  Every derivable multiplicative_expression tree has a leading unary_expression
  derivation. The recursive unary totality theorem therefore supplies finite
  normalization fuel for that leading operand. The already-proved
  multiplicative shell totality lemmas normalize the repeated suffixes, which
  remain exact certified ParseTrees in this refinement.

  Structural correspondence only. This proves totality and exact parse-tree
  reconstruction for the first-refined carrier; it does not yet refine repeated
  suffix operands, add evaluation semantics, change Grammar-v1, alter Haskell,
  or make broader production-parser claims. It continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Theorem
  phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "multiplicative_expression")
      input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_multiplicative_expression_first_refined_spine_tree refined =
        tree.
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
      _ _ _ first_tree Hfirst) as Hfirst_node.
  destruct
    (phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel_total_from_derivation
      _ _ _ first_tree Hfirst)
    as [fuel [first_refined [Hfirst_refined Hfirst_round_trip]]].
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
  assert (Hexpression :
    phase1_surface_normalize_multiplicative_expression_spine tree =
      Some expression).
  {
    rewrite Htree, Hsubtree, Hrest_tree.
    unfold phase1_surface_normalize_multiplicative_expression_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact2,
      phase1_surface_expect_repetition.
    cbn.
    rewrite Hfirst_node, Hrest_normalize.
    reflexivity.
  }
  pose (refined :=
    {| phase1_multiplicative_expression_first_refined_spine_first :=
         first_refined;
       phase1_multiplicative_expression_first_refined_spine_rest :=
         rest_suffixes |}).
  assert (Hresult :
    phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel
      fuel tree = Some refined).
  {
    unfold
      phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel.
    rewrite Hexpression.
    unfold
      phase1_surface_normalize_multiplicative_expression_first_refined_spine_fuel.
    cbn.
    rewrite Hfirst_refined.
    reflexivity.
  }
  exists fuel, refined.
  split.
  - exact Hresult.
  - eapply
      phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel_round_trip.
    exact Hresult.
Qed.
