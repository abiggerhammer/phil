From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstMultiplicativeExpressionRefinedSpine
  GrammarAstMultiplicativeExpressionSpineTotality
  GrammarAstUnaryExpressionRecursiveRefinedSpineTotality
  GrammarAstUnaryExpressionRecursiveRefinedSpineFuelMonotonicity
  GrammarAstMultiplicativeExpressionRefinedSpineFuelSupport.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the completed multiplicative-expression refinement.

  One shared fuel value covers the leading recursive unary_expression and every
  repeated multiplicative suffix operand. The finite witnesses supplied by the
  grammar derivation are raised to a common Nat.max bound, so every derivable
  multiplicative_expression normalizes to the fully refined carrier and
  reconstructs its exact certified parse tree.

  Structural correspondence only. This does not add evaluation semantics,
  change Grammar-v1, alter Haskell, refine the enclosing additive-expression
  carrier, or make broader production-parser soundness/completeness claims.
  It continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Theorem
  phase1_surface_normalize_multiplicative_expression_refined_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "multiplicative_expression")
      input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_multiplicative_expression_refined_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_multiplicative_expression_refined_spine_tree refined =
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
    as [first_fuel [first_refined
      [Hfirst_refined Hfirst_round_trip]]].
  destruct
    (phase1_surface_repetition_derivation_exposes
      _ phase1_surface_multiplicative_suffix_expression_for_totality
      _ _ rest_tree Hrest)
    as [rest_trees [Hrest_tree Hrest_body]].
  destruct
    (phase1_surface_normalize_multiplicative_suffix_refined_spines_fuel_total_from_repetition
      _ phase1_surface_multiplicative_suffix_expression_for_totality
      _ _ rest_trees Hrest_body eq_refl)
    as [rest_fuel [rest_suffixes [refined_rest
      [Hrest_normalize Hrest_refined]]]].
  let fuel := constr:(Nat.max first_fuel rest_fuel) in
  pose proof
    (phase1_surface_normalize_unary_expression_recursive_refined_tree_fuel_monotone
      first_fuel fuel first_tree first_refined
      (Nat.le_max_l first_fuel rest_fuel)
      Hfirst_refined)
    as Hfirst_lifted.
  pose proof
    (phase1_surface_normalize_multiplicative_suffix_refined_spines_fuel_monotone
      rest_fuel fuel rest_suffixes refined_rest
      (Nat.le_max_r first_fuel rest_fuel)
      Hrest_refined)
    as Hrest_lifted.
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
  pose (first_expression :=
    {| phase1_multiplicative_expression_first_refined_spine_first :=
         first_refined;
       phase1_multiplicative_expression_first_refined_spine_rest :=
         rest_suffixes |}).
  assert (Hfirst_expression :
    phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel
      fuel tree = Some first_expression).
  {
    unfold
      phase1_surface_normalize_multiplicative_expression_first_refined_tree_fuel.
    rewrite Hexpression.
    unfold
      phase1_surface_normalize_multiplicative_expression_first_refined_spine_fuel.
    cbn.
    rewrite Hfirst_lifted.
    reflexivity.
  }
  pose (refined :=
    {| phase1_multiplicative_expression_refined_spine_first :=
         first_refined;
       phase1_multiplicative_expression_refined_spine_rest :=
         refined_rest |}).
  assert (Hresult :
    phase1_surface_normalize_multiplicative_expression_refined_tree_fuel
      fuel tree = Some refined).
  {
    unfold phase1_surface_normalize_multiplicative_expression_refined_tree_fuel.
    rewrite Hfirst_expression.
    unfold
      phase1_surface_normalize_multiplicative_expression_refined_spine_fuel.
    cbn.
    rewrite Hrest_lifted.
    reflexivity.
  }
  exists fuel, refined.
  split.
  - exact Hresult.
  - eapply
      phase1_surface_normalize_multiplicative_expression_refined_tree_fuel_round_trip.
    exact Hresult.
Qed.
