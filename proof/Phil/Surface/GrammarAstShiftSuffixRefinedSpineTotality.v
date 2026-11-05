From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstShiftSuffixRefinedSpine
  GrammarAstShiftExpressionSpineTotality
  GrammarAstAdditiveExpressionRefinedSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Derivation-driven converse for one refined shift suffix.

  The existing shift-suffix spine already exposes the exact << / >> operator
  and retains the additive_expression operand as a certified ParseTree. This
  slice composes that structural carrier with the completed refined
  additive-expression normalizer and proves that every derivable shift suffix
  has some finite fuel witness whose refined carrier reconstructs the exact
  certified suffix tree.

  Structural surface-grammar correspondence only. This does not yet lift the
  fuel witness across repeated suffix lists or prove totality for the completed
  shift-expression carrier, add evaluation semantics, change Grammar-v1, alter
  Haskell, refine enclosing base/expression layers, or claim broader
  production-parser soundness/completeness. It continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Theorem
  phase1_surface_normalize_shift_suffix_refined_spine_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_shift_suffix_expression_for_totality
      input rest tree ->
    exists fuel suffix refined,
      phase1_surface_normalize_shift_suffix_spine tree = Some suffix /\
      phase1_surface_normalize_shift_suffix_refined_spine_fuel
        fuel suffix = Some refined /\
      phase1_surface_shift_suffix_refined_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_shift_suffix_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ EAlternative phase1_surface_shift_operator_items_for_totality;
        ENonterminal "additive_expression"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (EAlternative phase1_surface_shift_operator_items_for_totality)
      [ ENonterminal "additive_expression" ]
      input rest trees Hitems)
    as [after_operator [operator_tree [tail_trees
      [Htrees [Hoperator Htail]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "additive_expression") []
      after_operator rest tail_trees Htail)
    as [after_right [right_tree [nil_trees
      [Htail_trees [Hright Hnil]]]]].
  rewrite Htrees, Htail_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (phase1_surface_normalize_shift_operator_spine_total_from_derivation
      _ _ _ operator_tree Hoperator)
    as [operator [Hoperator_normalize Hoperator_round_trip]].
  pose proof
    (phase1_surface_normalize_additive_expression_node_total_from_derivation
      _ _ _ right_tree Hright) as Hright_normalize.
  destruct
    (phase1_surface_normalize_additive_expression_refined_tree_fuel_total_from_derivation
      _ _ _ right_tree Hright)
    as [fuel [right_refined [Hright_refined Hright_round_trip]]].
  pose (suffix :=
    {| phase1_shift_suffix_spine_operator := operator;
       phase1_shift_suffix_spine_right := right_tree |}).
  assert (Hsuffix :
    phase1_surface_normalize_shift_suffix_spine tree = Some suffix).
  {
    rewrite Htree.
    unfold phase1_surface_normalize_shift_suffix_spine,
      phase1_surface_expect_sequence,
      phase1_surface_exact2.
    cbn.
    rewrite Hoperator_normalize, Hright_normalize.
    reflexivity.
  }
  pose (refined :=
    {| phase1_shift_suffix_refined_spine_operator := operator;
       phase1_shift_suffix_refined_spine_right := right_refined |}).
  assert (Hrefined :
    phase1_surface_normalize_shift_suffix_refined_spine_fuel
      fuel suffix = Some refined).
  {
    unfold phase1_surface_normalize_shift_suffix_refined_spine_fuel.
    cbn.
    rewrite Hright_refined.
    reflexivity.
  }
  exists fuel, suffix, refined.
  split.
  - exact Hsuffix.
  - split.
    + exact Hrefined.
    + transitivity (phase1_surface_shift_suffix_spine_tree suffix).
      * eapply
          phase1_surface_normalize_shift_suffix_refined_spine_fuel_tree_round_trip.
        exact Hrefined.
      * eapply phase1_surface_normalize_shift_suffix_spine_round_trip.
        exact Hsuffix.
Qed.
