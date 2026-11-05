From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstRecordTotality
  GrammarAstBaseExpressionChoiceSpine
  GrammarAstFallbackBaseChoiceSpine
  GrammarAstExpressionOuterTotality
  GrammarAstExpressionFallbackBaseChoiceSpine
  GrammarAstExpressionFallbackBaseChoiceTotality
  GrammarAstExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstBaseExpressionRecursiveGroupingSpine
  GrammarAstBaseExpressionRecursiveGroupingSpineTotality
  GrammarAstFallbackRecursiveGroupingSpine
  GrammarAstFallbackRecursiveGroupingSpineTotality
  GrammarAstExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  Derivations supply both the main base-expression obligation and the optional
  fallback obligation. The latter exposes a fallback derivation when present,
  so reject payload conversion does not assume normalization succeeds.

  Public shell, raw-tree, and legacy-adapter totality use only grammar Derives
  premises. Failure targets, command bodies, and the generic grouping carrier's
  own nested fallback boundary retain their documented scope.
*)

Lemma
  phase1_surface_normalize_optional_fallback_recursive_grouping_spine_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path
      (EOptional (ESequence [ELiteral "or"; ENonterminal "fallback"]))
      input rest
      (phase1_surface_optional_expression_fallback_base_choice_tree previous) ->
    exists refined,
      phase1_surface_normalize_optional_fallback_recursive_grouping_spine
        previous = Some refined /\
      option_map phase1_surface_fallback_recursive_grouping_spine_base refined =
        previous.
Proof.
  intros path input rest [fallback |] Hderive.
  - destruct
      (optional_derivation_exposes_presence
        phase1_surface_rules path
        (ESequence [ELiteral "or"; ENonterminal "fallback"])
        input rest _ Hderive)
      as [[_ Hnone] | [body [Hsome Hbody]]].
    + cbn [phase1_surface_optional_expression_fallback_base_choice_tree] in Hnone.
      discriminate Hnone.
    + cbn [phase1_surface_optional_expression_fallback_base_choice_tree] in Hsome.
      inversion Hsome; subst body.
      destruct
        (derives_sequence_expression_exposes_items
          phase1_surface_rules _
          [ELiteral "or"; ENonterminal "fallback"]
          input rest _ Hbody)
        as [trees [Hsequence Hitems]].
      cbn [phase1_surface_expression_fallback_base_choice_tail_tree] in Hsequence.
      inversion Hsequence; subst trees.
      destruct
        (derives_sequence_cons_exposes_head_exact
          phase1_surface_rules _ 0 (ELiteral "or")
          [ENonterminal "fallback"] input rest _ Hitems)
        as [after_or [or_tree [tail_trees
          [Htrees [Hor Htail]]]]].
      inversion Htrees; subst or_tree tail_trees.
      destruct
        (derives_sequence_cons_exposes_head_exact
          phase1_surface_rules _ 1 (ENonterminal "fallback") []
          after_or rest _ Htail)
        as [after_fallback [fallback_tree [nil_trees
          [Htail_trees [Hfallback Hnil]]]]].
      inversion Htail_trees; subst fallback_tree nil_trees.
      destruct
        (phase1_surface_normalize_fallback_recursive_grouping_spine_total_from_derivation
          _ _ _ fallback Hfallback)
        as [actual [Hnormalize Hbase]].
      exists (Some actual).
      split.
      * cbn [phase1_surface_normalize_optional_fallback_recursive_grouping_spine].
        rewrite Hnormalize.
        reflexivity.
      * cbn [option_map].
        rewrite Hbase.
        reflexivity.
  - exists None.
    split; reflexivity.
Qed.

Theorem
  phase1_surface_normalize_expression_recursive_grouping_spine_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "expression") input rest
      (phase1_surface_expression_fallback_base_choice_spine_tree previous) ->
    exists refined,
      phase1_surface_normalize_expression_recursive_grouping_spine previous =
        Some refined /\
      phase1_surface_expression_recursive_grouping_spine_base refined = previous.
Proof.
  intros path input rest [base fallback] Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "expression" input rest _ Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  cbn [phase1_surface_expression_fallback_base_choice_spine_tree
    phase1_expression_fallback_base_choice_spine_base
    phase1_expression_fallback_base_choice_spine_fallback] in Htree.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules _
      [ ENonterminal "base_expression";
        EOptional (ESequence [ELiteral "or"; ENonterminal "fallback"]) ]
      input rest _ Hbody)
    as [trees [Hsequence Hitems]].
  inversion Hsequence; subst trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 0 (ENonterminal "base_expression")
      [EOptional (ESequence [ELiteral "or"; ENonterminal "fallback"])]
      input rest _ Hitems)
    as [after_base [base_tree [tail_trees
      [Htrees [Hbase Htail]]]]].
  inversion Htrees; subst base_tree tail_trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 1
      (EOptional (ESequence [ELiteral "or"; ENonterminal "fallback"])) []
      after_base rest _ Htail)
    as [after_fallback [fallback_tree [nil_trees
      [Htail_trees [Hfallback Hnil]]]]].
  inversion Htail_trees; subst fallback_tree nil_trees.
  destruct
    (phase1_surface_normalize_base_expression_recursive_grouping_spine_total_from_derivation
      _ _ _ base Hbase)
    as [actual_base [Hbase_normalize Hbase_round_trip]].
  destruct
    (phase1_surface_normalize_optional_fallback_recursive_grouping_spine_total_from_derivation
      _ _ _ fallback Hfallback)
    as [actual_fallback [Hfallback_normalize Hfallback_round_trip]].
  exists
    {| phase1_expression_recursive_grouping_spine_base := actual_base;
       phase1_expression_recursive_grouping_spine_fallback := actual_fallback |}.
  split.
  - unfold phase1_surface_normalize_expression_recursive_grouping_spine.
    cbn [phase1_expression_fallback_base_choice_spine_base
      phase1_expression_fallback_base_choice_spine_fallback].
    rewrite Hbase_normalize, Hfallback_normalize.
    reflexivity.
  - unfold phase1_surface_expression_recursive_grouping_spine_base.
    cbn [phase1_expression_recursive_grouping_spine_base
      phase1_expression_recursive_grouping_spine_fallback].
    rewrite Hbase_round_trip, Hfallback_round_trip.
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_expression_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_expression_recursive_grouping_tree tree =
        Some refined /\
      phase1_surface_expression_recursive_grouping_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_expression_fallback_base_choice_tree_total_from_derivation
      path input rest tree Hderive)
    as [previous [Hprevious Hprevious_tree]].
  rewrite <- Hprevious_tree in Hderive.
  destruct
    (phase1_surface_normalize_expression_recursive_grouping_spine_total_from_derivation
      path input rest previous Hderive)
    as [refined [Hnormalize Hbase]].
  exists refined.
  split.
  - unfold phase1_surface_normalize_expression_recursive_grouping_tree.
    rewrite Hprevious.
    exact Hnormalize.
  - unfold phase1_surface_expression_recursive_grouping_spine_tree.
    rewrite Hbase.
    exact Hprevious_tree.
Qed.

Theorem
  phase1_surface_refine_expression_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "expression") input rest
      (phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
        previous) ->
    exists refined,
      phase1_surface_refine_expression_recursive_grouping previous = Some refined /\
      phase1_surface_expression_recursive_grouping_spine_tree refined =
        phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
          previous.
Proof.
  intros path input rest previous Hderive.
  exact
    (phase1_surface_normalize_expression_recursive_grouping_tree_total_from_derivation
      path input rest _ Hderive).
Qed.
