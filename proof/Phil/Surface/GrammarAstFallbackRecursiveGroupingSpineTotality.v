From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstRecordTotality
  GrammarAstBaseExpressionChoiceSpine
  GrammarAstFallbackBaseChoiceSpine
  GrammarAstFallbackBaseChoiceTotality
  GrammarAstBaseExpressionRecursiveGroupingSpine
  GrammarAstBaseExpressionRecursiveGroupingSpineTotality
  GrammarAstFallbackRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  A reject fallback derivation supplies its base-expression derivation. That
  judgment discharges the new base carrier's totality obligation without a
  fuel or normalization-success premise. The fail branch retains its exact
  failure target; no additional failure-target semantics are claimed.
*)

Theorem
  phase1_surface_normalize_fallback_recursive_grouping_spine_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "fallback") input rest
      (phase1_surface_fallback_base_choice_spine_tree previous) ->
    exists refined,
      phase1_surface_normalize_fallback_recursive_grouping_spine previous =
        Some refined /\
      phase1_surface_fallback_recursive_grouping_spine_base refined = previous.
Proof.
  intros path input rest [failure_target | base] Hderive.
  - exists (Phase1FallbackGroupingFail failure_target).
    split; reflexivity.
  - destruct
      (derives_nonterminal_exposes_body
        phase1_surface_rules path "fallback" input rest _ Hderive)
      as [body [subtree [Hlookup [Htree Hbody]]]].
    rewrite phase1_surface_fallback_lookup_for_totality in Hlookup.
    inversion Hlookup; subst body.
    cbn [phase1_surface_fallback_base_choice_spine_tree] in Htree.
    inversion Htree; subst subtree.
    destruct
      (alternative_derivation_names_exact_branch
        phase1_surface_rules _ phase1_surface_fallback_items_for_totality
        input rest _ Hbody)
      as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
    inversion Hsubtree; subst index selected.
    cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules _
        [ELiteral "reject"; ENonterminal "base_expression"]
        input rest _ Hselected)
      as [trees [Hselected_tree Hitems]].
    inversion Hselected_tree; subst trees.
    destruct
      (derives_sequence_cons_exposes_head_exact
        phase1_surface_rules _ 0 (ELiteral "reject")
        [ENonterminal "base_expression"] input rest _ Hitems)
      as [after_keyword [keyword_tree [tail_trees
        [Htrees [Hkeyword Htail]]]]].
    inversion Htrees; subst keyword_tree tail_trees.
    destruct
      (derives_sequence_cons_exposes_head_exact
        phase1_surface_rules _ 1 (ENonterminal "base_expression") []
        after_keyword rest _ Htail)
      as [after_base [base_tree [nil_trees
        [Htail_trees [Hbase Hnil]]]]].
    inversion Htail_trees; subst base_tree nil_trees.
    destruct
      (phase1_surface_normalize_base_expression_recursive_grouping_spine_total_from_derivation
        _ _ _ base Hbase)
      as [actual [Hnormalize Hbase_round_trip]].
    exists (Phase1FallbackGroupingReject actual).
    split.
    + unfold phase1_surface_normalize_fallback_recursive_grouping_spine.
      rewrite Hnormalize.
      reflexivity.
    + cbn [phase1_surface_fallback_recursive_grouping_spine_base].
      rewrite Hbase_round_trip.
      reflexivity.
Qed.

Theorem
  phase1_surface_normalize_fallback_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "fallback")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_fallback_recursive_grouping_tree tree =
        Some refined /\
      phase1_surface_fallback_recursive_grouping_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_fallback_base_choice_spine_total_from_derivation
      path input rest tree Hderive)
    as [previous [Hprevious Hprevious_tree]].
  rewrite <- Hprevious_tree in Hderive.
  destruct
    (phase1_surface_normalize_fallback_recursive_grouping_spine_total_from_derivation
      path input rest previous Hderive)
    as [refined [Hnormalize Hbase]].
  exists refined.
  split.
  - unfold phase1_surface_normalize_fallback_recursive_grouping_tree.
    rewrite Hprevious.
    exact Hnormalize.
  - unfold phase1_surface_fallback_recursive_grouping_spine_tree.
    rewrite Hbase.
    exact Hprevious_tree.
Qed.

Theorem
  phase1_surface_refine_fallback_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "fallback") input rest
      (phase1_surface_fallback_base_choice_spine_tree previous) ->
    exists refined,
      phase1_surface_refine_fallback_recursive_grouping previous = Some refined /\
      phase1_surface_fallback_recursive_grouping_spine_tree refined =
        phase1_surface_fallback_base_choice_spine_tree previous.
Proof.
  intros path input rest previous Hderive.
  destruct
    (phase1_surface_normalize_fallback_recursive_grouping_spine_total_from_derivation
      path input rest previous Hderive)
    as [refined [Hnormalize Hbase]].
  exists refined.
  split.
  - exact Hnormalize.
  - unfold phase1_surface_fallback_recursive_grouping_spine_tree.
    rewrite Hbase.
    reflexivity.
Qed.
