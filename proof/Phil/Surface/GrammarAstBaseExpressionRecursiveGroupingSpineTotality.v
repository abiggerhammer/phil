From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstBaseExpressionChoiceSpine
  GrammarAstBaseExpressionChoiceTotality
  GrammarAstBaseExpressionShiftRefinedSpine
  GrammarAstShiftExpressionRecursiveGroupingSpine
  GrammarAstShiftExpressionRecursiveGroupingSpineTotality
  GrammarAstBaseExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001.
   A base-expression derivation supplies the shift child's derivation in the
   arithmetic branch. The command branch is retained exactly. Shell, raw-tree,
   and legacy-carrier totality require only the grammar derivation, without
   a caller-supplied fuel or normalization-success premise. *)

Theorem
  phase1_surface_normalize_base_expression_recursive_grouping_spine_total_from_derivation :
  forall path input rest expression,
    Derives phase1_surface_rules path (ENonterminal "base_expression")
      input rest (phase1_surface_base_expression_choice_spine_tree expression) ->
    exists refined,
      phase1_surface_normalize_base_expression_recursive_grouping_spine expression =
        Some refined /\
      phase1_surface_base_expression_recursive_grouping_spine_base refined =
        expression.
Proof.
  intros path input rest [command | shift] Hderive.
  - exists (Phase1BaseGroupingCommand command). split; reflexivity.
  - destruct (derives_nonterminal_exposes_body phase1_surface_rules path
      "base_expression" input rest _ Hderive)
      as [body [subtree [Hlookup [Htree Hbody]]]].
    rewrite phase1_surface_base_expression_lookup_for_totality in Hlookup.
    inversion Hlookup; subst body.
    cbn [phase1_surface_base_expression_choice_spine_tree] in Htree.
    inversion Htree; subst subtree.
    destruct (alternative_derivation_names_exact_branch phase1_surface_rules _
      phase1_surface_base_expression_items_for_totality input rest _ Hbody)
      as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
    inversion Hsubtree; subst index selected.
    cbn in Hnth. inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_shift_expression_recursive_grouping_tree_total_from_derivation
        _ input rest shift Hselected)
      as [converted [Hshift Hshift_tree]].
    exists (Phase1BaseGroupingShift converted). split.
    + unfold phase1_surface_normalize_base_expression_recursive_grouping_spine.
      rewrite Hshift. reflexivity.
    + cbn [phase1_surface_base_expression_recursive_grouping_spine_base].
      rewrite Hshift_tree. reflexivity.
Qed.

Theorem
  phase1_surface_normalize_base_expression_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "base_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_base_expression_recursive_grouping_tree tree =
        Some refined /\
      phase1_surface_base_expression_recursive_grouping_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_base_expression_choice_spine_total_from_derivation
      path input rest tree Hderive)
    as [expression [Hchoice Hchoice_tree]].
  rewrite <- Hchoice_tree in Hderive.
  destruct
    (phase1_surface_normalize_base_expression_recursive_grouping_spine_total_from_derivation
      path input rest expression Hderive)
    as [refined [Hnormalize Hbase]].
  exists refined. split.
  - unfold phase1_surface_normalize_base_expression_recursive_grouping_tree.
    rewrite Hchoice. exact Hnormalize.
  - unfold phase1_surface_base_expression_recursive_grouping_spine_tree.
    rewrite Hbase. exact Hchoice_tree.
Qed.

Theorem phase1_surface_refine_base_expression_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "base_expression")
      input rest (phase1_surface_base_expression_shift_refined_spine_tree previous) ->
    exists refined,
      phase1_surface_refine_base_expression_recursive_grouping previous =
        Some refined /\
      phase1_surface_base_expression_recursive_grouping_spine_tree refined =
        phase1_surface_base_expression_shift_refined_spine_tree previous.
Proof.
  intros path input rest previous Hderive.
  exact
    (phase1_surface_normalize_base_expression_recursive_grouping_tree_total_from_derivation
      path input rest _ Hderive).
Qed.
