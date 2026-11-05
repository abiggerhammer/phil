From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstRecordTotality
  GrammarAstPostfixExpressionSpine
  GrammarAstPostfixExpressionSpineTotality
  GrammarAstPostfixExpressionNamedRefinedSpine
  GrammarAstPostfixExpressionRefinedSpine
  GrammarAstPostfixExpressionRefinedSpineTotality
  GrammarAstPrimaryExpressionIntegerSpine
  GrammarAstPrimaryExpressionRecursiveGroupingSpine
  GrammarAstPrimaryExpressionRecursiveGroupingSpineTotality
  GrammarAstPostfixExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  Universal totality of the consuming postfix refinement on grammar-derived
  trees.  A postfix derivation supplies the primary child's derivation; that
  derivation, rather than a recursive normalization-success hypothesis,
  discharges the primary recursive grouping adapter's totality obligation.

  Named payloads retain their existing representation.  These theorems neither
  certify arbitrary forged carrier values nor lift the new postfix type into
  enclosing expression or source-declaration carriers.
*)

Lemma phase1_surface_postfix_expression_refined_primary_derivation :
  forall path input rest primary projections,
    Derives phase1_surface_rules path
      (ENonterminal "postfix_expression") input rest
      (phase1_surface_postfix_expression_refined_spine_tree
        (Phase1SurfacePostfixExpressionPrimaryRefined primary projections)) ->
    exists primary_path after_primary,
      Derives phase1_surface_rules primary_path
        (ENonterminal "primary_expression") input after_primary
        (phase1_surface_primary_expression_integer_spine_tree primary).
Proof.
  intros path input rest primary projections Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "postfix_expression" input rest _ Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_postfix_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  cbn in Htree.
  inversion Htree; subst subtree.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules _
      phase1_surface_postfix_expression_items_for_totality
      input rest _ Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  inversion Hsubtree; subst index selected.
  cbn in Hnth.
  inversion Hnth; subst item.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules _
      [ ENonterminal "primary_expression";
        ERepetition
          (ESequence [ELiteral "."; ENonterminal "identifier"])
      ]
      input rest _ Hselected)
    as [trees [Hselected_tree Hitems]].
  inversion Hselected_tree; subst trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 0
      (ENonterminal "primary_expression")
      [ ERepetition
          (ESequence [ELiteral "."; ENonterminal "identifier"])
      ]
      input rest _ Hitems)
    as [after_primary [primary_tree [tail_trees
      [Htrees [Hprimary Htail]]]]].
  inversion Htrees; subst primary_tree tail_trees.
  do 2 eexists.
  exact Hprimary.
Qed.

Theorem
  phase1_surface_refine_postfix_expression_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path
      (ENonterminal "postfix_expression") input rest
      (phase1_surface_postfix_expression_refined_spine_tree previous) ->
    exists expression,
      phase1_surface_refine_postfix_expression_recursive_grouping previous =
        Some expression /\
      phase1_surface_postfix_expression_recursive_grouping_spine_tree
        expression =
        phase1_surface_postfix_expression_refined_spine_tree previous.
Proof.
  intros path input rest previous Hderive.
  destruct previous as [named | primary projections].
  - exists (Phase1PostfixGroupingNamed named).
    split; reflexivity.
  - destruct
      (phase1_surface_postfix_expression_refined_primary_derivation
        path input rest primary projections Hderive)
      as [primary_path [after_primary Hprimary_derive]].
    destruct
      (phase1_surface_refine_primary_expression_recursive_grouping_total_from_derivation
        primary_path input after_primary primary Hprimary_derive)
      as [refined [Hprimary Hprimary_tree]].
    exists (Phase1PostfixGroupingPrimary refined projections).
    split.
    + unfold phase1_surface_refine_postfix_expression_recursive_grouping.
      rewrite Hprimary.
      reflexivity.
    + unfold phase1_surface_postfix_expression_recursive_grouping_spine_tree,
        phase1_surface_postfix_expression_refined_spine_tree.
      rewrite Hprimary_tree.
      reflexivity.
Qed.

Theorem
  phase1_surface_normalize_postfix_expression_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "postfix_expression") input rest tree ->
    exists expression,
      phase1_surface_normalize_postfix_expression_recursive_grouping_tree tree =
        Some expression /\
      phase1_surface_postfix_expression_recursive_grouping_spine_tree
        expression = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_postfix_expression_refined_tree_total_from_derivation
      path input rest tree Hderive)
    as [previous [Hprevious Hprevious_tree]].
  rewrite <- Hprevious_tree in Hderive.
  destruct
    (phase1_surface_refine_postfix_expression_recursive_grouping_total_from_derivation
      path input rest previous Hderive)
    as [expression [Hrefine Hexpression_tree]].
  exists expression.
  split.
  - unfold phase1_surface_normalize_postfix_expression_recursive_grouping_tree.
    rewrite Hprevious.
    exact Hrefine.
  - rewrite Hexpression_tree.
    exact Hprevious_tree.
Qed.
