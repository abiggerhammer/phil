From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstRecordTotality
  GrammarAstSourceHeaderTotality
  GrammarAstShiftExpressionSpine
  GrammarAstShiftExpressionSpineTotality
  GrammarAstShiftExpressionRefinedSpine
  GrammarAstAdditiveExpressionRecursiveGroupingSpine
  GrammarAstAdditiveExpressionRecursiveGroupingSpineTotality
  GrammarAstShiftExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  A grammar derivation supplies the leading operand derivation and a derivation
  for every suffix right operand. Normalization uses the lower layer's total
  computed-fuel entry point at each position. No caller-supplied fuel or
  recursive normalization-success hypothesis occurs in the public theorems.

  The suffix-list proof preserves every operator and its position. As with the
  lower carrier, these are structural correspondence statements, not semantic
  checking or a production Haskell AST binding.
*)

Lemma
  phase1_surface_normalize_shift_suffix_recursive_grouping_spine_total_from_derivation :
  forall path input rest suffix,
    Derives phase1_surface_rules path
      phase1_surface_shift_suffix_expression_for_totality
      input rest (phase1_surface_shift_suffix_spine_tree suffix) ->
    exists refined,
      phase1_surface_normalize_shift_suffix_recursive_grouping_spine
        suffix = Some refined /\
      phase1_surface_shift_suffix_recursive_grouping_spine_base refined =
        suffix.
Proof.
  intros path input rest [operator right_tree] Hderive.
  unfold phase1_surface_shift_suffix_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ EAlternative phase1_surface_shift_operator_items_for_totality;
        ENonterminal "additive_expression" ]
      input rest _ Hderive)
    as [trees [Htree Hitems]].
  cbn [phase1_surface_shift_suffix_spine_tree
    phase1_shift_suffix_spine_operator
    phase1_shift_suffix_spine_right
    phase1_surface_additive_expression_node_tree] in Htree.
  inversion Htree; subst trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (EAlternative phase1_surface_shift_operator_items_for_totality)
      [ ENonterminal "additive_expression" ]
      input rest _ Hitems)
    as [after_operator [operator_tree [tail_trees
      [Htrees [Hoperator Htail]]]]].
  inversion Htrees; subst operator_tree tail_trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "additive_expression") []
      after_operator rest _ Htail)
    as [after_right [right_tree' [nil_trees
      [Htail_trees [Hright Hnil]]]]].
  inversion Htail_trees; subst right_tree' nil_trees.
  destruct
    (phase1_surface_normalize_additive_expression_recursive_grouping_tree_total_from_derivation
      _ _ _ right_tree Hright)
    as [right_operand [Hnormalize Hround_trip]].
  exists
    {| phase1_shift_suffix_recursive_grouping_spine_operator := operator;
       phase1_shift_suffix_recursive_grouping_spine_right :=
         right_operand |}.
  split.
  - unfold phase1_surface_normalize_shift_suffix_recursive_grouping_spine.
    cbn [phase1_shift_suffix_spine_operator
      phase1_shift_suffix_spine_right].
    rewrite Hnormalize.
    reflexivity.
  - unfold phase1_surface_shift_suffix_recursive_grouping_spine_base.
    cbn [phase1_shift_suffix_recursive_grouping_spine_operator
      phase1_shift_suffix_recursive_grouping_spine_right].
    rewrite Hround_trip.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_shift_suffix_recursive_grouping_spines_total_from_repetition :
  forall suffixes path input rest,
    DerivesRepetition phase1_surface_rules path
      phase1_surface_shift_suffix_expression_for_totality input rest
      (map phase1_surface_shift_suffix_spine_tree suffixes) ->
    exists refined,
      phase1_surface_normalize_shift_suffix_recursive_grouping_spines
        suffixes = Some refined /\
      map phase1_surface_shift_suffix_recursive_grouping_spine_base
        refined = suffixes.
Proof.
  induction suffixes as [|suffix suffixes IH]; intros path input rest Hderive.
  - exists []. split; reflexivity.
  - cbn in Hderive.
    inversion Hderive as
      [|path' body' input' middle rest' tree trees Hitem Hprogress Htail]; subst.
    destruct
      (phase1_surface_normalize_shift_suffix_recursive_grouping_spine_total_from_derivation
        _ _ _ suffix Hitem)
      as [head [Hhead Hhead_base]].
    destruct (IH _ _ _ Htail) as [tail [Htail_normalize Htail_base]].
    exists (head :: tail).
    split.
    + cbn [phase1_surface_normalize_shift_suffix_recursive_grouping_spines].
      rewrite Hhead, Htail_normalize.
      reflexivity.
    + cbn.
      rewrite Hhead_base, Htail_base.
      reflexivity.
Qed.

Theorem
  phase1_surface_normalize_shift_expression_recursive_grouping_spine_total_from_derivation :
  forall path input rest expression,
    Derives phase1_surface_rules path
      (ENonterminal "shift_expression") input rest
      (phase1_surface_shift_expression_spine_tree expression) ->
    exists refined,
      phase1_surface_normalize_shift_expression_recursive_grouping_spine
        expression = Some refined /\
      phase1_surface_shift_expression_recursive_grouping_spine_base
        refined = expression.
Proof.
  intros path input rest [first_tree suffixes] Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "shift_expression"
      input rest _ Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_shift_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  cbn [phase1_surface_shift_expression_spine_tree
    phase1_shift_expression_spine_first
    phase1_shift_expression_spine_rest
    phase1_surface_additive_expression_node_tree] in Htree.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules _
      [ ENonterminal "additive_expression";
        ERepetition phase1_surface_shift_suffix_expression_for_totality ]
      input rest _ Hbody)
    as [trees [Hsubtree Hitems]].
  inversion Hsubtree; subst trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 0
      (ENonterminal "additive_expression")
      [ ERepetition phase1_surface_shift_suffix_expression_for_totality ]
      input rest _ Hitems)
    as [after_first [first_tree' [tail_trees
      [Htrees [Hfirst Htail]]]]].
  inversion Htrees; subst first_tree' tail_trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 1
      (ERepetition phase1_surface_shift_suffix_expression_for_totality) []
      after_first rest _ Htail)
    as [after_rest [rest_tree [nil_trees
      [Htail_trees [Hrest Hnil]]]]].
  inversion Htail_trees; subst rest_tree nil_trees.
  destruct
    (phase1_surface_repetition_derivation_exposes
      _ phase1_surface_shift_suffix_expression_for_totality
      _ _ _ Hrest)
    as [trees [Hrepetition_tree Hsuffixes]].
  inversion Hrepetition_tree; subst trees.
  destruct
    (phase1_surface_normalize_additive_expression_recursive_grouping_tree_total_from_derivation
      _ _ _ first_tree Hfirst)
    as [first [Hfirst_normalize Hfirst_round_trip]].
  destruct
    (phase1_surface_normalize_shift_suffix_recursive_grouping_spines_total_from_repetition
      suffixes _ _ _ Hsuffixes)
    as [refined_suffixes [Hsuffixes_normalize Hsuffixes_base]].
  exists
    {| phase1_shift_expression_recursive_grouping_spine_first := first;
       phase1_shift_expression_recursive_grouping_spine_rest :=
         refined_suffixes |}.
  split.
  - unfold phase1_surface_normalize_shift_expression_recursive_grouping_spine.
    cbn [phase1_shift_expression_spine_first
      phase1_shift_expression_spine_rest].
    rewrite Hfirst_normalize, Hsuffixes_normalize.
    reflexivity.
  - unfold phase1_surface_shift_expression_recursive_grouping_spine_base.
    cbn [phase1_shift_expression_recursive_grouping_spine_first
      phase1_shift_expression_recursive_grouping_spine_rest].
    rewrite Hfirst_round_trip, Hsuffixes_base.
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_shift_expression_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "shift_expression") input rest tree ->
    exists refined,
      phase1_surface_normalize_shift_expression_recursive_grouping_tree
        tree = Some refined /\
      phase1_surface_shift_expression_recursive_grouping_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_shift_expression_spine_total_from_derivation
      path input rest tree Hderive)
    as [expression [Hexpression Hexpression_tree]].
  rewrite <- Hexpression_tree in Hderive.
  destruct
    (phase1_surface_normalize_shift_expression_recursive_grouping_spine_total_from_derivation
      path input rest expression Hderive)
    as [refined [Hnormalize Hbase]].
  exists refined.
  split.
  - unfold phase1_surface_normalize_shift_expression_recursive_grouping_tree.
    rewrite Hexpression.
    exact Hnormalize.
  - unfold phase1_surface_shift_expression_recursive_grouping_spine_tree.
    rewrite Hbase.
    exact Hexpression_tree.
Qed.

Theorem
  phase1_surface_refine_shift_expression_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path
      (ENonterminal "shift_expression") input rest
      (phase1_surface_shift_expression_refined_spine_tree previous) ->
    exists refined,
      phase1_surface_refine_shift_expression_recursive_grouping previous =
        Some refined /\
      phase1_surface_shift_expression_recursive_grouping_spine_tree
        refined =
        phase1_surface_shift_expression_refined_spine_tree previous.
Proof.
  intros path input rest previous Hderive.
  exact
    (phase1_surface_normalize_shift_expression_recursive_grouping_tree_total_from_derivation
      path input rest _ Hderive).
Qed.
