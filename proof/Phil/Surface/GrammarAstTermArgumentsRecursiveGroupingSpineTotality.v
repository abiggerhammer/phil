From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstRecordTotality
  GrammarAstSourceHeaderTotality
  GrammarAstTermArgumentsSpine
  GrammarAstTermArgumentsTotality
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstExpressionRecursiveGroupingSpine
  GrammarAstExpressionRecursiveGroupingSpineTotality
  GrammarAstTermArgumentsRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  Every repeated comma suffix supplies an expression derivation. Induction
  over that list proves conversion for every argument, then the optional
  entries and outer parenthesized shell compose the result. Empty arguments
  denote the present term_arguments tree "()", not an enclosing absent node.

  Public shell, raw-tree, and legacy-adapter totality require only grammar
  Derives judgments. No fuel witness or child-normalization-success premise is
  supplied by the caller. The expression carrier's boundaries are inherited.
*)

Lemma phase1_surface_term_argument_recursive_grouping_suffix_derivation :
  forall path input rest argument,
    Derives phase1_surface_rules path
      (ESequence [ELiteral ","; ENonterminal "expression"])
      input rest (phase1_surface_term_argument_suffix_tree argument) ->
    exists argument_path before_argument after_argument,
      Derives phase1_surface_rules argument_path (ENonterminal "expression")
        before_argument after_argument argument.
Proof.
  intros path input rest argument Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ELiteral ","; ENonterminal "expression"]
      input rest _ Hderive)
    as [trees [Htree Hitems]].
  cbn [phase1_surface_term_argument_suffix_tree
    phase1_surface_expression_node_tree] in Htree.
  inversion Htree; subst trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0 (ELiteral ",")
      [ENonterminal "expression"] input rest _ Hitems)
    as [after_comma [comma_tree [tail_trees
      [Htrees [Hcomma Htail]]]]].
  inversion Htrees; subst comma_tree tail_trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1 (ENonterminal "expression") []
      after_comma rest _ Htail)
    as [after_argument [argument_tree [nil_trees
      [Htail_trees [Hargument Hnil]]]]].
  inversion Htail_trees; subst argument_tree nil_trees.
  do 3 eexists.
  exact Hargument.
Qed.

Lemma
  phase1_surface_normalize_term_argument_recursive_grouping_values_total_from_repetition :
  forall arguments path input rest,
    DerivesRepetition phase1_surface_rules path
      (ESequence [ELiteral ","; ENonterminal "expression"])
      input rest (map phase1_surface_term_argument_suffix_tree arguments) ->
    exists refined,
      phase1_surface_normalize_term_argument_recursive_grouping_values arguments =
        Some refined /\
      map phase1_surface_expression_recursive_grouping_spine_tree refined =
        arguments.
Proof.
  induction arguments as [|argument arguments IH]; intros path input rest Hderive.
  - exists []. split; reflexivity.
  - cbn [map] in Hderive.
    inversion Hderive as
      [|path' body' input' middle rest' tree trees Hitem Hprogress Htail]; subst.
    destruct
      (phase1_surface_term_argument_recursive_grouping_suffix_derivation
        _ _ _ argument Hitem)
      as [argument_path [before_argument [after_argument Hargument]]].
    destruct
      (phase1_surface_normalize_expression_recursive_grouping_tree_total_from_derivation
        argument_path before_argument after_argument argument Hargument)
      as [actual [Hactual Hactual_tree]].
    destruct (IH _ _ _ Htail)
      as [actual_rest [Hactual_rest Hactual_rest_tree]].
    exists (actual :: actual_rest).
    split.
    + cbn [phase1_surface_normalize_term_argument_recursive_grouping_values].
      rewrite Hactual, Hactual_rest.
      reflexivity.
    + cbn [map].
      rewrite Hactual_tree, Hactual_rest_tree.
      reflexivity.
Qed.

Lemma
  phase1_surface_normalize_term_argument_recursive_grouping_values_total_from_entries_derivation :
  forall path input rest arguments,
    Derives phase1_surface_rules path
      (EOptional
        (ESequence
          [ ENonterminal "expression";
            ERepetition
              (ESequence [ELiteral ","; ENonterminal "expression"]) ]))
      input rest (phase1_surface_term_argument_entries_tree arguments) ->
    exists refined,
      phase1_surface_normalize_term_argument_recursive_grouping_values arguments =
        Some refined /\
      map phase1_surface_expression_recursive_grouping_spine_tree refined =
        arguments.
Proof.
  intros path input rest [|first arguments] Hderive.
  - exists []. split; reflexivity.
  - destruct
      (optional_derivation_exposes_presence
        phase1_surface_rules path
        (ESequence
          [ ENonterminal "expression";
            ERepetition
              (ESequence [ELiteral ","; ENonterminal "expression"]) ])
        input rest _ Hderive)
      as [[_ Hnone] | [body [Hsome Hbody]]].
    + cbn [phase1_surface_term_argument_entries_tree] in Hnone.
      discriminate Hnone.
    + cbn [phase1_surface_term_argument_entries_tree
        phase1_surface_expression_node_tree] in Hsome.
      inversion Hsome; subst body.
      destruct
        (derives_sequence_expression_exposes_items
          phase1_surface_rules _
          [ ENonterminal "expression";
            ERepetition
              (ESequence [ELiteral ","; ENonterminal "expression"]) ]
          input rest _ Hbody)
        as [trees [Hsequence Hitems]].
      inversion Hsequence; subst trees.
      destruct
        (derives_sequence_cons_exposes_head_exact
          phase1_surface_rules _ 0 (ENonterminal "expression")
          [ ERepetition
              (ESequence [ELiteral ","; ENonterminal "expression"]) ]
          input rest _ Hitems)
        as [after_first [first_tree [tail_trees
          [Htrees [Hfirst Htail]]]]].
      inversion Htrees; subst first_tree tail_trees.
      destruct
        (derives_sequence_cons_exposes_head_exact
          phase1_surface_rules _ 1
          (ERepetition
            (ESequence [ELiteral ","; ENonterminal "expression"])) []
          after_first rest _ Htail)
        as [after_suffixes [suffixes_tree [nil_trees
          [Htail_trees [Hsuffixes Hnil]]]]].
      inversion Htail_trees; subst suffixes_tree nil_trees.
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ (ESequence [ELiteral ","; ENonterminal "expression"])
          _ _ _ Hsuffixes)
        as [suffix_trees [Hsuffix_trees Hrepetition]].
      inversion Hsuffix_trees; subst suffix_trees.
      destruct
        (phase1_surface_normalize_expression_recursive_grouping_tree_total_from_derivation
          _ _ _ first Hfirst)
        as [actual_first [Hactual_first Hactual_first_tree]].
      destruct
        (phase1_surface_normalize_term_argument_recursive_grouping_values_total_from_repetition
          arguments _ _ _ Hrepetition)
        as [actual_rest [Hactual_rest Hactual_rest_tree]].
      exists (actual_first :: actual_rest).
      split.
      * cbn [phase1_surface_normalize_term_argument_recursive_grouping_values].
        rewrite Hactual_first, Hactual_rest.
        reflexivity.
      * cbn [map].
        rewrite Hactual_first_tree, Hactual_rest_tree.
        reflexivity.
Qed.

Theorem
  phase1_surface_normalize_term_arguments_recursive_grouping_spine_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "term_arguments") input rest
      (phase1_surface_term_arguments_spine_tree previous) ->
    exists refined,
      phase1_surface_normalize_term_arguments_recursive_grouping_spine previous =
        Some refined /\
      phase1_surface_term_arguments_recursive_grouping_spine_base refined = previous.
Proof.
  intros path input rest [arguments] Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "term_arguments" input rest _ Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_term_arguments_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  cbn [phase1_surface_term_arguments_spine_tree
    phase1_term_arguments_spine_arguments] in Htree.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules _
      [ ELiteral "(";
        EOptional
          (ESequence
            [ ENonterminal "expression";
              ERepetition
                (ESequence [ELiteral ","; ENonterminal "expression"]) ]);
        ELiteral ")" ]
      input rest _ Hbody)
    as [trees [Hsequence Hitems]].
  inversion Hsequence; subst trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 0 (ELiteral "(")
      [ EOptional
          (ESequence
            [ ENonterminal "expression";
              ERepetition
                (ESequence [ELiteral ","; ENonterminal "expression"]) ]);
        ELiteral ")" ]
      input rest _ Hitems)
    as [after_open [open_tree [tail_trees
      [Htrees [Hopen Htail]]]]].
  inversion Htrees; subst open_tree tail_trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 1
      (EOptional
        (ESequence
          [ ENonterminal "expression";
            ERepetition
              (ESequence [ELiteral ","; ENonterminal "expression"]) ]))
      [ELiteral ")"] after_open rest _ Htail)
    as [after_entries [entries_tree [close_trees
      [Htail_trees [Hentries Hclose]]]]].
  inversion Htail_trees; subst entries_tree close_trees.
  destruct
    (phase1_surface_normalize_term_argument_recursive_grouping_values_total_from_entries_derivation
      _ _ _ arguments Hentries)
    as [actual [Hnormalize Hmap]].
  exists {| phase1_term_arguments_recursive_grouping_spine_arguments := actual |}.
  split.
  - unfold phase1_surface_normalize_term_arguments_recursive_grouping_spine.
    cbn [phase1_term_arguments_spine_arguments].
    rewrite Hnormalize.
    reflexivity.
  - unfold phase1_surface_term_arguments_recursive_grouping_spine_base.
    cbn [phase1_term_arguments_recursive_grouping_spine_arguments].
    rewrite Hmap.
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_term_arguments_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "term_arguments")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_term_arguments_recursive_grouping_tree tree =
        Some refined /\
      phase1_surface_term_arguments_recursive_grouping_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_term_arguments_spine_total_from_derivation
      path input rest tree Hderive)
    as [previous [Hprevious Hprevious_tree]].
  rewrite <- Hprevious_tree in Hderive.
  destruct
    (phase1_surface_normalize_term_arguments_recursive_grouping_spine_total_from_derivation
      path input rest previous Hderive)
    as [refined [Hnormalize Hbase]].
  exists refined.
  split.
  - unfold phase1_surface_normalize_term_arguments_recursive_grouping_tree.
    rewrite Hprevious.
    exact Hnormalize.
  - unfold phase1_surface_term_arguments_recursive_grouping_spine_tree.
    rewrite Hbase.
    exact Hprevious_tree.
Qed.

Theorem
  phase1_surface_refine_term_arguments_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "term_arguments") input rest
      (phase1_surface_term_arguments_expression_fallback_base_choice_shift_refined_spine_tree
        previous) ->
    exists refined,
      phase1_surface_refine_term_arguments_recursive_grouping previous =
        Some refined /\
      phase1_surface_term_arguments_recursive_grouping_spine_tree refined =
        phase1_surface_term_arguments_expression_fallback_base_choice_shift_refined_spine_tree
          previous.
Proof.
  intros path input rest previous Hderive.
  exact
    (phase1_surface_normalize_term_arguments_recursive_grouping_tree_total_from_derivation
      path input rest _ Hderive).
Qed.
