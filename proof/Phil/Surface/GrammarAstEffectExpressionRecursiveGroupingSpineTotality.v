From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstRecordTotality
  GrammarAstStaticReferenceSpine
  GrammarAstEffectExpressionSpine
  GrammarAstEffectExpressionTotality
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstTermArgumentsRecursiveGroupingSpine
  GrammarAstTermArgumentsRecursiveGroupingSpineTotality
  GrammarAstEffectExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  The effect derivation supplies the optional term-arguments derivation. When
  present, the latter supplies the child's derivation for the raw normalizer or
  legacy adapter. No fuel or child-normalization-success premise is required.

  The static-reference value is retained exactly. These proofs do not claim
  additional validity for its interiors, and they preserve the inherited
  term-argument boundaries and absence-versus-present-empty distinction.
*)

Lemma phase1_surface_effect_expression_recursive_grouping_arguments_derivation :
  forall path input rest reference_tree arguments_tree,
    Derives phase1_surface_rules path (ENonterminal "effect_expression")
      input rest
      (PTNonterminal "effect_expression"
        (PTSequence [reference_tree; arguments_tree])) ->
    exists arguments_path before_arguments after_arguments,
      Derives phase1_surface_rules arguments_path
        (EOptional (ENonterminal "term_arguments"))
        before_arguments after_arguments arguments_tree.
Proof.
  intros path input rest reference_tree arguments_tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_expression" input rest _ Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_effect_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules _
      [ENonterminal "static_reference"; EOptional (ENonterminal "term_arguments")]
      input rest _ Hbody)
    as [trees [Hsequence Hitems]].
  inversion Hsequence; subst trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 0 (ENonterminal "static_reference")
      [EOptional (ENonterminal "term_arguments")]
      input rest _ Hitems)
    as [after_reference [actual_reference [tail_trees
      [Htrees [Hreference Htail]]]]].
  inversion Htrees; subst actual_reference tail_trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 1 (EOptional (ENonterminal "term_arguments")) []
      after_reference rest _ Htail)
    as [after_arguments [actual_arguments [nil_trees
      [Htail_trees [Harguments Hnil]]]]].
  inversion Htail_trees; subst actual_arguments nil_trees.
  do 3 eexists.
  exact Harguments.
Qed.

Lemma
  phase1_surface_normalize_optional_term_arguments_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "term_arguments")) input rest
      (phase1_surface_optional_term_arguments_tree previous) ->
    exists refined,
      phase1_surface_normalize_optional_term_arguments_recursive_grouping previous =
        Some refined /\
      option_map phase1_surface_term_arguments_recursive_grouping_spine_tree refined =
        previous.
Proof.
  intros path input rest [arguments_tree |] Hderive.
  - destruct
      (optional_derivation_exposes_presence
        phase1_surface_rules path (ENonterminal "term_arguments")
        input rest _ Hderive)
      as [[_ Hnone] | [body [Hsome Hbody]]].
    + cbn [phase1_surface_optional_term_arguments_tree] in Hnone.
      discriminate Hnone.
    + cbn [phase1_surface_optional_term_arguments_tree] in Hsome.
      inversion Hsome; subst body.
      destruct
        (phase1_surface_normalize_term_arguments_recursive_grouping_tree_total_from_derivation
          _ _ _ arguments_tree Hbody)
        as [actual [Hnormalize Htree]].
      exists (Some actual).
      split.
      * cbn [phase1_surface_normalize_optional_term_arguments_recursive_grouping].
        rewrite Hnormalize.
        reflexivity.
      * cbn [option_map].
        rewrite Htree.
        reflexivity.
  - exists None.
    split; reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_expression_recursive_grouping_spine_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "effect_expression")
      input rest (phase1_surface_effect_expression_spine_tree previous) ->
    exists refined,
      phase1_surface_normalize_effect_expression_recursive_grouping_spine previous =
        Some refined /\
      phase1_surface_effect_expression_recursive_grouping_spine_base refined =
        previous.
Proof.
  intros path input rest [reference arguments] Hderive.
  destruct
    (phase1_surface_effect_expression_recursive_grouping_arguments_derivation
      path input rest (phase1_surface_static_reference_spine_tree reference)
      (phase1_surface_optional_term_arguments_tree arguments) Hderive)
    as [arguments_path [before_arguments [after_arguments Harguments]]].
  destruct
    (phase1_surface_normalize_optional_term_arguments_recursive_grouping_total_from_derivation
      arguments_path before_arguments after_arguments arguments Harguments)
    as [actual [Hnormalize Hmap]].
  exists
    {| phase1_effect_expression_recursive_grouping_spine_reference := reference;
       phase1_effect_expression_recursive_grouping_spine_arguments := actual |}.
  split.
  - unfold phase1_surface_normalize_effect_expression_recursive_grouping_spine.
    cbn [phase1_effect_expression_spine_reference
      phase1_effect_expression_spine_arguments].
    rewrite Hnormalize.
    reflexivity.
  - unfold phase1_surface_effect_expression_recursive_grouping_spine_base.
    cbn [phase1_effect_expression_recursive_grouping_spine_reference
      phase1_effect_expression_recursive_grouping_spine_arguments].
    rewrite Hmap.
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_expression_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "effect_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_effect_expression_recursive_grouping_tree tree =
        Some refined /\
      phase1_surface_effect_expression_recursive_grouping_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_effect_expression_spine_total_from_derivation
      path input rest tree Hderive)
    as [previous [Hprevious Hprevious_tree]].
  rewrite <- Hprevious_tree in Hderive.
  destruct
    (phase1_surface_normalize_effect_expression_recursive_grouping_spine_total_from_derivation
      path input rest previous Hderive)
    as [refined [Hnormalize Hbase]].
  exists refined.
  split.
  - unfold phase1_surface_normalize_effect_expression_recursive_grouping_tree.
    rewrite Hprevious.
    exact Hnormalize.
  - unfold phase1_surface_effect_expression_recursive_grouping_spine_tree.
    rewrite Hbase.
    exact Hprevious_tree.
Qed.

Lemma
  phase1_surface_refine_optional_term_arguments_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "term_arguments")) input rest
      (phase1_surface_optional_term_arguments_expression_fallback_base_choice_shift_refined_tree
        previous) ->
    exists refined,
      phase1_surface_refine_optional_term_arguments_recursive_grouping previous =
        Some refined /\
      phase1_surface_optional_term_arguments_recursive_grouping_tree refined =
        phase1_surface_optional_term_arguments_expression_fallback_base_choice_shift_refined_tree
          previous.
Proof.
  intros path input rest [arguments |] Hderive.
  - destruct
      (optional_derivation_exposes_presence
        phase1_surface_rules path (ENonterminal "term_arguments")
        input rest _ Hderive)
      as [[_ Hnone] | [body [Hsome Hbody]]].
    + cbn
        [phase1_surface_optional_term_arguments_expression_fallback_base_choice_shift_refined_tree]
        in Hnone.
      discriminate Hnone.
    + cbn
        [phase1_surface_optional_term_arguments_expression_fallback_base_choice_shift_refined_tree]
        in Hsome.
      inversion Hsome; subst body.
      destruct
        (phase1_surface_refine_term_arguments_recursive_grouping_total_from_derivation
          _ _ _ arguments Hbody)
        as [actual [Hnormalize Htree]].
      assert (Hresult :
        phase1_surface_refine_optional_term_arguments_recursive_grouping
          (Some arguments) = Some (Some actual)).
      {
        cbn [phase1_surface_refine_optional_term_arguments_recursive_grouping].
        rewrite Hnormalize.
        reflexivity.
      }
      exists (Some actual).
      split.
      * exact Hresult.
      * eapply
          phase1_surface_refine_optional_term_arguments_recursive_grouping_round_trip.
        exact Hresult.
  - exists None.
    split; reflexivity.
Qed.

Theorem
  phase1_surface_refine_effect_expression_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "effect_expression") input rest
      (phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
        previous) ->
    exists refined,
      phase1_surface_refine_effect_expression_recursive_grouping previous =
        Some refined /\
      phase1_surface_effect_expression_recursive_grouping_spine_tree refined =
        phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
          previous.
Proof.
  intros path input rest [reference arguments] Hderive.
  destruct
    (phase1_surface_effect_expression_recursive_grouping_arguments_derivation
      path input rest (phase1_surface_static_reference_spine_tree reference)
      (phase1_surface_optional_term_arguments_expression_fallback_base_choice_shift_refined_tree
        arguments) Hderive)
    as [arguments_path [before_arguments [after_arguments Harguments]]].
  destruct
    (phase1_surface_refine_optional_term_arguments_recursive_grouping_total_from_derivation
      arguments_path before_arguments after_arguments arguments Harguments)
    as [actual [Hnormalize Htree]].
  assert (Hresult :
    phase1_surface_refine_effect_expression_recursive_grouping
      {| phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference :=
           reference;
         phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_arguments :=
           arguments |} =
      Some
        {| phase1_effect_expression_recursive_grouping_spine_reference := reference;
           phase1_effect_expression_recursive_grouping_spine_arguments := actual |}).
  {
    unfold phase1_surface_refine_effect_expression_recursive_grouping.
    cbn
      [phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference
       phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_arguments].
    rewrite Hnormalize.
    reflexivity.
  }
  exists
    {| phase1_effect_expression_recursive_grouping_spine_reference := reference;
       phase1_effect_expression_recursive_grouping_spine_arguments := actual |}.
  split.
  - exact Hresult.
  - eapply phase1_surface_refine_effect_expression_recursive_grouping_round_trip.
    exact Hresult.
Qed.
