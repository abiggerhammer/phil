From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedLiteralTotality
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstEffectSetExpressionFallbackBaseChoiceTotality.

Import ListNotations.
Open Scope string_scope.

Lemma
  phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_choice_fuel_total_from_spine_derivation :
  forall literal path input rest,
    Derives phase1_surface_rules path (ENonterminal "effect_set_expression")
      input rest
      (phase1_surface_effect_set_expression_fallback_base_choice_spine_tree
        (Phase1EffectSetExpressionFallbackBaseChoiceLiteral literal)) ->
    exists fuel refined,
      phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel
        fuel literal = Some refined.
Proof.
  intros literal path input rest Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_set_expression"
      input rest
      (PTNonterminal "effect_set_expression"
        (PTAlternative 0
          (phase1_surface_effect_set_expression_fallback_base_choice_literal_spine_tree
            literal)))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_effect_set_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_expression"))
      [ ENonterminal "effect_set_literal";
        ENonterminal "static_reference"
      ]
      input rest
      (PTAlternative 0
        (phase1_surface_effect_set_expression_fallback_base_choice_literal_spine_tree
          literal))
      Hbody)
    as [index [item [selected [Hnth [Hbranch Hselected]]]]].
  inversion Hbranch; subst index selected.
  cbn in Hnth.
  inversion Hnth; subst item.
  eapply
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel_total_from_spine_derivation.
  exact Hselected.
Qed.

Lemma
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation :
  forall effects path input rest,
    Derives phase1_surface_rules path (ENonterminal "effect_set_expression")
      input rest
      (phase1_surface_effect_set_expression_fallback_base_choice_spine_tree effects) ->
    exists fuel refined,
      phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel effects = Some refined.
Proof.
  intros effects path input rest Hderive.
  destruct effects as [literal | reference].
  - destruct
      (phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_choice_fuel_total_from_spine_derivation
        literal path input rest Hderive)
      as [fuel [refined Hrefined]].
    exists fuel,
      (Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedLiteral refined).
    cbn.
    rewrite Hrefined.
    reflexivity.
  - exists 0,
      (Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedReference reference).
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "effect_set_expression")
      input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_effect_set_expression_fallback_base_choice_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
      base path input rest Hcanonical)
    as [fuel [refined Hrefined]].
  assert (Hnormalize :
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined).
  {
    unfold
      phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel.
    rewrite Hbase.
    exact Hrefined.
  }
  exists fuel, refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip.
    exact Hnormalize.
Qed.
