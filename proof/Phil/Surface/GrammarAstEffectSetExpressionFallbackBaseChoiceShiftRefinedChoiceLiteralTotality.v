From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedLiteralTotality
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
