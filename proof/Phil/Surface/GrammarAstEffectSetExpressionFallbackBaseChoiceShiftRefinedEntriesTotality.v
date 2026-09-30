From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedListTotality
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedFuelCombine
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceShiftRefinedTotality.

Import ListNotations.
Open Scope string_scope.

Lemma
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel_total_from_entries_derivation :
  forall effects path input rest,
    Derives phase1_surface_rules path
      (EOptional
        (ESequence
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence [ELiteral ","; ENonterminal "effect_expression"])
          ]))
      input rest
      (phase1_surface_effect_expression_expression_fallback_base_choice_entries_tree
        effects) ->
    exists fuel refined,
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
        fuel effects = Some refined.
Proof.
  intros effects path input rest Hderive.
  destruct effects as [|first rest_effects].
  - exists 0, [].
    reflexivity.
  - cbn in Hderive |- *.
    inversion Hderive; subst.
    match goal with
    | Hbody : Derives phase1_surface_rules _
        (ESequence
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence [ELiteral ","; ENonterminal "effect_expression"])
          ])
        _ _
        (PTSequence
          [ phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
              first;
            PTRepetition
              (map
                phase1_surface_effect_expression_expression_fallback_base_choice_suffix_tree
                rest_effects)
          ]) |- _ =>
        destruct
          (derives_sequence_expression_exposes_items
            phase1_surface_rules _
            [ ENonterminal "effect_expression";
              ERepetition
                (ESequence [ELiteral ","; ENonterminal "effect_expression"])
            ]
            _ _
            (PTSequence
              [ phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
                  first;
                PTRepetition
                  (map
                    phase1_surface_effect_expression_expression_fallback_base_choice_suffix_tree
                    rest_effects)
              ])
            Hbody)
          as [trees [Htree Hitems]];
        inversion Htree; subst trees;
        repeat match goal with
        | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
            inversion Hseq; subst; clear Hseq
        end;
        match goal with
        | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
            inversion Hnil; subst; clear Hnil
        end;
        match goal with
        | Hfirst : Derives phase1_surface_rules _
            (ENonterminal "effect_expression") _ _
            (phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
              first),
          Hrepeat : Derives phase1_surface_rules _
            (ERepetition
              (ESequence [ELiteral ","; ENonterminal "effect_expression"]))
            _ _
            (PTRepetition
              (map
                phase1_surface_effect_expression_expression_fallback_base_choice_suffix_tree
                rest_effects)) |- _ =>
            destruct
              (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
                first _ _ _ Hfirst)
              as [first_fuel [refined_first Hfirst_refined]];
            destruct
              (phase1_surface_repetition_derivation_exposes
                _
                (ESequence [ELiteral ","; ENonterminal "effect_expression"])
                _ _
                (PTRepetition
                  (map
                    phase1_surface_effect_expression_expression_fallback_base_choice_suffix_tree
                    rest_effects))
                Hrepeat)
              as [rest_trees [Hrest_tree Hrest_body]];
            inversion Hrest_tree; subst rest_trees;
            destruct
              (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel_total_from_suffix_repetition
                _
                (ESequence [ELiteral ","; ENonterminal "effect_expression"])
                _ _
                (map
                  phase1_surface_effect_expression_expression_fallback_base_choice_suffix_tree
                  rest_effects)
                Hrest_body eq_refl rest_effects eq_refl)
              as [rest_fuel [refined_rest Hrest_refined]];
            destruct
              (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_cons_fuel_total
                first rest_effects
                first_fuel refined_first rest_fuel refined_rest
                Hfirst_refined Hrest_refined)
              as [fuel Hfuel];
            exists fuel, (refined_first :: refined_rest);
            exact Hfuel
        end
    end.
Qed.
