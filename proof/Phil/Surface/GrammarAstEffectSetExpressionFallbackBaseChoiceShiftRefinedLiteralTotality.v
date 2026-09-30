From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedEntriesTotality
  GrammarAstEffectSetExpressionFallbackBaseChoiceTotality.

Import ListNotations.
Open Scope string_scope.

Lemma
  phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel_total_from_spine_derivation :
  forall literal path input rest,
    Derives phase1_surface_rules path (ENonterminal "effect_set_literal")
      input rest
      (phase1_surface_effect_set_expression_fallback_base_choice_literal_spine_tree
        literal) ->
    exists fuel refined,
      phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_fuel
        fuel literal = Some refined.
Proof.
  intros [effects] path input rest Hderive.
  unfold
    phase1_surface_effect_set_expression_fallback_base_choice_literal_spine_tree
    in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_set_literal"
      input rest
      (PTNonterminal "effect_set_literal"
        (PTSequence
          [ PTLiteral "{";
            phase1_surface_effect_expression_expression_fallback_base_choice_entries_tree
              effects;
            PTLiteral "}"
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_effect_set_literal_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_literal"))
      [ ELiteral "{";
        EOptional
          (ESequence
            [ ENonterminal "effect_expression";
              ERepetition
                (ESequence [ELiteral ","; ENonterminal "effect_expression"])
            ]);
        ELiteral "}"
      ]
      input rest
      (PTSequence
        [ PTLiteral "{";
          phase1_surface_effect_expression_expression_fallback_base_choice_entries_tree
            effects;
          PTLiteral "}"
        ])
      Hbody)
    as [trees [Hsequence_tree Hitems]].
  inversion Hsequence_tree; subst trees.
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hentries : Derives phase1_surface_rules _
      (EOptional
        (ESequence
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence [ELiteral ","; ENonterminal "effect_expression"])
          ]))
      _ _
      (phase1_surface_effect_expression_expression_fallback_base_choice_entries_tree
        effects) |- _ =>
      destruct
        (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel_total_from_entries_derivation
          effects _ _ _ Hentries)
        as [fuel [refined_effects Hrefined_effects]];
      exists fuel,
        {| phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects :=
             refined_effects |};
      cbn;
      rewrite Hrefined_effects;
      reflexivity
  end.
Qed.
