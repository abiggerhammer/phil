From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementEffectsShiftRefinedSpine
  GrammarAstGenericRequirementEffectsTotality
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedChoiceLiteralTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Derivation-driven converse for the isolated shift-refined payload of
  generic_requirement alternative 6 ("effects ... within ...;").

  This remains structural Rocq surface correspondence only and continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel_total_from_derivation :
  forall name_tree effects path input rest,
    Derives phase1_surface_rules path (ENonterminal "generic_requirement")
      input rest
      (PTNonterminal "generic_requirement"
        (PTAlternative 6
          (PTSequence
            [ PTLiteral "effects";
              name_tree;
              PTLiteral "within";
              phase1_surface_effect_set_expression_fallback_base_choice_spine_tree
                effects;
              PTLiteral ";"
            ]))) ->
    exists fuel refined,
      phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel
        fuel name_tree effects = Some refined.
Proof.
  intros name_tree effects path input rest Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_requirement"
      input rest
      (PTNonterminal "generic_requirement"
        (PTAlternative 6
          (PTSequence
            [ PTLiteral "effects";
              name_tree;
              PTLiteral "within";
              phase1_surface_effect_set_expression_fallback_base_choice_spine_tree
                effects;
              PTLiteral ";"
            ])))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_requirement_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "generic_requirement"))
      phase1_surface_generic_requirement_items_for_totality
      input rest
      (PTAlternative 6
        (PTSequence
          [ PTLiteral "effects";
            name_tree;
            PTLiteral "within";
            phase1_surface_effect_set_expression_fallback_base_choice_spine_tree
              effects;
            PTLiteral ";"
          ]))
      Hbody)
    as [index [item [selected [Hnth [Hbranch Hselected]]]]].
  inversion Hbranch; subst index selected.
  cbn in Hnth.
  inversion Hnth; subst item.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      _
      [ ELiteral "effects";
        ENonterminal "identifier";
        ELiteral "within";
        ENonterminal "effect_set_expression";
        ELiteral ";"
      ]
      _ _
      (PTSequence
        [ PTLiteral "effects";
          name_tree;
          PTLiteral "within";
          phase1_surface_effect_set_expression_fallback_base_choice_spine_tree
            effects;
          PTLiteral ";"
        ])
      Hselected)
    as [trees [Hselected_tree Hitems]].
  inversion Hselected_tree; subst trees.
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Heffects : Derives phase1_surface_rules _
      (ENonterminal "effect_set_expression")
      _ _
      (phase1_surface_effect_set_expression_fallback_base_choice_spine_tree
        effects)
      |- _ =>
      destruct
        (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
          effects _ _ _ Heffects)
        as [fuel [refined_effects Hrefined_effects]];
      exists fuel,
        {| phase1_generic_effects_requirement_shift_refined_name_tree :=
             name_tree;
           phase1_generic_effects_requirement_shift_refined_effects :=
             refined_effects |};
      cbn;
      rewrite Hrefined_effects;
      reflexivity
  end.
Qed.

Theorem
  phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel_total_and_round_trip_from_derivation :
  forall name_tree effects path input rest,
    Derives phase1_surface_rules path (ENonterminal "generic_requirement")
      input rest
      (PTNonterminal "generic_requirement"
        (PTAlternative 6
          (PTSequence
            [ PTLiteral "effects";
              name_tree;
              PTLiteral "within";
              phase1_surface_effect_set_expression_fallback_base_choice_spine_tree
                effects;
              PTLiteral ";"
            ]))) ->
    exists fuel refined,
      phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel
        fuel name_tree effects = Some refined /\
      phase1_surface_generic_effects_requirement_shift_refined_spine_tree
        refined =
      PTNonterminal "generic_requirement"
        (PTAlternative 6
          (PTSequence
            [ PTLiteral "effects";
              name_tree;
              PTLiteral "within";
              phase1_surface_effect_set_expression_fallback_base_choice_spine_tree
                effects;
              PTLiteral ";"
            ])).
Proof.
  intros name_tree effects path input rest Hderive.
  destruct
    (phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel_total_from_derivation
      name_tree effects path input rest Hderive)
    as [fuel [refined Hnormalize]].
  exists fuel, refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel_round_trip.
    exact Hnormalize.
Qed.
