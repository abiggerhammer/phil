From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsExpressionFallbackBaseChoiceTotality
  GrammarAstGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedListFuelTotality.

Import ListNotations.
Open Scope string_scope.

Lemma
  phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation :
  forall requirements path input rest,
    Derives phase1_surface_rules path (ENonterminal "generic_requirements")
      input rest
      (phase1_surface_generic_requirements_expression_fallback_base_choice_spine_tree
        requirements) ->
    exists fuel refined,
      phase1_surface_normalize_generic_requirements_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel requirements = Some refined.
Proof.
  intros [entries] path input rest Hderive.
  unfold phase1_surface_generic_requirements_expression_fallback_base_choice_spine_tree
    in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_requirements"
      input rest
      (PTNonterminal "generic_requirements"
        (PTSequence
          [ PTLiteral "requires";
            PTLiteral "{";
            PTRepetition
              (map
                phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
                entries);
            PTLiteral "}"
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_requirements_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "generic_requirements"))
      [ ELiteral "requires";
        ELiteral "{";
        ERepetition (ENonterminal "generic_requirement");
        ELiteral "}"
      ]
      input rest
      (PTSequence
        [ PTLiteral "requires";
          PTLiteral "{";
          PTRepetition
            (map
              phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
              entries);
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
  | Hrepeat : Derives phase1_surface_rules _
      (ERepetition (ENonterminal "generic_requirement"))
      _ _
      (PTRepetition
        (map
          phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
          entries)) |- _ =>
      destruct
        (phase1_surface_repetition_derivation_exposes
          _
          (ENonterminal "generic_requirement")
          _ _
          (PTRepetition
            (map
              phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
              entries))
          Hrepeat)
        as [entry_trees [Hentry_tree Hentry_body]];
      inversion Hentry_tree; subst entry_trees;
      destruct
        (phase1_surface_normalize_generic_requirement_expression_fallback_base_choice_shift_refined_values_fuel_total_from_spine_repetition
          _
          (ENonterminal "generic_requirement")
          _ _
          (map
            phase1_surface_generic_requirement_expression_fallback_base_choice_spine_tree
            entries)
          Hentry_body eq_refl
          entries eq_refl)
        as [fuel [refined_entries Hrefined_entries]];
      exists fuel;
      exists
        {| phase1_generic_requirements_expression_fallback_base_choice_shift_refined_spine_entries :=
             refined_entries |};
      cbn;
      rewrite Hrefined_entries;
      reflexivity
  end.
Qed.
