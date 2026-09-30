From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstExpressionFallbackBaseChoiceShiftSpineTotality
  GrammarAstBaseExpressionChoiceTotality
  GrammarAstBaseExpressionShiftRefinedSpineTotality
  GrammarAstShiftExpressionRefinedSpineTotality.

Import ListNotations.
Open Scope string_scope.

Lemma
  phase1_surface_normalize_base_expression_shift_refined_spine_fuel_total_from_spine_derivation :
  forall expression path input rest,
    Derives phase1_surface_rules path (ENonterminal "base_expression")
      input rest
      (phase1_surface_base_expression_shift_spine_tree expression) ->
    exists fuel refined,
      phase1_surface_normalize_base_expression_shift_refined_spine_fuel
        fuel expression = Some refined.
Proof.
  intros expression path input rest Hderive.
  destruct expression as [command | shift].
  - exists 0, (Phase1BaseExpressionShiftRefinedCommand command).
    reflexivity.
  - destruct
      (derives_nonterminal_exposes_body
        phase1_surface_rules path "base_expression"
        input rest
        (phase1_surface_base_expression_shift_spine_tree
          (Phase1BaseExpressionShiftSpineShift shift))
        Hderive)
      as [body [subtree [Hlookup [Htree Hbody]]]].
    rewrite phase1_surface_base_expression_lookup_for_totality in Hlookup.
    inversion Hlookup; subst body.
    destruct
      (alternative_derivation_names_exact_branch
        phase1_surface_rules
        (descend path (AtNonterminal "base_expression"))
        phase1_surface_base_expression_items_for_totality
        input rest subtree Hbody)
      as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
    cbn in Htree.
    inversion Htree; subst subtree.
    inversion Hsubtree; subst index selected.
    cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_shift_expression_refined_tree_fuel_total_from_derivation
        _ _ _ _ Hselected)
      as [fuel [refined_shift [Hrefined_shift Hround_trip]]].
    exists fuel, (Phase1BaseExpressionShiftRefinedShift refined_shift).
    cbn.
    rewrite Hrefined_shift.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation :
  forall expression path input rest,
    Derives phase1_surface_rules path (ENonterminal "expression")
      input rest
      (phase1_surface_expression_fallback_base_choice_shift_spine_tree
        expression) ->
    exists fuel refined,
      phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel expression = Some refined.
Proof.
  intros [base fallback] path input rest Hderive.
  unfold phase1_surface_expression_fallback_base_choice_shift_spine_tree
    in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "expression"
      input rest
      (PTNonterminal "expression"
        (PTSequence
          [ phase1_surface_base_expression_shift_spine_tree base;
            phase1_surface_optional_expression_fallback_base_choice_tree
              fallback
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "expression"))
      [ ENonterminal "base_expression";
        EOptional
          (ESequence
            [ ELiteral "or";
              ENonterminal "fallback"
            ])
      ]
      input rest
      (PTSequence
        [ phase1_surface_base_expression_shift_spine_tree base;
          phase1_surface_optional_expression_fallback_base_choice_tree fallback
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
  | Hbase : Derives phase1_surface_rules _
      (ENonterminal "base_expression") _ _
      (phase1_surface_base_expression_shift_spine_tree base) |- _ =>
      destruct
        (phase1_surface_normalize_base_expression_shift_refined_spine_fuel_total_from_spine_derivation
          base _ _ _ Hbase)
        as [fuel [refined_base Hrefined_base]];
      exists fuel,
        {| phase1_expression_fallback_base_choice_shift_refined_spine_base :=
             refined_base;
           phase1_expression_fallback_base_choice_shift_refined_spine_fallback :=
             fallback |};
      cbn;
      rewrite Hrefined_base;
      reflexivity
  end.
Qed.

Theorem
  phase1_surface_normalize_expression_fallback_base_choice_shift_refined_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "expression")
      input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_expression_fallback_base_choice_shift_refined_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_expression_fallback_base_choice_shift_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
      base path input rest Hcanonical)
    as [fuel [refined Hrefined]].
  assert (Hnormalize :
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined).
  {
    unfold
      phase1_surface_normalize_expression_fallback_base_choice_shift_refined_tree_fuel.
    rewrite Hbase.
    exact Hrefined.
  }
  exists fuel, refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip.
    exact Hnormalize.
Qed.
