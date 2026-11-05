From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedFuelSupport
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceShiftRefinedTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Shared-fuel totality support for refined effect-set member lists.

  This first helper handles comma-prefixed repetition tails. Each derivable
  effect_expression gets its existing finite-fuel witness; Nat.max plus the
  established monotonicity lemmas lifts the head and tail to one shared bound.

  Structural Rocq surface correspondence only. Continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel_total_from_suffix_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body =
      ESequence [ELiteral ","; ENonterminal "effect_expression"] ->
    forall effects,
      trees =
        map
          phase1_surface_effect_expression_expression_fallback_base_choice_suffix_tree
          effects ->
      exists fuel refined,
        phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
          fuel effects = Some refined.
Proof.
  intros path body input rest trees Hderive Hbody_shape.
  subst body.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros effects Htrees.
  - destruct effects as [|effect effects]; cbn in Htrees.
    + exists 0, [].
      reflexivity.
    + discriminate Htrees.
  - destruct effects as [|effect effects]; cbn in Htrees;
      try discriminate Htrees.
    inversion Htrees; subst tree trees.
    unfold
      phase1_surface_effect_expression_expression_fallback_base_choice_suffix_tree
      in Hitem.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend path AtRepetitionBody)
        [ ELiteral ",";
          ENonterminal "effect_expression"
        ]
        input middle
        (PTSequence
          [ PTLiteral ",";
            phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
              effect
          ])
        Hitem)
      as [item_trees [Hitem_tree Hitem_items]].
    inversion Hitem_tree; subst item_trees.
    repeat match goal with
    | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
        inversion Hseq; subst; clear Hseq
    end.
    match goal with
    | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
        inversion Hnil; subst; clear Hnil
    end.
    match goal with
    | Heffect : Derives phase1_surface_rules _
        (ENonterminal "effect_expression")
        _ _
        (phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
          effect) |- _ =>
        destruct
          (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
            effect _ _ _ Heffect)
          as [effect_fuel [refined_effect Hrefined_effect]];
        destruct (IHrest effects eq_refl)
          as [rest_fuel [refined_rest Hrefined_rest]];
        exists
          (Nat.max effect_fuel rest_fuel),
          (refined_effect :: refined_rest);
        cbn;
        rewrite
          (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_monotone
            effect_fuel
            (Nat.max effect_fuel rest_fuel)
            effect
            refined_effect
            (Nat.le_max_l effect_fuel rest_fuel)
            Hrefined_effect);
        rewrite
          (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel_monotone
            rest_fuel
            (Nat.max effect_fuel rest_fuel)
            effects
            refined_rest
            (Nat.le_max_r effect_fuel rest_fuel)
            Hrefined_rest);
        reflexivity
    end.
Qed.
