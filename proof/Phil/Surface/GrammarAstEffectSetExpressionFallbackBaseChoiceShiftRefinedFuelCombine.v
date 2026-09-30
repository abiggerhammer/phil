From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedFuelSupport.

Lemma
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_cons_fuel_total :
  forall effect rest effect_fuel refined_effect rest_fuel refined_rest,
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel
      effect_fuel effect = Some refined_effect ->
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
      rest_fuel rest = Some refined_rest ->
    exists fuel,
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel
        fuel (effect :: rest) =
      Some (refined_effect :: refined_rest).
Proof.
  intros effect rest effect_fuel refined_effect rest_fuel refined_rest
    Heffect Hrest.
  exists (Nat.max effect_fuel rest_fuel).
  cbn.
  rewrite
    (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_monotone
      effect_fuel
      (Nat.max effect_fuel rest_fuel)
      effect
      refined_effect
      (Nat.le_max_l effect_fuel rest_fuel)
      Heffect).
  rewrite
    (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_values_fuel_monotone
      rest_fuel
      (Nat.max effect_fuel rest_fuel)
      rest
      refined_rest
      (Nat.le_max_r effect_fuel rest_fuel)
      Hrest).
  reflexivity.
Qed.
