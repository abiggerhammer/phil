From Stdlib Require Import Arith.PeanoNat.

From Phil.Surface Require Import
  GrammarAstGenericRequirementEffectsShiftRefinedSpine
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedFuelSupport.

(*
  Shared-fuel monotonicity for the shift-refined effect-set payload carried by
  generic_requirement alternative 6 ("effects ... within ...;").

  A successful generic-effects refinement remains successful when fuel is
  increased because the only fuel-sensitive component is the already-proved
  shift-refined effect_set_expression normalization.

  Structural Rocq surface correspondence only. This does not change Grammar-v1,
  Haskell/runtime behavior, evaluation semantics, or make broader parser
  soundness/completeness claims. It continues PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel_monotone :
  forall fuel larger name_tree effects refined,
    fuel <= larger ->
    phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel
      fuel name_tree effects = Some refined ->
    phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel
      larger name_tree effects = Some refined.
Proof.
  intros fuel larger name_tree effects refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel effects)
    as [actual |] eqn:Heffects; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel_monotone
      fuel larger effects actual Hle Heffects).
  reflexivity.
Qed.
