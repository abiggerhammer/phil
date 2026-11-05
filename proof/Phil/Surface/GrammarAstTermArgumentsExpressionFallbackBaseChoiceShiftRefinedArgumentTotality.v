From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstExpressionFallbackBaseChoiceShiftSpineTotality
  GrammarAstExpressionFallbackBaseChoiceShiftRefinedSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Per-argument totality support for the completed refined shift-expression
  lift through term_arguments.

  Structural Rocq surface-correspondence only.  This does not change Grammar-v1
  or evaluation semantics, touch Haskell/runtime code, or claim broader
  production-parser soundness/completeness.  It continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel_total_from_derivation :
  forall expression path input rest,
    Derives phase1_surface_rules path (ENonterminal "expression")
      input rest
      (phase1_surface_expression_fallback_base_choice_spine_tree expression) ->
    exists fuel refined,
      phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel
        fuel expression = Some refined.
Proof.
  intros expression path input rest Hderive.
  destruct
    (phase1_surface_normalize_expression_fallback_base_choice_shift_spine_total_from_spine_derivation
      expression path input rest Hderive)
    as [shifted Hshifted].
  pose proof Hderive as Hcanonical.
  rewrite <-
    (phase1_surface_normalize_expression_fallback_base_choice_shift_spine_round_trip
      expression shifted Hshifted)
    in Hcanonical.
  destruct
    (phase1_surface_normalize_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
      shifted path input rest Hcanonical)
    as [fuel [refined Hrefined]].
  exists fuel, refined.
  unfold
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_from_base_choice_spine_fuel.
  rewrite Hshifted.
  exact Hrefined.
Qed.
