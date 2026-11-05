From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine.

Open Scope string_scope.

(*
  Refine the payload of the generic "effects ... within ...;" requirement with
  the completed shift-refined effect_set_expression carrier.

  Structural Rocq surface correspondence only; continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Record Phase1SurfaceGenericEffectsRequirementShiftRefinedSpine : Type := {
  phase1_generic_effects_requirement_shift_refined_name_tree : ParseTree;
  phase1_generic_effects_requirement_shift_refined_effects :
    Phase1SurfaceEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine
}.

Definition phase1_surface_generic_effects_requirement_shift_refined_spine_tree
  (requirement : Phase1SurfaceGenericEffectsRequirementShiftRefinedSpine)
  : ParseTree :=
  PTNonterminal "generic_requirement"
    (PTAlternative 6
      (PTSequence
        [ PTLiteral "effects";
          phase1_generic_effects_requirement_shift_refined_name_tree requirement;
          PTLiteral "within";
          phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_spine_tree
            (phase1_generic_effects_requirement_shift_refined_effects requirement);
          PTLiteral ";"
        ])).

Definition phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel
  (fuel : nat)
  (name_tree : ParseTree)
  (effects : Phase1SurfaceEffectSetExpressionFallbackBaseChoiceSpine)
  : option Phase1SurfaceGenericEffectsRequirementShiftRefinedSpine :=
  match
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel effects
  with
  | Some refined =>
      Some
        {| phase1_generic_effects_requirement_shift_refined_name_tree :=
             name_tree;
           phase1_generic_effects_requirement_shift_refined_effects :=
             refined |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel_round_trip :
  forall fuel name_tree effects refined,
    phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel
      fuel name_tree effects = Some refined ->
    phase1_surface_generic_effects_requirement_shift_refined_spine_tree refined =
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
  intros fuel name_tree effects refined Hnormalize.
  unfold
    phase1_surface_normalize_generic_effects_requirement_shift_refined_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel effects)
    as [actual |] eqn:Heffects; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip
      fuel effects actual Heffects).
  reflexivity.
Qed.
