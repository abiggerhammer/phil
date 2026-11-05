From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceSpine
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the completed refined shift-expression term_arguments carrier through
  effect_expression.

  The already-refined static-reference spine remains unchanged. A present
  term_arguments value advances from the fallback/base-choice carrier to the
  fuel-indexed refined shift carrier, using one explicit fuel value for the
  whole optional-arguments payload.

  Structural Rocq surface correspondence only. This continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Definition
  phase1_surface_optional_term_arguments_expression_fallback_base_choice_shift_refined_tree
  (arguments :
    option Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  match arguments with
  | None => PTOptionalNone
  | Some arguments_value =>
      PTOptionalSome
        (phase1_surface_term_arguments_expression_fallback_base_choice_shift_refined_spine_tree
          arguments_value)
  end.

Definition
  phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel
  (fuel : nat)
  (arguments : option Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceSpine)
  : option
      (option
        Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine) :=
  match arguments with
  | None => Some None
  | Some arguments_value =>
      match
        phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel
          fuel arguments_value
      with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel_round_trip :
  forall fuel arguments refined,
    phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel
      fuel arguments = Some refined ->
    phase1_surface_optional_term_arguments_expression_fallback_base_choice_shift_refined_tree
      refined =
    phase1_surface_optional_term_arguments_expression_fallback_base_choice_tree
      arguments.
Proof.
  intros fuel [arguments_value |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel arguments_value)
      as [actual |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip
        fuel arguments_value actual Harguments).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Record
  Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine
  : Type := {
  phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference :
    Phase1SurfaceStaticReferenceSpine;
  phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_arguments :
    option
      Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine
}.

Definition
  phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
  (effect :
    Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  PTNonterminal "effect_expression"
    (PTSequence
      [ phase1_surface_static_reference_spine_tree
          (phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference
            effect);
        phase1_surface_optional_term_arguments_expression_fallback_base_choice_shift_refined_tree
          (phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_arguments
            effect)
      ]).

Definition
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel
  (fuel : nat)
  (effect : Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceSpine)
  : option
      Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel
      fuel
      (phase1_effect_expression_expression_fallback_base_choice_spine_arguments
        effect)
  with
  | Some arguments =>
      Some
        {| phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference :=
             phase1_effect_expression_expression_fallback_base_choice_spine_reference
               effect;
           phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_arguments :=
             arguments |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip :
  forall fuel effect refined,
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel effect = Some refined ->
    phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
    phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
      effect.
Proof.
  intros fuel [reference arguments] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel
      fuel arguments)
    as [actual |] eqn:Harguments; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel_round_trip
      fuel arguments actual Harguments).
  reflexivity.
Qed.

Definition
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option
      Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree
      tree
  with
  | Some effect =>
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel effect
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
      refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree
      tree)
    as [effect |] eqn:Heffect; try discriminate Hnormalize.
  transitivity
    (phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
      effect).
  - eapply
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree_round_trip.
    exact Heffect.
Qed.
