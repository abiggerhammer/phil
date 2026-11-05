From Stdlib Require Import Arith.PeanoNat.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedFuelSupport.

(*
  Shared-fuel monotonicity for the record_decl and data_decl lifts of the
  shift-refined generic_requirements carrier introduced in #1495.

  A successful declaration normalization at some fuel remains successful at
  every larger fuel. The only fuel-sensitive declaration field is the optional
  generic_requirements carrier, so the proof threads its established
  monotonicity through all unchanged declaration fields and then through the
  corresponding whole-tree normalizers.

  Structural Rocq surface correspondence only. This does not yet prove
  declaration-level derivation-driven fuel totality, change Grammar-v1,
  Haskell/runtime behavior, evaluation semantics, or make broader parser
  soundness/completeness claims. It continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1495.
*)

Lemma
  phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_monotone :
  forall fuel larger record refined,
    fuel <= larger ->
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel record = Some refined ->
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
      larger record = Some refined.
Proof.
  intros fuel larger
    [name generic_params mode requirements fields]
    refined Hle Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel
      fuel requirements)
    as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel_monotone
      fuel larger requirements actual Hle Hrequirements).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree
      tree)
    as [record |] eqn:Hrecord; try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_monotone :
  forall fuel larger data_value refined,
    fuel <= larger ->
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel data_value = Some refined ->
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
      larger data_value = Some refined.
Proof.
  intros fuel larger
    [name generic_params mode requirements first_variant rest_variants]
    refined Hle Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel
      fuel requirements)
    as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel_monotone
      fuel larger requirements actual Hle Hrequirements).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_monotone :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree
      tree)
    as [data_value |] eqn:Hdata; try discriminate Hnormalize.
  eapply
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.
