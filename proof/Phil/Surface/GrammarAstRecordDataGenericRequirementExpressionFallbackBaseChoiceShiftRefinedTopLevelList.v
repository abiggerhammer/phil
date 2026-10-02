From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelSpine.

Import ListNotations.

Fixpoint
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel
  (fuel : nat)
  (top_levels : list Phase1SurfaceTopLevelSpine)
  : option
      (list
        Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelSpine) :=
  match top_levels with
  | [] => Some []
  | top_level :: rest =>
      match
        phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel
          fuel top_level,
        phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel
          fuel rest
      with
      | Some refined, Some refined_rest =>
          Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel_round_trip :
  forall fuel top_levels refined,
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel
      fuel top_levels = Some refined ->
    map
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_tree
      refined =
    map phase1_surface_top_level_spine_tree top_levels.
Proof.
  intros fuel top_levels.
  induction top_levels as [|top_level top_levels IH];
    intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel
        fuel top_level)
      as [refined_top_level |] eqn:Htop_level;
      try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel
        fuel top_levels)
      as [refined_rest |] eqn:Hrest;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel_round_trip.
      exact Htop_level.
    + eapply IH.
      exact Hrest.
Qed.

Lemma
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel_monotone :
  forall fuel larger top_levels refined,
    fuel <= larger ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel
      fuel top_levels = Some refined ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel
      larger top_levels = Some refined.
Proof.
  intros fuel larger top_levels.
  induction top_levels as [|top_level top_levels IH];
    intros refined Hle Hnormalize.
  - cbn in Hnormalize |- *.
    exact Hnormalize.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel
        fuel top_level)
      as [refined_top_level |] eqn:Htop_level;
      try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel
        fuel top_levels)
      as [refined_rest |] eqn:Hrest;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel_monotone
        fuel larger top_level refined_top_level Hle Htop_level).
    rewrite (IH refined_rest Hle Hrest).
    reflexivity.
Qed.
