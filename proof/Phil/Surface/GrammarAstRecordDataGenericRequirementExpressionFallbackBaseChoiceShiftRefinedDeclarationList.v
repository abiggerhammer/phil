From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclarationFuelSupport.

Import ListNotations.

(*
  Lift the shift-refined record/data declaration-spine normalizer across a
  finite list while threading one shared explicit fuel value.

  Successful normalization preserves the exact selected ParseTree list, and
  any successful list normalization remains stable when fuel increases.

  Structural Rocq surface correspondence only. This does not yet prove
  derivation-driven existence of a shared fuel for an arbitrary declaration
  list, lift attributes/top-level/source carriers, change Grammar-v1, or alter
  runtime/extraction behavior. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after
  #1502.
*)

Fixpoint
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel
  (fuel : nat)
  (declarations : list Phase1SurfaceDeclarationSpine)
  : option
      (list
        Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration) :=
  match declarations with
  | [] => Some []
  | declaration :: rest =>
      match
        phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
          fuel declaration,
        phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel
          fuel rest
      with
      | Some refined, Some refined_rest =>
          Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel_round_trip :
  forall fuel declarations refined,
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel
      fuel declarations = Some refined ->
    map
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_tree
      refined =
    map phase1_declaration_spine_selected_tree declarations.
Proof.
  intros fuel declarations.
  induction declarations as [|declaration declarations IH];
    intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
        fuel declaration)
      as [refined_declaration |] eqn:Hdeclaration;
      try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel
        fuel declarations)
      as [refined_rest |] eqn:Hrest;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_round_trip.
      exact Hdeclaration.
    + eapply IH.
      exact Hrest.
Qed.

Lemma
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel_monotone :
  forall fuel larger declarations refined,
    fuel <= larger ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel
      fuel declarations = Some refined ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel
      larger declarations = Some refined.
Proof.
  intros fuel larger declarations.
  induction declarations as [|declaration declarations IH];
    intros refined Hle Hnormalize.
  - cbn in Hnormalize |- *.
    exact Hnormalize.
  - cbn in Hnormalize |- *.
    destruct
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
        fuel declaration)
      as [refined_declaration |] eqn:Hdeclaration;
      try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel
        fuel declarations)
      as [refined_rest |] eqn:Hrest;
      try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    rewrite
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_monotone
        fuel larger declaration refined_declaration Hle Hdeclaration).
    rewrite (IH refined_rest Hle Hrest).
    reflexivity.
Qed.
