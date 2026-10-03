From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceImplementationAdmissibilityWitnessErasedCertificate.

Definition
  phase1_surface_reference_shift_refined_record_data_admissible
  (tokens : list ConcreteToken)
  : Prop :=
  match phase1_surface_reference_source_top_level tokens with
  | Some source =>
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable source
  | None => False
  end.
