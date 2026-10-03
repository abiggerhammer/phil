From Stdlib Require Import Lists.List.
From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceImplementationAdmissibleCertificate.
Import ListNotations.

Definition
  phase1_surface_reference_shift_refined_record_data_implementation_certified
  (tokens : list ConcreteToken)
  (implementation :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource)
  : Prop :=
  phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
    tokens implementation /\
  match
    phase1_surface_shift_refined_record_data_implementation_source_tree implementation
  with
  | Some tree =>
      phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
      Phase1CompleteDerivation tokens tree
  | None => False
  end.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_certified :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    exists! implementation :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      phase1_surface_reference_shift_refined_record_data_implementation_certified
        tokens implementation.
Proof.
  intros tokens Hadmissible.
  unfold phase1_surface_reference_shift_refined_record_data_implementation_certified.
  apply
    phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_admissible_certificate.
  exact Hadmissible.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_unique :
  forall tokens implementation1 implementation2,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation1 ->
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation2 ->
    implementation1 = implementation2.
Proof.
  intros tokens implementation1 implementation2
    [Hcorresponds1 Hcertificate1]
    [Hcorresponds2 Hcertificate2].
  eapply
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique.
  - exact Hcorresponds1.
  - exact Hcorresponds2.
Qed.
