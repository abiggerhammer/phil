From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleCorrespondenceCertificate.

Import ListNotations.

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_implementation_correspondence_exists_unique :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    exists! implementation :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation.
Proof.
  intros tokens Hadmissible.
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_correspondence_certificate_exists_unique
      tokens Hadmissible)
    as [tree [[Hparse [Hcomplete Himplementation]] Htree_unique]].
  destruct Himplementation
    as [implementation [[Hcorresponds Hsource] Himplementation_unique]].
  exists implementation.
  - exact Hcorresponds.
  - intros implementation' Hcorresponds'.
    eapply
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique.
    + exact Hcorresponds.
    + exact Hcorresponds'.
Qed.
