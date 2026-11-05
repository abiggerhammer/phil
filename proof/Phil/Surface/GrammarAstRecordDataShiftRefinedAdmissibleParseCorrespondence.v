From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleParseImplementation.

Import ListNotations.

(*
  Expose the underlying fuel-erased implementation correspondence behind an
  observed successful reference parse of an admissible shift-refined
  record/data token stream.

  #1534 recovers the unique certified implementation whose reconstructed source
  tree is exactly the ResultTree already held by the caller. This slice projects
  that packaged certificate back to the intrinsic correspondence relation while
  retaining the observed-tree reconstruction and complete-derivation evidence
  in one exactly-one result.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1534.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_parse_correspondence_exists_unique :
  forall tokens tree,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    phase1_surface_reference_parse tokens = Some ([], ResultTree tree) ->
    exists! implementation :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation /\
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation = Some tree /\
      Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens tree Hadmissible Hparse.
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_parse_implementation_exists_unique
      tokens tree Hadmissible Hparse)
    as [implementation [[Hcertified Hsource] Himplementation_unique]].
  assert (Hcomplete : Phase1CompleteDerivation tokens tree).
  {
    apply
      (phase1_surface_reference_shift_refined_record_data_admissible_parse_complete
        tokens tree Hadmissible Hparse).
  }
  exists implementation.
  - split.
    + apply
        (proj1
          (phase1_surface_reference_shift_refined_record_data_implementation_certified_iff_corresponds
            tokens implementation)).
      exact Hcertified.
    + split.
      * exact Hsource.
      * exact Hcomplete.
  - intros implementation' [Hcorresponds' [Hsource' Hcomplete']].
    apply Himplementation_unique.
    split.
    + apply
        (proj2
          (phase1_surface_reference_shift_refined_record_data_implementation_certified_iff_corresponds
            tokens implementation')).
      exact Hcorresponds'.
    + exact Hsource'.
Qed.
