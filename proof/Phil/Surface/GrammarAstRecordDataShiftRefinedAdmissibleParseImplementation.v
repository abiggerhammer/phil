From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleParseComplete
  GrammarAstRecordDataShiftRefinedCertified.

Import ListNotations.

(*
  Recover the unique certified implementation behind an observed successful
  reference parse of an admissible shift-refined record/data token stream.

  #1533 projects Phase1CompleteDerivation directly onto the ResultTree a caller
  already holds. This slice closes the adjacent caller-facing seam: that same
  observed tree is the source tree of exactly one certified implementation.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1533.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_parse_implementation_exists_unique :
  forall tokens tree,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    phase1_surface_reference_parse tokens = Some ([], ResultTree tree) ->
    exists! implementation :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      phase1_surface_reference_shift_refined_record_data_implementation_certified
        tokens implementation /\
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation = Some tree.
Proof.
  intros tokens tree Hadmissible Hparse.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_certified
      tokens Hadmissible)
    as [implementation [Hcertified Himplementation_unique]].
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_certified_tree_certificate
      tokens implementation Hcertified)
    as [canonical [Hsource [Hcanonical_parse Hcomplete]]].
  rewrite Hcanonical_parse in Hparse.
  inversion Hparse.
  subst tree.
  exists implementation.
  - split.
    + exact Hcertified.
    + exact Hsource.
  - intros implementation' [Hcertified' Hsource'].
    apply Himplementation_unique.
    exact Hcertified'.
Qed.
