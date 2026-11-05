From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleImplementationCorrespondence
  GrammarAstRecordDataShiftRefinedAdmissibleCorrespondenceTreeIff.

Import ListNotations.

(*
  Package the unique admissible implementation correspondence together with
  its canonical reference-tree characterization.

  #1537 proves exactly one corresponding implementation from token-level
  admissibility. #1539 proves that, for any caller-held correspondence, the
  implementation's projected source tree is a candidate tree iff the
  certified reference parser returns that same tree with a complete
  derivation. This slice composes those caller-facing facts so users starting
  only from admissibility obtain one implementation carrying the full
  bidirectional tree characterization.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence/completeness beyond the existing
  shift-refined record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1539.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_correspondence_tree_characterization_exists_unique :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    exists! implementation :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation /\
      forall tree,
        (phase1_surface_shift_refined_record_data_implementation_source_tree
           implementation = Some tree <->
         phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
         Phase1CompleteDerivation tokens tree).
Proof.
  intros tokens Hadmissible.
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_implementation_correspondence_exists_unique
      tokens Hadmissible)
    as [implementation [Hcorresponds Himplementation_unique]].
  exists implementation.
  - split.
    + exact Hcorresponds.
    + intro tree.
      apply
        phase1_surface_reference_shift_refined_record_data_admissible_correspondence_tree_iff_certificate.
      * exact Hadmissible.
      * exact Hcorresponds.
  - intros implementation' [Hcorresponds' Htree_characterization].
    apply Himplementation_unique.
    exact Hcorresponds'.
Qed.
