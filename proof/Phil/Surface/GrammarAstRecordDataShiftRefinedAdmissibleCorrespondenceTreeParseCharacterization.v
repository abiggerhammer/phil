From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleImplementationCorrespondence
  GrammarAstRecordDataShiftRefinedAdmissibleCorrespondenceTreeParseIff.

Import ListNotations.

(*
  Package the unique admissible implementation correspondence together with
  the runtime-shaped reference-parse characterization of its projected tree.

  #1537 proves exactly one corresponding implementation from token-level
  admissibility. #1541 erases the proof-only complete-derivation conjunct from
  the per-tree correspondence theorem, showing that any caller-held
  correspondence projects to a candidate tree iff the certified reference
  parser returns that same ResultTree. This slice composes those facts so
  callers starting only from admissibility obtain the unique implementation
  together with the direct parse/result equivalence they can use at the
  surface boundary.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1541.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_correspondence_tree_parse_characterization_exists_unique :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    exists! implementation :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation /\
      forall tree,
        (phase1_surface_shift_refined_record_data_implementation_source_tree
           implementation = Some tree <->
         phase1_surface_reference_parse tokens = Some ([], ResultTree tree)).
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
        phase1_surface_reference_shift_refined_record_data_admissible_correspondence_tree_parse_iff.
      * exact Hadmissible.
      * exact Hcorresponds.
  - intros implementation' [Hcorresponds' Htree_characterization].
    apply Himplementation_unique.
    exact Hcorresponds'.
Qed.
