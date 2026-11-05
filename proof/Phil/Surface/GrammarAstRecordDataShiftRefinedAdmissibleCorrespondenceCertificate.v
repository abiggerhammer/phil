From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleTreeUnique
  GrammarAstRecordDataShiftRefinedAdmissibleParseCorrespondence.

Import ListNotations.

(*
  Package the caller-facing admissible record/data correspondence around the
  canonical reference parse tree.

  #1532 proves that every admissible token stream has exactly one reference
  parse tree carrying Phase1CompleteDerivation. #1535 proves that any such
  observed tree has exactly one corresponding implementation reconstructing
  that tree. This slice composes those two results so callers starting only
  from token-level admissibility can recover the canonical tree and its unique
  implementation correspondence without first supplying a parse-result
  witness.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1535.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_correspondence_certificate_exists_unique :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    exists! tree,
      phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
      Phase1CompleteDerivation tokens tree /\
      exists! implementation :
        Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
        phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
          tokens implementation /\
        phase1_surface_shift_refined_record_data_implementation_source_tree
          implementation = Some tree.
Proof.
  intros tokens Hadmissible.
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_tree_certificate_exists_unique
      tokens Hadmissible)
    as [tree [[Hparse Hcomplete] Htree_unique]].
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_parse_correspondence_exists_unique
      tokens tree Hadmissible Hparse)
    as [implementation
          [[Hcorresponds [Hsource Hcomplete']]
           Himplementation_unique]].
  exists tree.
  - split.
    + exact Hparse.
    + split.
      * exact Hcomplete.
      * exists implementation.
        -- split.
           ++ exact Hcorresponds.
           ++ exact Hsource.
        -- intros implementation' [Hcorresponds' Hsource'].
           apply Himplementation_unique.
           split.
           ++ exact Hcorresponds'.
           ++ split.
              ** exact Hsource'.
              ** exact Hcomplete.
  - intros tree' [Hparse' [Hcomplete' Himplementation_exists']].
    apply Htree_unique.
    split.
    + exact Hparse'.
    + exact Hcomplete'.
Qed.
