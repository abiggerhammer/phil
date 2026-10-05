From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleCorrespondenceTreeParseCharacterization
  GrammarAstRecordDataShiftRefinedAdmissibleCorrespondenceCanonicalTree.

Import ListNotations.

(*
  Repackage the admissible correspondence/parse characterization as concrete
  unique witnesses for callers that want to destruct evidence rather than use
  the higher-order per-tree iff directly.

  #1542 proves that token-level admissibility yields exactly one corresponding
  implementation and characterizes every projected source tree by equality
  with the certified reference parser's ResultTree. This slice exposes the
  constructive witness form: that unique implementation comes with exactly one
  tree that is both its projected source tree and the observed successful
  reference parse.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1542.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_correspondence_parse_witness_exists_unique :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    exists! implementation :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation /\
      exists! tree,
        phase1_surface_shift_refined_record_data_implementation_source_tree
          implementation = Some tree /\
        phase1_surface_reference_parse tokens = Some ([], ResultTree tree).
Proof.
  intros tokens Hadmissible.
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_correspondence_tree_parse_characterization_exists_unique
      tokens Hadmissible)
    as [implementation [[Hcorresponds Htree_iff] Himplementation_unique]].
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_correspondence_canonical_tree_certificate
      tokens implementation Hadmissible Hcorresponds)
    as [tree [Hsource [Hparse [Hcomplete Htree_unique]]]].
  exists implementation.
  - split.
    + exact Hcorresponds.
    + exists tree.
      * split.
        -- exact Hsource.
        -- exact Hparse.
      * intros tree' [Hsource' Hparse'].
        rewrite Hsource in Hsource'.
        inversion Hsource'.
        reflexivity.
  - intros implementation' [Hcorresponds' Htree_exists_unique].
    apply Himplementation_unique.
    split.
    + exact Hcorresponds'.
    + intro tree'.
      apply
        phase1_surface_reference_shift_refined_record_data_admissible_correspondence_tree_parse_iff.
      * exact Hadmissible.
      * exact Hcorresponds'.
Qed.
