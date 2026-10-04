From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleCorrespondenceCanonicalTree.

Import ListNotations.

(*
  Expose the canonical admissible reference tree behind a caller-held
  correspondence as a bidirectional tree certificate.

  #1538 proves that any corresponding implementation for an admissible
  shift-refined record/data token stream reconstructs one canonical reference
  parse tree, and that any other complete reference parse tree is equal to it.
  This slice packages the resulting transport law directly: a candidate tree
  is the implementation's projected source tree iff it is exactly the
  certified reference parse tree with a complete derivation.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence/completeness beyond the existing
  shift-refined record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1538.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_correspondence_tree_iff_certificate :
  forall tokens implementation tree,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
      tokens implementation ->
    (phase1_surface_shift_refined_record_data_implementation_source_tree
       implementation = Some tree <->
     phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
     Phase1CompleteDerivation tokens tree).
Proof.
  intros tokens implementation tree Hadmissible Hcorresponds.
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_correspondence_canonical_tree_certificate
      tokens implementation Hadmissible Hcorresponds)
    as
      [canonical
        [Himplementation_tree
          [Hparse
            [Hcomplete Hcanonical_unique]]]].
  split.
  - intro Htree.
    rewrite Himplementation_tree in Htree.
    inversion Htree; subst tree.
    split.
    + exact Hparse.
    + exact Hcomplete.
  - intros [Hparse' Hcomplete'].
    pose proof
      (Hcanonical_unique tree Hparse' Hcomplete')
      as Htree_canonical.
    subst tree.
    exact Himplementation_tree.
Qed.
