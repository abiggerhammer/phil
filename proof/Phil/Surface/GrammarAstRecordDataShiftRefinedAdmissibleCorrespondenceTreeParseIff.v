From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleCorrespondenceTreeIff
  GrammarAstRecordDataShiftRefinedAdmissibleParseComplete.

Import ListNotations.

(*
  Erase the proof-only complete-derivation conjunct from the caller-facing
  admissible correspondence/tree equivalence.

  #1539 shows that, for an admissible shift-refined record/data token stream
  and a caller-held implementation correspondence, the implementation's
  projected source tree is a candidate tree iff the certified reference parser
  returns that tree and it carries Phase1CompleteDerivation. #1533 already
  proves that any successful admissible reference parse carries that complete
  derivation. This slice composes the two results into the runtime-shaped
  equivalence proof clients usually need: projected implementation tree iff
  observed successful reference parse.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence/completeness beyond the existing
  shift-refined record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1540.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_correspondence_tree_parse_iff :
  forall tokens implementation tree,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
      tokens implementation ->
    (phase1_surface_shift_refined_record_data_implementation_source_tree
       implementation = Some tree <->
     phase1_surface_reference_parse tokens = Some ([], ResultTree tree)).
Proof.
  intros tokens implementation tree Hadmissible Hcorresponds.
  split.
  - intro Htree.
    pose proof
      (proj1
        (phase1_surface_reference_shift_refined_record_data_admissible_correspondence_tree_iff_certificate
          tokens implementation tree Hadmissible Hcorresponds)
        Htree)
      as [Hparse Hcomplete].
    exact Hparse.
  - intro Hparse.
    apply
      (proj2
        (phase1_surface_reference_shift_refined_record_data_admissible_correspondence_tree_iff_certificate
          tokens implementation tree Hadmissible Hcorresponds)).
    split.
    + exact Hparse.
    + exact
        (phase1_surface_reference_shift_refined_record_data_admissible_parse_complete
          tokens tree Hadmissible Hparse).
Qed.
