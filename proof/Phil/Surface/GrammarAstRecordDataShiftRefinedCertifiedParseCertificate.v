From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedCertifiedSourceTreeParseIff
  GrammarAstRecordDataShiftRefinedCertifiedParseComplete.

Import ListNotations.

(*
  Package the source projection and complete-derivation consequences of an
  observed certified reference parse after #1553.

  Once callers hold a certified shift-refined record/data implementation and
  observe a reference-parser ResultTree, #1551 identifies that tree with the
  implementation-source projection and #1553 transports the existing
  Phase1CompleteDerivation to it. This theorem exposes those two facts together
  as the minimal observed-parse certificate.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, prove a new certified implementation existence result, or
  extend correspondence/completeness beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1553.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_parse_certificate :
  forall tokens implementation tree,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation ->
    phase1_surface_reference_parse tokens = Some ([], ResultTree tree) ->
    phase1_surface_shift_refined_record_data_implementation_source_tree
      implementation = Some tree /\
    Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens implementation tree Hcertified Hparse.
  split.
  - apply
      (proj2
        (phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_parse_iff
          tokens implementation Hcertified tree)).
    exact Hparse.
  - eapply
      phase1_surface_reference_shift_refined_record_data_implementation_certified_parse_complete.
    + exact Hcertified.
    + exact Hparse.
Qed.
