From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedCertifiedSourceTreeParseIff
  GrammarAstRecordDataShiftRefinedCertifiedParseComplete.

(*
  Project complete-derivation evidence directly from a certified
  implementation-source tree after #1554.

  For an already-certified shift-refined record/data implementation, the
  source-tree/reference-parser equivalence turns the observed implementation
  projection into the corresponding certified reference parse. The existing
  certified parse-completeness theorem then transports
  Phase1CompleteDerivation to that projected tree.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, prove a new certified implementation existence result, or
  extend correspondence/completeness beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1554.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_complete :
  forall tokens implementation tree,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation ->
    phase1_surface_shift_refined_record_data_implementation_source_tree
      implementation = Some tree ->
    Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens implementation tree Hcertified Hsource.
  eapply
    phase1_surface_reference_shift_refined_record_data_implementation_certified_parse_complete.
  - exact Hcertified.
  - apply
      (proj1
        (phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_parse_iff
          tokens implementation Hcertified tree)).
    exact Hsource.
Qed.
