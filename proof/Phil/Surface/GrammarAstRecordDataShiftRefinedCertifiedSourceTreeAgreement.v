From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedCertified.

(*
  Erase the explicit ParseTree witnesses from #1548 and #1549 and expose the
  projection-level agreement already forced by certified implementation
  uniqueness.

  Any two certified shift-refined record/data implementations for the same
  tokens are equal. Their deterministic implementation-source projections
  therefore agree directly, so callers comparing certified implementations do
  not need to unpack a tree witness merely to establish source-tree equality.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, prove a new existence result, or extend correspondence beyond
  the existing shift-refined record/data carrier. Continues
  PHIL-SURFACE-GRAMMAR-CORR-001 after #1549.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_agreement :
  forall tokens implementation1 implementation2,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation1 ->
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation2 ->
    phase1_surface_shift_refined_record_data_implementation_source_tree
      implementation1 =
    phase1_surface_shift_refined_record_data_implementation_source_tree
      implementation2.
Proof.
  intros tokens implementation1 implementation2 Hcertified1 Hcertified2.
  assert (Himplementation : implementation1 = implementation2).
  {
    eapply
      phase1_surface_reference_shift_refined_record_data_implementation_certified_unique.
    - exact Hcertified1.
    - exact Hcertified2.
  }
  subst implementation2.
  reflexivity.
Qed.
