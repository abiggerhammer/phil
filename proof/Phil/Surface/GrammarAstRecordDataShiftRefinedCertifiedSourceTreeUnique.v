From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedCertified.

(*
  Erase the parser/derivation payload from the certified tree certificate after
  #1548 and expose exactly the projection fact needed by callers that already
  hold a certified implementation.

  Certification already guarantees that the implementation source projection
  is Some tree. The projection is a deterministic function, so that tree is
  unique without separately carrying the reference parser ResultTree or
  Phase1CompleteDerivation witnesses.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, prove existence of a certified implementation, or extend
  correspondence beyond the existing shift-refined record/data carrier.
  Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1548.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_exists_unique :
  forall tokens implementation,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation ->
    exists! tree,
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation = Some tree.
Proof.
  intros tokens implementation Hcertified.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_certified_tree_certificate
      tokens implementation Hcertified)
    as [tree [Hsource [Hparse Hcomplete]]].
  exists tree.
  - exact Hsource.
  - intros tree' Hsource'.
    rewrite Hsource in Hsource'.
    inversion Hsource'.
    reflexivity.
Qed.
