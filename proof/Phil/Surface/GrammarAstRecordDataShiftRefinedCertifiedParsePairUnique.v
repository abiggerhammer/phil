From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedCertified.

Import ListNotations.

(*
  Strengthen #1547's certified parse-pair transport law by isolating uniqueness
  from the admissibility hypothesis used for existence.

  Certified implementations for fixed tokens are already unique. Once the
  implementations are equal, the deterministic implementation-source
  projection makes their paired ParseTrees equal as well. Callers that already
  hold certified implementations can therefore compare their pairs directly
  without first reconstructing token-level admissibility.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, prove a new existence result, or extend correspondence beyond
  the existing shift-refined record/data carrier. Continues
  PHIL-SURFACE-GRAMMAR-CORR-001 after #1547.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_certified_parse_pair_unique :
  forall tokens implementation1 tree1 implementation2 tree2,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation1 ->
    phase1_surface_shift_refined_record_data_implementation_source_tree
      implementation1 = Some tree1 ->
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation2 ->
    phase1_surface_shift_refined_record_data_implementation_source_tree
      implementation2 = Some tree2 ->
    (implementation1, tree1) = (implementation2, tree2).
Proof.
  intros
    tokens
    implementation1 tree1
    implementation2 tree2
    Hcertified1 Hsource1
    Hcertified2 Hsource2.
  assert (Himplementation : implementation1 = implementation2).
  {
    eapply
      phase1_surface_reference_shift_refined_record_data_implementation_certified_unique.
    - exact Hcertified1.
    - exact Hcertified2.
  }
  subst implementation2.
  rewrite Hsource1 in Hsource2.
  inversion Hsource2.
  reflexivity.
Qed.
