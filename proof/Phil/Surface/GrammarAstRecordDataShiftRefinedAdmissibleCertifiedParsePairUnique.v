From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleCertifiedParsePairCertificate.

Import ListNotations.

(*
  Expose the joint uniqueness packaged by #1546 as a direct transport law for
  caller-held admissible certified implementation/parse-tree pairs.

  #1546 proves that an admissible shift-refined record/data token stream has
  exactly one (certified implementation, ParseTree) pair whose implementation
  source projection reconstructs that tree. This slice lets callers compare
  two independently held certified pairs directly: if both satisfy that same
  stable certified-boundary predicate, the pairs are equal.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1546.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_certified_parse_pair_unique :
  forall tokens implementation1 tree1 implementation2 tree2,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
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
    Hadmissible
    Hcertified1 Hsource1
    Hcertified2 Hsource2.
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_certified_parse_pair_certificate_exists_unique
      tokens Hadmissible)
    as [canonical [_ Hunique]].
  assert (Hpair1 : (implementation1, tree1) = canonical).
  {
    apply Hunique.
    cbn.
    split.
    - exact Hcertified1.
    - exact Hsource1.
  }
  assert (Hpair2 : (implementation2, tree2) = canonical).
  {
    apply Hunique.
    cbn.
    split.
    - exact Hcertified2.
    - exact Hsource2.
  }
  rewrite Hpair1, Hpair2.
  reflexivity.
Qed.
