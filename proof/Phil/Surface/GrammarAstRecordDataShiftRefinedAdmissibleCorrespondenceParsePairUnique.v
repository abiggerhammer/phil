From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleCorrespondenceParsePairCertificate.

Import ListNotations.

(*
  Expose the joint uniqueness packaged by #1544 as a direct transport law for
  caller-held admissible correspondence/parse pairs.

  #1544 proves that an admissible shift-refined record/data token stream has
  exactly one (implementation, ParseTree) pair satisfying intrinsic
  correspondence, exact source-tree reconstruction, and the certified
  reference parser result. This slice lets callers compare two independently
  held certificates directly: if both pairs satisfy that same surface
  predicate, the pairs are equal.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1544.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_correspondence_parse_pair_unique :
  forall tokens implementation1 tree1 implementation2 tree2,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
      tokens implementation1 ->
    phase1_surface_shift_refined_record_data_implementation_source_tree
      implementation1 = Some tree1 ->
    phase1_surface_reference_parse tokens = Some ([], ResultTree tree1) ->
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
      tokens implementation2 ->
    phase1_surface_shift_refined_record_data_implementation_source_tree
      implementation2 = Some tree2 ->
    phase1_surface_reference_parse tokens = Some ([], ResultTree tree2) ->
    (implementation1, tree1) = (implementation2, tree2).
Proof.
  intros
    tokens
    implementation1 tree1
    implementation2 tree2
    Hadmissible
    Hcorresponds1 Hsource1 Hparse1
    Hcorresponds2 Hsource2 Hparse2.
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_correspondence_parse_pair_certificate_exists_unique
      tokens Hadmissible)
    as [canonical [_ Hunique]].
  assert (Hpair1 : (implementation1, tree1) = canonical).
  {
    apply Hunique.
    cbn.
    repeat split.
    - exact Hcorresponds1.
    - exact Hsource1.
    - exact Hparse1.
  }
  assert (Hpair2 : (implementation2, tree2) = canonical).
  {
    apply Hunique.
    cbn.
    repeat split.
    - exact Hcorresponds2.
    - exact Hsource2.
    - exact Hparse2.
  }
  rewrite Hpair1, Hpair2.
  reflexivity.
Qed.
