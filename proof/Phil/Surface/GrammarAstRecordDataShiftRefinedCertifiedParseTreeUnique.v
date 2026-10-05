From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedCertified.

Import ListNotations.

(*
  Erase the source-projection and complete-derivation payload from the certified
  tree certificate after #1551 and expose exactly one ResultTree returned by
  the reference parser for any already-certified shift-refined record/data
  implementation.

  Certification already supplies one projected tree together with the exact
  reference-parser result. Because the parser result is a deterministic value,
  any second tree appearing in that same ResultTree position must be equal.
  Callers that only need parser-result canonicality therefore do not need to
  carry the implementation-source projection or Phase1CompleteDerivation.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, prove a new certified implementation existence result, or
  extend correspondence beyond the existing shift-refined record/data carrier.
  Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1551.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_parse_tree_exists_unique :
  forall tokens implementation,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation ->
    exists! tree,
      phase1_surface_reference_parse tokens = Some ([], ResultTree tree).
Proof.
  intros tokens implementation Hcertified.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_certified_tree_certificate
      tokens implementation Hcertified)
    as [tree [Hsource [Hparse Hcomplete]]].
  exists tree.
  - exact Hparse.
  - intros tree' Hparse'.
    rewrite Hparse in Hparse'.
    inversion Hparse'.
    reflexivity.
Qed.
