From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedCertified.

Import ListNotations.

(*
  Project complete-derivation evidence directly from an observed certified
  reference parse after #1552.

  Once callers already hold a certified shift-refined record/data
  implementation, certification supplies one canonical parser ResultTree and
  its Phase1CompleteDerivation. Any observed parser ResultTree for the same
  tokens is equal to that canonical tree by parser-result determinism, so the
  complete derivation transports to the observed tree without separately
  requiring token-level admissibility.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, prove a new certified implementation existence result, or
  extend correspondence/completeness beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1552.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_parse_complete :
  forall tokens implementation tree,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation ->
    phase1_surface_reference_parse tokens = Some ([], ResultTree tree) ->
    Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens implementation tree Hcertified Hparse.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_certified_tree_certificate
      tokens implementation Hcertified)
    as [certified_tree [Hsource [Hcertified_parse Hcomplete]]].
  rewrite Hcertified_parse in Hparse.
  inversion Hparse.
  exact Hcomplete.
Qed.
