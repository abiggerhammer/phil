From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedCertifiedTreeUnique.

Import ListNotations.

(*
  Erase the implementation witness from the caller-facing certified tree
  certificate. For every token stream satisfying the token-only admissibility
  proposition, expose exactly one reference parse tree carrying a complete
  derivation.

  This continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1531. It is a Rocq
  surface-refinement theorem only: no Grammar-v1 changes, no new declaration
  families, no runtime/parser changes, no weakening of admissibility, and no
  completeness claim beyond the existing shift-refined record/data carrier.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_tree_certificate_exists_unique :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    exists! tree,
      phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
      Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens Hadmissible.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_certified
      tokens Hadmissible)
    as [implementation [Hcertified Himplementation_unique]].
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_certified_tree_certificate_exists_unique
      tokens implementation Hcertified)
    as [tree [[Himplementation_tree [Hparse Hcomplete]] Htree_unique]].
  exists tree.
  - split.
    + exact Hparse.
    + exact Hcomplete.
  - intros tree' [Hparse' Hcomplete'].
    rewrite Hparse in Hparse'.
    inversion Hparse'.
    reflexivity.
Qed.
