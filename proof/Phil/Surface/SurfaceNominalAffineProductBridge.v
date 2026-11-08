From Stdlib Require Import Strings.String Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context DataMode DataProduct.
From Phil.Surface Require Import
  SurfaceFlatProductCorrespondence
  SurfaceFiniteContextFrame
  SurfaceSourceAffineBridge.

(*
  FSEM-01: a nominal affine element plus a linear Bytes element in a checked
  flat-product return. The type carriers are abstract and name equality is
  Rocq String, not Haskell Text. The admitted nominal lifecycle gate remains
  an external premise; Haskell-to-Rocq product decoder/checker refinement
  and satisfies-C authority are NOT established here.
*)

Definition nominalAffineLinearProduct
  (permitTy bytesTy : Syntax.Ty) : list DataProduct.ProductElementContract :=
  [ DataProduct.mkProductElementContract Syntax.Affine permitTy
  ; DataProduct.mkProductElementContract Syntax.Linear bytesTy
  ].

Theorem nominal_affine_linear_aggregate_mode_is_linear :
  forall permitTy bytesTy,
    DataProduct.deriveProductMode
      (nominalAffineLinearProduct permitTy bytesTy) = Syntax.Linear.
Proof. intros; reflexivity. Qed.

Theorem source_admitted_nominal_product_keeps_affine_premise :
  forall declaredMode admitted permitTy bytesTy,
    SurfaceSourceAffineBridge.checkedSourceAffineMode
      declaredMode admitted = Some Syntax.Affine ->
    declaredMode = Syntax.Affine /\
    admitted = true /\
    DataProduct.deriveProductMode
      (nominalAffineLinearProduct permitTy bytesTy) = Syntax.Linear.
Proof.
  intros declaredMode admitted permitTy bytesTy Hchecked.
  pose proof
    (SurfaceSourceAffineBridge.source_affine_requires_admitted_evidence
      declaredMode admitted Hchecked) as [Hmode Hadmitted].
  repeat split; try assumption; reflexivity.
Qed.

(* Sound type equality is an explicit premise: it is not a proof that Haskell
   Eq or the parsed nominal resolver implements Rocq abstract Ty equality. *)
Theorem matched_nominal_product_preserves_exact_ordered_members :
  forall (eqTy : Syntax.Ty -> Syntax.Ty -> bool),
    (forall first second,
      eqTy first second = true -> first = second) ->
    forall permitTy bytesTy actual,
      SurfaceFlatProductCorrespondence.matchFlatProduct eqTy
        (nominalAffineLinearProduct permitTy bytesTy) actual = true ->
      actual = nominalAffineLinearProduct permitTy bytesTy.
Proof.
  intros eqTy Heq permitTy bytesTy actual Hchecked.
  symmetry.
  eapply SurfaceFlatProductCorrespondence.checked_flat_product_preserves_exact_ordered_contract.
  - exact Heq.
  - exact Hchecked.
Qed.

Theorem identical_nominal_product_is_accepted_by_exact_contract :
  forall (eqTy : Syntax.Ty -> Syntax.Ty -> bool),
    (forall ty, eqTy ty ty = true) ->
    forall permitTy bytesTy,
      SurfaceFlatProductCorrespondence.matchFlatProduct eqTy
        (nominalAffineLinearProduct permitTy bytesTy)
        (nominalAffineLinearProduct permitTy bytesTy) = true.
Proof.
  intros eqTy Heq permitTy bytesTy.
  now apply SurfaceFlatProductCorrespondence.checked_flat_product_accepts_identical_contract.
Qed.

Theorem reversed_nominal_linear_elements_rejected :
  forall (eqTy : Syntax.Ty -> Syntax.Ty -> bool) permitTy bytesTy,
    SurfaceFlatProductCorrespondence.matchFlatProduct eqTy
      (nominalAffineLinearProduct permitTy bytesTy)
      [ DataProduct.mkProductElementContract Syntax.Linear bytesTy
      ; DataProduct.mkProductElementContract Syntax.Affine permitTy ] = false.
Proof. intros; reflexivity. Qed.

Theorem wrong_affine_element_mode_rejected :
  forall (eqTy : Syntax.Ty -> Syntax.Ty -> bool) permitTy bytesTy,
    SurfaceFlatProductCorrespondence.matchFlatProduct eqTy
      (nominalAffineLinearProduct permitTy bytesTy)
      [ DataProduct.mkProductElementContract Syntax.Unrestricted permitTy
      ; DataProduct.mkProductElementContract Syntax.Linear bytesTy ] = false.
Proof. intros; reflexivity. Qed.

Theorem wrong_linear_element_mode_rejected :
  forall (eqTy : Syntax.Ty -> Syntax.Ty -> bool) permitTy bytesTy,
    SurfaceFlatProductCorrespondence.matchFlatProduct eqTy
      (nominalAffineLinearProduct permitTy bytesTy)
      [ DataProduct.mkProductElementContract Syntax.Affine permitTy
      ; DataProduct.mkProductElementContract Syntax.Unrestricted bytesTy ] = false.
Proof.
  intros eqTy permitTy bytesTy.
  simpl.
  destruct (eqTy permitTy permitTy); reflexivity.
Qed.

Theorem nominal_product_exact_arity_after_checked_match :
  forall (eqTy : Syntax.Ty -> Syntax.Ty -> bool),
    (forall first second, eqTy first second = true -> first = second) ->
    forall permitTy bytesTy actual,
      SurfaceFlatProductCorrespondence.matchFlatProduct eqTy
        (nominalAffineLinearProduct permitTy bytesTy) actual = true ->
      length actual = 2.
Proof.
  intros eqTy Heq permitTy bytesTy actual Hmatch.
  pose proof
    (SurfaceFlatProductCorrespondence.checked_flat_product_preserves_arity
      eqTy Heq
      (nominalAffineLinearProduct permitTy bytesTy) actual Hmatch) as Hlen.
  simpl in Hlen.
  now symmetry.
Qed.

(* A bounded, two-transition resource model: after an unloaned affine
   consumption and a linear consumption, both returned owners are absent.
   Borrowing/closing is supplied by earlier context lemmas and executable
   source traces. This is NOT a proof of the native Haskell operations. *)
Theorem checked_nominal_product_return_consumes_both_owners :
  forall permit payload permitTy bytesTy before afterAffine finished,
    SurfaceFiniteContextFrame.consumeAffineModel permit before =
      Some (permitTy, afterAffine) ->
    Context.consumeLinear payload afterAffine =
      Context.Consumed bytesTy finished ->
    Context.affineBindings finished permit = None /\
    Context.linearBindings finished payload = None.
Proof.
  intros permit payload permitTy bytesTy before afterAffine finished
    Haffine Hlinear.
  pose proof
    (SurfaceSourceAffineBridge.source_affine_consume_preserves_every_spectator
      permit permitTy before afterAffine Haffine) as
      [_ [Hremoved [_ _]]].
  pose proof
    (Context.consumeLinear_success_exact
      payload afterAffine finished bytesTy Hlinear) as
      [_ [HlinearRemoved [_ [_ [HaffineFrame _]]]]].
  split.
  - now rewrite HaffineFrame.
  - exact HlinearRemoved.
Qed.

(* Every unrelated binding and loan survives both source-ordered moves. *)
Theorem checked_nominal_product_return_frames_foreign_context :
  forall permit payload permitTy bytesTy before afterAffine finished,
    SurfaceFiniteContextFrame.consumeAffineModel permit before =
      Some (permitTy, afterAffine) ->
    Context.consumeLinear payload afterAffine =
      Context.Consumed bytesTy finished ->
    forall spectator,
      String.eqb spectator permit = false ->
      String.eqb spectator payload = false ->
      Context.unrestrictedBindings finished spectator =
        Context.unrestrictedBindings before spectator /\
      Context.affineBindings finished spectator =
        Context.affineBindings before spectator /\
      Context.linearBindings finished spectator =
        Context.linearBindings before spectator /\
      Context.sharedLoans finished spectator =
        Context.sharedLoans before spectator.
Proof.
  intros permit payload permitTy bytesTy before afterAffine finished
    Haffine Hlinear spectator HneqPermit HneqPayload.
  pose proof
    (SurfaceFiniteContextFrame.successful_affine_consume_frames_any_finite_context
      permit permitTy before afterAffine Haffine)
      as HframeAffine.
  pose proof
    (SurfaceFiniteContextFrame.successful_linear_consume_frames_any_finite_context
      payload bytesTy afterAffine finished Hlinear)
      as HframeLinear.
  specialize (HframeAffine spectator HneqPermit).
  specialize (HframeLinear spectator HneqPayload).
  destruct HframeAffine as [Hu1 [Ha1 [Hl1 Hloan1]]].
  destruct HframeLinear as [Hu2 [Ha2 [Hl2 Hloan2]]].
  repeat split; congruence.
Qed.

Print Assumptions nominal_affine_linear_aggregate_mode_is_linear.
Print Assumptions source_admitted_nominal_product_keeps_affine_premise.
Print Assumptions matched_nominal_product_preserves_exact_ordered_members.
Print Assumptions identical_nominal_product_is_accepted_by_exact_contract.
Print Assumptions reversed_nominal_linear_elements_rejected.
Print Assumptions wrong_affine_element_mode_rejected.
Print Assumptions wrong_linear_element_mode_rejected.
Print Assumptions nominal_product_exact_arity_after_checked_match.
Print Assumptions checked_nominal_product_return_consumes_both_owners.
Print Assumptions checked_nominal_product_return_frames_foreign_context.
