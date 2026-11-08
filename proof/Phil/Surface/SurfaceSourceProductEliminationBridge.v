From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax Context DataMode DataProduct.
From Phil.Surface Require Import SurfaceSourceAffineBridge.

(* FSEM-01: abstract finite product restoration plan, specialized to an
   explicitly admitted nominal Affine member and an intrinsic Linear member.
   The concrete Haskell product elimination is checked independently on real
   source-driven production contexts. No universal Haskell->Rocq refinement. *)

Definition sourceAffineLinearContract (permitTy bytesTy : Syntax.Ty) :
    list DataProduct.ProductElementContract :=
  [ DataProduct.mkProductElementContract Syntax.Affine permitTy
  ; DataProduct.mkProductElementContract Syntax.Linear bytesTy ].

Definition sourceAffineLinearPlan
    (permit payload : Syntax.Name) (permitTy bytesTy : Syntax.Ty) :
    list DataProduct.RestoredProductBinding :=
  [ DataProduct.mkRestoredProductBinding permit Syntax.Affine permitTy
  ; DataProduct.mkRestoredProductBinding payload Syntax.Linear bytesTy ].

Theorem source_affine_linear_product_mode_is_linear :
  forall permitTy bytesTy,
    DataProduct.deriveProductMode
      (sourceAffineLinearContract permitTy bytesTy) = Syntax.Linear.
Proof. intros; reflexivity. Qed.

Theorem source_product_restores_exact_positional_contract :
  forall permit payload permitTy bytesTy,
    DataProduct.productRestorationPlan
      (sourceAffineLinearContract permitTy bytesTy) [permit; payload] =
      Some (sourceAffineLinearPlan permit payload permitTy bytesTy).
Proof. intros; reflexivity. Qed.

Theorem source_product_elimination_accepts_distinct_successors :
  forall permit payload permitTy bytesTy,
    permit <> payload ->
    DataProduct.ProductEliminationAccepted
      (sourceAffineLinearContract permitTy bytesTy) [permit; payload].
Proof.
  intros permit payload permitTy bytesTy Hdiff.
  exists (sourceAffineLinearPlan permit payload permitTy bytesTy).
  split.
  - reflexivity.
  - constructor.
    + simpl. intros [Heq | Hempty].
      * apply Hdiff. symmetry. exact Heq.
      * contradiction.
    + constructor.
      * simpl. tauto.
      * constructor.
Qed.

Theorem source_product_elimination_requires_distinct_successors :
  forall permit payload permitTy bytesTy,
    DataProduct.ProductEliminationAccepted
      (sourceAffineLinearContract permitTy bytesTy) [permit; payload] ->
    permit <> payload.
Proof.
  intros permit payload permitTy bytesTy Haccepted Heq.
  apply DataProduct.accepted_product_elimination_has_unique_successors
    in Haccepted.
  subst payload.
  inversion Haccepted as [| _ _ Hnot _].
  apply Hnot.
  simpl; auto.
Qed.

Theorem source_product_wrong_arity_has_no_restoration_plan :
  forall successor permitTy bytesTy,
    DataProduct.productRestorationPlan
      (sourceAffineLinearContract permitTy bytesTy) [successor] = None.
Proof. intros; reflexivity. Qed.

Theorem source_product_success_preserves_two_element_arity :
  forall permitTy bytesTy successors,
    DataProduct.ProductEliminationAccepted
      (sourceAffineLinearContract permitTy bytesTy) successors ->
    length successors = 2.
Proof.
  intros permitTy bytesTy successors Haccepted.
  pose proof
    (DataProduct.accepted_product_elimination_has_exact_arity
      (sourceAffineLinearContract permitTy bytesTy)
      successors Haccepted) as Harity.
  simpl in Harity.
  exact Harity.
Qed.

Theorem source_product_affine_mode_requires_external_admission :
  forall mode admitted permitTy bytesTy,
    SurfaceSourceAffineBridge.checkedSourceAffineMode
      mode admitted = Some Syntax.Affine ->
    mode = Syntax.Affine /\ admitted = true /\
    DataProduct.deriveProductMode
      (sourceAffineLinearContract permitTy bytesTy) = Syntax.Linear.
Proof.
  intros mode admitted permitTy bytesTy Hchecked.
  pose proof
    (SurfaceSourceAffineBridge.source_affine_requires_admitted_evidence
       mode admitted Hchecked) as [Hmode Hadmitted].
  repeat split; try assumption; reflexivity.
Qed.

Theorem source_product_consumption_prevents_reusing_linear_owner :
  forall productName before after productTy,
    Context.consumeLinear productName before =
      Context.Consumed productTy after ->
    forall laterType later,
      Context.consumeLinear productName after <>
        Context.Consumed laterType later.
Proof.
  intros productName before after productTy Hconsume laterType later.
  eapply DataProduct.consuming_linear_product_is_one_shot.
  exact Hconsume.
Qed.

Theorem restored_linear_successor_cannot_be_silently_discarded :
  forall payload bytesTy before after,
    Context.insertBinding Syntax.Linear payload bytesTy before =
      Context.Inserted after ->
    ~ DataProduct.LinearCompletionAllowed after.
Proof.
  intros payload bytesTy before after Hinsert.
  eapply DataProduct.inserted_linear_product_cannot_be_silently_dropped.
  exact Hinsert.
Qed.

Print Assumptions source_affine_linear_product_mode_is_linear.
Print Assumptions source_product_restores_exact_positional_contract.
Print Assumptions source_product_elimination_accepts_distinct_successors.
Print Assumptions source_product_elimination_requires_distinct_successors.
Print Assumptions source_product_wrong_arity_has_no_restoration_plan.
Print Assumptions source_product_success_preserves_two_element_arity.
Print Assumptions source_product_affine_mode_requires_external_admission.
Print Assumptions source_product_consumption_prevents_reusing_linear_owner.
Print Assumptions restored_linear_successor_cannot_be_silently_discarded.
