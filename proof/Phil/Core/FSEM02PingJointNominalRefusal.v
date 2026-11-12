From Stdlib Require Import Strings.String.
From Phil.Core Require Import
  Syntax Context SessionStep FSEM02PingJointAtomicity.

(* NON-NORMATIVE: these four boolean nominal gates are externally checked
   premises, never inferred as source-syntax authority.  This conditional
   paired model is not a refinement theorem about native ProcessRendezvous. *)

Definition fsem02PingJointNominal
  (senderInstanceOK receiverInstanceOK senderRoleOK receiverRoleOK : bool)
  (senderHead receiverHead : Session)
  (senderOld senderNext receiverOld receiverNext : Name)
  (senderBefore receiverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  if senderInstanceOK then
    if receiverInstanceOK then
      if senderRoleOK then
        if receiverRoleOK then
          fsem02PingJointResources senderHead receiverHead
            senderOld senderNext receiverOld receiverNext
            senderBefore receiverBefore
        else None
      else None
    else None
  else None.

Theorem fsem02PingJointRejectsForeignSenderInstance :
  forall ri sr rr sh rh so sn ro rn sb rb,
    fsem02PingJointNominal false ri sr rr sh rh so sn ro rn sb rb = None.
Proof. reflexivity. Qed.

Theorem fsem02PingJointRejectsForeignReceiverInstance :
  forall si sr rr sh rh so sn ro rn sb rb,
    fsem02PingJointNominal si false sr rr sh rh so sn ro rn sb rb = None.
Proof. intros; destruct si; reflexivity. Qed.

Theorem fsem02PingJointRejectsForeignSenderRole :
  forall si ri rr sh rh so sn ro rn sb rb,
    fsem02PingJointNominal si ri false rr sh rh so sn ro rn sb rb = None.
Proof. intros; destruct si, ri; reflexivity. Qed.

Theorem fsem02PingJointRejectsForeignReceiverRole :
  forall si ri sr sh rh so sn ro rn sb rb,
    fsem02PingJointNominal si ri sr false sh rh so sn ro rn sb rb = None.
Proof. intros; destruct si, ri, sr; reflexivity. Qed.

Theorem fsem02PingJointNominalSuccessRequiresEveryGate :
  forall si ri sr rr sh rh so sn ro rn sb rb sa ra,
    fsem02PingJointNominal si ri sr rr sh rh so sn ro rn sb rb =
      Some (sa, ra) ->
    si = true /\ ri = true /\ sr = true /\ rr = true /\
    fsem02PingJointResources sh rh so sn ro rn sb rb = Some (sa, ra).
Proof.
  intros si ri sr rr sh rh so sn ro rn sb rb sa ra H.
  destruct si, ri, sr, rr; simpl in H; try discriminate.
  repeat split; try reflexivity; exact H.
Qed.

Theorem fsem02PingJointNominalSuccessProjectsBothLocalSteps :
  forall si ri sr rr sh rh so sn ro rn sb rb sa ra,
    fsem02PingJointNominal si ri sr rr sh rh so sn ro rn sb rb =
      Some (sa, ra) ->
    fsem02Progression FSEM02Send sh so sn sb = StepSucceeded sa /\
    fsem02Progression FSEM02Receive rh ro rn rb = StepSucceeded ra.
Proof.
  intros si ri sr rr sh rh so sn ro rn sb rb sa ra H.
  apply fsem02PingJointNominalSuccessRequiresEveryGate in H.
  destruct H as [_ [_ [_ [_ Hjoint]]]].
  eapply fsem02PingJointSuccessProjectsBothSteps; eassumption.
Qed.

Theorem fsem02PingJointNominalAllGatesAcceptJointResult :
  forall sh rh so sn ro rn sb rb,
    fsem02PingJointNominal true true true true
      sh rh so sn ro rn sb rb =
    fsem02PingJointResources sh rh so sn ro rn sb rb.
Proof. reflexivity. Qed.
