From Stdlib Require Import Strings.String Bool.Bool.
From Phil.Core Require Import Syntax.

(*
  FSEM-02 non-normative, source-restricted diagnostic classifier.
  Source checks, independently authorized sender occurrence/owner, and live
  sender/receiver projected head-resource agreement precede the separately
  authorized message binder in the tested native Core path. The flags are
  independently checked evidence, not an algorithm granting authority.
  Ready is only an eligibility gate: not a proved Core transfer.
*)
Inductive FSEM02HeadBinderDecision : Type :=
| FSEM02HBSourceCloseMismatch
| FSEM02HBSourceTypeMismatch
| FSEM02HBOwnerMismatch
| FSEM02HBSenderHeadMismatch
| FSEM02HBReceiverHeadMismatch
| FSEM02HBProtocolBinderMismatch
| FSEM02HBReadyForCore.

Definition fsem02HeadBinderDecision
  (sourceCloseValid writtenTypeValid : bool)
  (sourceSender activatedSender : Name)
  (senderHeadValid receiverHeadValid : bool)
  (sourceReceiver protocolReceiver : Name) : FSEM02HeadBinderDecision :=
  if sourceCloseValid then
    if writtenTypeValid then
      if String.eqb sourceSender activatedSender then
        if senderHeadValid then
          if receiverHeadValid then
            if String.eqb sourceReceiver protocolReceiver then
              FSEM02HBReadyForCore
            else FSEM02HBProtocolBinderMismatch
          else FSEM02HBReceiverHeadMismatch
        else FSEM02HBSenderHeadMismatch
      else FSEM02HBOwnerMismatch
    else FSEM02HBSourceTypeMismatch
  else FSEM02HBSourceCloseMismatch.

Theorem fsem02HBSourceCloseBeforeAllExternalFaults :
  forall writtenTypeValid sender owner sh rh receiver binder,
    fsem02HeadBinderDecision false writtenTypeValid
      sender owner sh rh receiver binder = FSEM02HBSourceCloseMismatch.
Proof. reflexivity. Qed.

Theorem fsem02HBSourceTypeBeforeAllExternalFaults :
  forall sender owner sh rh receiver binder,
    fsem02HeadBinderDecision true false
      sender owner sh rh receiver binder = FSEM02HBSourceTypeMismatch.
Proof. reflexivity. Qed.

Theorem fsem02HBOwnerBeforeBothHeadsAndBinder :
  forall sender owner sh rh receiver binder,
    sender <> owner ->
    fsem02HeadBinderDecision true true
      sender owner sh rh receiver binder = FSEM02HBOwnerMismatch.
Proof.
  intros sender owner sh rh receiver binder Hneq.
  unfold fsem02HeadBinderDecision.
  apply String.eqb_neq in Hneq.
  now rewrite Hneq.
Qed.

Theorem fsem02HBSenderHeadBeforeReceiverAndBinder :
  forall sender rh receiver binder,
    fsem02HeadBinderDecision true true
      sender sender false rh receiver binder = FSEM02HBSenderHeadMismatch.
Proof.
  intros.
  unfold fsem02HeadBinderDecision.
  now rewrite String.eqb_refl.
Qed.

Theorem fsem02HBReceiverHeadBeforeBinder :
  forall sender receiver binder,
    fsem02HeadBinderDecision true true
      sender sender true false receiver binder = FSEM02HBReceiverHeadMismatch.
Proof.
  intros.
  unfold fsem02HeadBinderDecision.
  now rewrite String.eqb_refl.
Qed.

Theorem fsem02HBProtocolBinderAfterHeadRepairs :
  forall sender receiver binder,
    receiver <> binder ->
    fsem02HeadBinderDecision true true
      sender sender true true receiver binder = FSEM02HBProtocolBinderMismatch.
Proof.
  intros sender receiver binder Hneq.
  unfold fsem02HeadBinderDecision.
  rewrite String.eqb_refl.
  apply String.eqb_neq in Hneq.
  now rewrite Hneq.
Qed.

Theorem fsem02HBAllIndependentGatesRestored :
  forall sender receiver,
    fsem02HeadBinderDecision true true
      sender sender true true receiver receiver = FSEM02HBReadyForCore.
Proof.
  intros.
  unfold fsem02HeadBinderDecision.
  now rewrite !String.eqb_refl.
Qed.

Theorem fsem02HBReadyRequiresEveryIndependentGate :
  forall closeValid typeValid sender owner sh rh receiver binder,
    fsem02HeadBinderDecision closeValid typeValid
      sender owner sh rh receiver binder = FSEM02HBReadyForCore ->
    closeValid = true /\ typeValid = true /\
    sender = owner /\ sh = true /\ rh = true /\ receiver = binder.
Proof.
  intros closeValid typeValid sender owner sh rh receiver binder Hready.
  destruct closeValid; [|discriminate].
  destruct typeValid; [|discriminate].
  unfold fsem02HeadBinderDecision in Hready.
  simpl in Hready.
  destruct (String.eqb sender owner) eqn:Howner; [|discriminate].
  destruct sh; [|discriminate].
  destruct rh; [|discriminate].
  destruct (String.eqb receiver binder) eqn:Hbinder; [|discriminate].
  apply String.eqb_eq in Howner.
  apply String.eqb_eq in Hbinder.
  repeat split; try reflexivity; assumption.
Qed.
