From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax.

(*
  FSEM-02 non-normative *diagnostic classifier*, not a transition checker.
  The two source booleans model the specifically checked Close-operand and
  receive-payload-type cases from the restricted source adapter. Name
  values are declaration-rooted checked semantic identities, not display
  spellings; activation owner and protocol receiver binder are independently
  supplied. A "ready" result only passes these four gates and is NOT a
  successful Core transition, protocol authority, or source admission proof.
*)
Inductive FSEM02PriorityDecision : Type :=
| FSEM02PrioritySourceCloseMismatch
| FSEM02PrioritySourceTypeMismatch
| FSEM02PriorityActivationOwnerMismatch
| FSEM02PriorityProtocolBinderMismatch
| FSEM02PriorityReadyForCore.

Definition fsem02DualAuthorityDecision
  (closeOperandValid writtenReceiverTypeValid : bool)
  (sourceSender activatedSender sourceReceiver protocolReceiver : Name)
  : FSEM02PriorityDecision :=
  if closeOperandValid then
    if writtenReceiverTypeValid then
      if String.eqb sourceSender activatedSender then
        if String.eqb sourceReceiver protocolReceiver then
          FSEM02PriorityReadyForCore
        else FSEM02PriorityProtocolBinderMismatch
      else FSEM02PriorityActivationOwnerMismatch
    else FSEM02PrioritySourceTypeMismatch
  else FSEM02PrioritySourceCloseMismatch.

Theorem fsem02PrioritySourceCloseBeforeExternalFaults :
  forall writtenReceiverTypeValid sourceSender activatedSender
         sourceReceiver protocolReceiver,
    fsem02DualAuthorityDecision false writtenReceiverTypeValid
      sourceSender activatedSender sourceReceiver protocolReceiver =
      FSEM02PrioritySourceCloseMismatch.
Proof. reflexivity. Qed.

Theorem fsem02PrioritySourceTypeBeforeExternalFaults :
  forall sourceSender activatedSender sourceReceiver protocolReceiver,
    fsem02DualAuthorityDecision true false
      sourceSender activatedSender sourceReceiver protocolReceiver =
      FSEM02PrioritySourceTypeMismatch.
Proof. reflexivity. Qed.

Theorem fsem02PriorityOwnerBeforeProtocolBinder :
  forall sourceSender activatedSender sourceReceiver protocolReceiver,
    sourceSender <> activatedSender ->
    fsem02DualAuthorityDecision true true
      sourceSender activatedSender sourceReceiver protocolReceiver =
      FSEM02PriorityActivationOwnerMismatch.
Proof.
  intros sourceSender activatedSender sourceReceiver protocolReceiver Hneq.
  unfold fsem02DualAuthorityDecision.
  apply String.eqb_neq in Hneq.
  now rewrite Hneq.
Qed.

Theorem fsem02PriorityProtocolBinderAfterOwnerRepair :
  forall sourceSender sourceReceiver protocolReceiver,
    sourceReceiver <> protocolReceiver ->
    fsem02DualAuthorityDecision true true
      sourceSender sourceSender sourceReceiver protocolReceiver =
      FSEM02PriorityProtocolBinderMismatch.
Proof.
  intros sourceSender sourceReceiver protocolReceiver Hneq.
  unfold fsem02DualAuthorityDecision.
  rewrite String.eqb_refl.
  apply String.eqb_neq in Hneq.
  now rewrite Hneq.
Qed.

Theorem fsem02PriorityBothAuthoritiesRestored :
  forall sourceSender sourceReceiver,
    fsem02DualAuthorityDecision true true
      sourceSender sourceSender sourceReceiver sourceReceiver =
      FSEM02PriorityReadyForCore.
Proof.
  intros.
  unfold fsem02DualAuthorityDecision.
  now rewrite !String.eqb_refl.
Qed.

Theorem fsem02PriorityReadyRequiresAllFourGates :
  forall closeOperandValid writtenReceiverTypeValid
         sourceSender activatedSender sourceReceiver protocolReceiver,
    fsem02DualAuthorityDecision
      closeOperandValid writtenReceiverTypeValid
      sourceSender activatedSender sourceReceiver protocolReceiver =
      FSEM02PriorityReadyForCore ->
    closeOperandValid = true /\
    writtenReceiverTypeValid = true /\
    sourceSender = activatedSender /\
    sourceReceiver = protocolReceiver.
Proof.
  intros closeOperandValid writtenReceiverTypeValid
    sourceSender activatedSender sourceReceiver protocolReceiver Hready.
  destruct closeOperandValid; [|discriminate].
  destruct writtenReceiverTypeValid; [|discriminate].
  unfold fsem02DualAuthorityDecision in Hready.
  simpl in Hready.
  destruct (String.eqb sourceSender activatedSender) eqn:Hsender;
    [|discriminate].
  destruct (String.eqb sourceReceiver protocolReceiver) eqn:Hreceiver;
    [|discriminate].
  apply String.eqb_eq in Hsender.
  apply String.eqb_eq in Hreceiver.
  repeat split; try reflexivity; assumption.
Qed.
