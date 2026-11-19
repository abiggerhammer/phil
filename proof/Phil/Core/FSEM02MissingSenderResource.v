From Stdlib Require Import Bool.Bool.
(* NON-NORMATIVE FSEM-02 finite decision model. Source, nominal owner
   ledger, protocol/endpoint authority are external premises. The production
   Haskell Map/Set resources are exercised by native tests, not modeled here
   by representation refinement. *)
Inductive MSRDecision : Type :=
| MSRBadSource | MSRBadOwnerIndex | MSRMissingSender
| MSRReceiverDuplicate | MSRAdmitted.
Record MSRState : Type := {
  msrSourceAccepted : bool;
  msrOwnerIndexValid : bool;
  msrSenderLinearPresent : bool;
  msrReceiverOccupied : bool;
  msrSpectatorFrame : bool
}.
Definition msrDecision (s : MSRState) : MSRDecision :=
  if msrSourceAccepted s then
    if msrOwnerIndexValid s then
      if msrSenderLinearPresent s then
        if msrReceiverOccupied s then MSRReceiverDuplicate else MSRAdmitted
      else MSRMissingSender
    else MSRBadOwnerIndex
  else MSRBadSource.
Definition msrStep (s : MSRState) : option (bool * bool * bool) :=
  match msrDecision s with
  | MSRAdmitted => Some (false, true, msrSpectatorFrame s)
  | _ => None
  end.
Theorem msrSourceRefusalPreempts :
  forall owner sender busy spectator,
    let s := {| msrSourceAccepted := false;
                msrOwnerIndexValid := owner;
                msrSenderLinearPresent := sender;
                msrReceiverOccupied := busy;
                msrSpectatorFrame := spectator |} in
    msrDecision s = MSRBadSource /\ msrStep s = None.
Proof. intros; split; reflexivity. Qed.
Theorem msrOwnerIndexRefusalPreempts :
  forall sender busy spectator,
    let s := {| msrSourceAccepted := true;
                msrOwnerIndexValid := false;
                msrSenderLinearPresent := sender;
                msrReceiverOccupied := busy;
                msrSpectatorFrame := spectator |} in
    msrDecision s = MSRBadOwnerIndex /\ msrStep s = None.
Proof. intros; split; reflexivity. Qed.
Theorem msrAbsentSenderPrecedesAnyReceiver :
  forall busy spectator,
    let s := {| msrSourceAccepted := true;
                msrOwnerIndexValid := true;
                msrSenderLinearPresent := false;
                msrReceiverOccupied := busy;
                msrSpectatorFrame := spectator |} in
    msrDecision s = MSRMissingSender /\ msrStep s = None.
Proof. intros; split; reflexivity. Qed.
Theorem msrReceiverRepairDoesNotRestoreSender :
  forall spectator,
    let s := {| msrSourceAccepted := true;
                msrOwnerIndexValid := true;
                msrSenderLinearPresent := false;
                msrReceiverOccupied := false;
                msrSpectatorFrame := spectator |} in
    msrDecision s = MSRMissingSender /\ msrStep s = None.
Proof. intros; split; reflexivity. Qed.
Theorem msrSenderRepairExposesCollision :
  forall spectator,
    let s := {| msrSourceAccepted := true;
                msrOwnerIndexValid := true;
                msrSenderLinearPresent := true;
                msrReceiverOccupied := true;
                msrSpectatorFrame := spectator |} in
    msrDecision s = MSRReceiverDuplicate /\ msrStep s = None.
Proof. intros; split; reflexivity. Qed.
Theorem msrBothRepairsAllowFramedTransfer :
  forall spectator,
    let s := {| msrSourceAccepted := true;
                msrOwnerIndexValid := true;
                msrSenderLinearPresent := true;
                msrReceiverOccupied := false;
                msrSpectatorFrame := spectator |} in
    msrDecision s = MSRAdmitted /\
    msrStep s = Some (false, true, spectator).
Proof. intros; split; reflexivity. Qed.
Theorem msrNoPartialSuccessorFromAbsentSender :
  forall busy spectator,
    msrStep {| msrSourceAccepted := true;
               msrOwnerIndexValid := true;
               msrSenderLinearPresent := false;
               msrReceiverOccupied := busy;
               msrSpectatorFrame := spectator |} = None.
Proof. intros; reflexivity. Qed.
Theorem msrFramedSuccessRequiresEveryGate :
  forall s senderOwner receiverOwner spectator,
    msrStep s = Some (senderOwner, receiverOwner, spectator) ->
    msrSourceAccepted s = true /\
    msrOwnerIndexValid s = true /\
    msrSenderLinearPresent s = true /\
    msrReceiverOccupied s = false /\
    senderOwner = false /\ receiverOwner = true /\
    spectator = msrSpectatorFrame s.
Proof.
  intros [src owner sender busy frame] senderOwner receiverOwner spectator H.
  destruct src, owner, sender, busy; simpl in H; try discriminate.
  inversion H; subst; repeat split; reflexivity.
Qed.
