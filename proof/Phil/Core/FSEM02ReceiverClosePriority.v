From Stdlib Require Import Bool.Bool.

(* NON-NORMATIVE FSEM-02 finite classification. Independently checked
   protocol/owner/activation/selected-root authority is a premise.
   These finite laws do not refine real Haskell ResourceContext. *)
Inductive RCPFault := RCPBorrowed | RCPMissing | RCPWrongMode | RCPHealthy.
Inductive RCPResult :=
| RCPBadSender | RCPBadReceiver | RCPNoAuthority | RCPBorrowedSender
| RCPMissingSender | RCPWrongModeSender | RCPDuplicateReceiver | RCPAdmitted.
Record RCPState := {
  rcpSenderValid : bool;
  rcpReceiverValid : bool;
  rcpExternalValid : bool;
  rcpSenderFault : RCPFault;
  rcpReceiverBusy : bool;
  rcpSpectator : bool
}.
Definition rcpDecision (s : RCPState) : RCPResult :=
  if rcpSenderValid s then
    if rcpReceiverValid s then
      if rcpExternalValid s then
        match rcpSenderFault s with
        | RCPBorrowed => RCPBorrowedSender
        | RCPMissing => RCPMissingSender
        | RCPWrongMode => RCPWrongModeSender
        | RCPHealthy => if rcpReceiverBusy s then RCPDuplicateReceiver
                        else RCPAdmitted
        end
      else RCPNoAuthority
    else RCPBadReceiver
  else RCPBadSender.
Definition rcpNext (s : RCPState) : option (bool * bool * bool) :=
  match rcpDecision s with
  | RCPAdmitted => Some (false, true, rcpSpectator s)
  | _ => None
  end.
Theorem rcpSenderSourceFirst : forall rec ext fault busy frame,
  let s := {| rcpSenderValid := false; rcpReceiverValid := rec;
    rcpExternalValid := ext; rcpSenderFault := fault;
    rcpReceiverBusy := busy; rcpSpectator := frame |} in
  rcpDecision s = RCPBadSender /\ rcpNext s = None.
Proof. intros; split; reflexivity. Qed.
Theorem rcpReceiverSourcePreemptsAllNativeFaults : forall ext fault busy frame,
  let s := {| rcpSenderValid := true; rcpReceiverValid := false;
    rcpExternalValid := ext; rcpSenderFault := fault;
    rcpReceiverBusy := busy; rcpSpectator := frame |} in
  rcpDecision s = RCPBadReceiver /\ rcpNext s = None.
Proof. intros; split; reflexivity. Qed.
Theorem rcpExternalAuthorityIsIndependent : forall fault busy frame,
  let s := {| rcpSenderValid := true; rcpReceiverValid := true;
    rcpExternalValid := false; rcpSenderFault := fault;
    rcpReceiverBusy := busy; rcpSpectator := frame |} in
  rcpDecision s = RCPNoAuthority /\ rcpNext s = None.
Proof. intros; split; reflexivity. Qed.
Theorem rcpBorrowedSenderBeforeDestination : forall busy frame,
  let s := {| rcpSenderValid := true; rcpReceiverValid := true;
    rcpExternalValid := true; rcpSenderFault := RCPBorrowed;
    rcpReceiverBusy := busy; rcpSpectator := frame |} in
  rcpDecision s = RCPBorrowedSender /\ rcpNext s = None.
Proof. intros; split; reflexivity. Qed.
Theorem rcpMissingSenderBeforeDestination : forall busy frame,
  let s := {| rcpSenderValid := true; rcpReceiverValid := true;
    rcpExternalValid := true; rcpSenderFault := RCPMissing;
    rcpReceiverBusy := busy; rcpSpectator := frame |} in
  rcpDecision s = RCPMissingSender /\ rcpNext s = None.
Proof. intros; split; reflexivity. Qed.
Theorem rcpWrongModeBeforeDestination : forall busy frame,
  let s := {| rcpSenderValid := true; rcpReceiverValid := true;
    rcpExternalValid := true; rcpSenderFault := RCPWrongMode;
    rcpReceiverBusy := busy; rcpSpectator := frame |} in
  rcpDecision s = RCPWrongModeSender /\ rcpNext s = None.
Proof. intros; split; reflexivity. Qed.
Theorem rcpSenderOnlyRepairExposesDuplicate : forall frame,
  let s := {| rcpSenderValid := true; rcpReceiverValid := true;
    rcpExternalValid := true; rcpSenderFault := RCPHealthy;
    rcpReceiverBusy := true; rcpSpectator := frame |} in
  rcpDecision s = RCPDuplicateReceiver /\ rcpNext s = None.
Proof. intros; split; reflexivity. Qed.
Theorem rcpFullRepairFramedTransfer : forall frame,
  let s := {| rcpSenderValid := true; rcpReceiverValid := true;
    rcpExternalValid := true; rcpSenderFault := RCPHealthy;
    rcpReceiverBusy := false; rcpSpectator := frame |} in
  rcpDecision s = RCPAdmitted /\ rcpNext s = Some (false, true, frame).
Proof. intros; split; reflexivity. Qed.
Theorem rcpSuccessRequiresAllGates : forall s sourceOwner receiverOwner frame,
  rcpNext s = Some (sourceOwner, receiverOwner, frame) ->
  rcpSenderValid s = true /\ rcpReceiverValid s = true /\
  rcpExternalValid s = true /\ rcpSenderFault s = RCPHealthy /\
  rcpReceiverBusy s = false /\ sourceOwner = false /\
  receiverOwner = true /\ frame = rcpSpectator s.
Proof.
  intros [a b c d e f] x y z H.
  destruct a, b, c, d, e; simpl in H; try discriminate.
  inversion H; subst; repeat split; reflexivity.
Qed.
