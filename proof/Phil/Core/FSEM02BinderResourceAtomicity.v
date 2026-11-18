From Stdlib Require Import Bool.Bool.

(*
  FSEM-02 bounded non-normative resource/authority gate.
  sourceValid is actual independent source checking; priorValid packages
  separately checked process/owner/projected-head premises. binderValid is
  the independently authorized protocol receiver identity. The resource
  flags are exact observations of a separately supplied native state,
  not authority manufactured by parsing. This is NOT Haskell refinement.
*)
Record FSEM02ResourceSnapshot : Type := {
  fsem02SenderPayloadPresent : bool;
  fsem02ReceiverSlotVacant : bool;
  fsem02SpectatorUnchanged : bool
}.

Inductive FSEM02ResourceDecision : Type :=
| FSEM02ResourceSourceReject
| FSEM02ResourcePriorReject
| FSEM02ResourceBinderReject
| FSEM02ResourceSenderMissing
| FSEM02ResourceReceiverOccupied
| FSEM02ResourceReady.

Definition fsem02ResourceDecision
    (sourceValid priorValid binderValid : bool)
    (state : FSEM02ResourceSnapshot) : FSEM02ResourceDecision :=
  if sourceValid then
    if priorValid then
      if binderValid then
        if fsem02SenderPayloadPresent state then
          if fsem02ReceiverSlotVacant state then FSEM02ResourceReady
          else FSEM02ResourceReceiverOccupied
        else FSEM02ResourceSenderMissing
      else FSEM02ResourceBinderReject
    else FSEM02ResourcePriorReject
  else FSEM02ResourceSourceReject.

Definition fsem02ResourceStep
    (sourceValid priorValid binderValid : bool)
    (state : FSEM02ResourceSnapshot) : option FSEM02ResourceSnapshot :=
  match fsem02ResourceDecision sourceValid priorValid binderValid state with
  | FSEM02ResourceReady =>
      Some {| fsem02SenderPayloadPresent := false;
              fsem02ReceiverSlotVacant := false;
              fsem02SpectatorUnchanged := fsem02SpectatorUnchanged state |}
  | _ => None
  end.

Theorem fsem02ResourceBadSourceBeforeAuthority :
  forall prior binder state,
    fsem02ResourceStep false prior binder state = None.
Proof. reflexivity. Qed.

Theorem fsem02ResourceBinderBeforeAnyResourceFault :
  forall state,
    fsem02ResourceStep true true false state = None /\
    fsem02ResourceDecision true true false state = FSEM02ResourceBinderReject.
Proof. intros; split; reflexivity. Qed.

Theorem fsem02ResourceMissingSenderBeforeReceiverOccupied :
  forall spectator,
    let state := {| fsem02SenderPayloadPresent := false;
                    fsem02ReceiverSlotVacant := false;
                    fsem02SpectatorUnchanged := spectator |} in
    fsem02ResourceStep true true true state = None /\
    fsem02ResourceDecision true true true state = FSEM02ResourceSenderMissing.
Proof. intros; split; reflexivity. Qed.

Theorem fsem02ResourceReceiverOccupancyAfterSenderRepair :
  forall spectator,
    let state := {| fsem02SenderPayloadPresent := true;
                    fsem02ReceiverSlotVacant := false;
                    fsem02SpectatorUnchanged := spectator |} in
    fsem02ResourceStep true true true state = None /\
    fsem02ResourceDecision true true true state = FSEM02ResourceReceiverOccupied.
Proof. intros; split; reflexivity. Qed.

Theorem fsem02ResourceExactTransferAndSpectatorFrame :
  forall spectator,
    fsem02ResourceStep true true true
      {| fsem02SenderPayloadPresent := true;
         fsem02ReceiverSlotVacant := true;
         fsem02SpectatorUnchanged := spectator |} =
    Some {| fsem02SenderPayloadPresent := false;
            fsem02ReceiverSlotVacant := false;
            fsem02SpectatorUnchanged := spectator |}.
Proof. reflexivity. Qed.

Theorem fsem02ResourceSuccessNeedsAllGates :
  forall source prior binder state next,
    fsem02ResourceStep source prior binder state = Some next ->
    source = true /\ prior = true /\ binder = true /\
    fsem02SenderPayloadPresent state = true /\
    fsem02ReceiverSlotVacant state = true /\
    fsem02SenderPayloadPresent next = false /\
    fsem02ReceiverSlotVacant next = false /\
    fsem02SpectatorUnchanged next = fsem02SpectatorUnchanged state.
Proof.
  intros source prior binder [sender receiver spectator] next H.
  destruct source, prior, binder, sender, receiver;
    simpl in H; try discriminate.
  inversion H; subst; repeat split; reflexivity.
Qed.
