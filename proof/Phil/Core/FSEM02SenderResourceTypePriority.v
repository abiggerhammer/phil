From Stdlib Require Import Bool.Bool.

(*
  FSEM-02 non-normative finite decision model. Exact source validity,
  protocol/owner/head admission, and message-binder authority are separately
  supplied checks. senderTyped means the actual consumed Haskell resource
  agrees with the externally authorized message Ty, not a source-conferred
  capability. The model is NOT a Haskell Map/Set or compiler refinement.
*)
Record FSEM02TypedSenderState : Type := {
  fsem02SenderPresent : bool;
  fsem02SenderTypeCorrect : bool;
  fsem02ReceiverVacant : bool;
  fsem02SpectatorFramed : bool
}.

Inductive FSEM02TypedSenderDecision : Type :=
| FSEM02TSBadSource
| FSEM02TSBadPriorAuthority
| FSEM02TSBadMessageBinder
| FSEM02TSMissingSender
| FSEM02TSWrongSenderType
| FSEM02TSOccupiedReceiver
| FSEM02TSReady.

Definition fsem02TypedSenderDecision (source prior binder : bool)
    (s : FSEM02TypedSenderState) : FSEM02TypedSenderDecision :=
  if source then
    if prior then
      if binder then
        if fsem02SenderPresent s then
          if fsem02SenderTypeCorrect s then
            if fsem02ReceiverVacant s then FSEM02TSReady
            else FSEM02TSOccupiedReceiver
          else FSEM02TSWrongSenderType
        else FSEM02TSMissingSender
      else FSEM02TSBadMessageBinder
    else FSEM02TSBadPriorAuthority
  else FSEM02TSBadSource.

Definition fsem02TypedSenderStep (source prior binder : bool)
    (s : FSEM02TypedSenderState) : option FSEM02TypedSenderState :=
  match fsem02TypedSenderDecision source prior binder s with
  | FSEM02TSReady =>
      Some {| fsem02SenderPresent := false;
              fsem02SenderTypeCorrect := true;
              fsem02ReceiverVacant := false;
              fsem02SpectatorFramed := fsem02SpectatorFramed s |}
  | _ => None
  end.

Theorem fsem02TypedSenderSourceBeforeExternalFaults :
  forall prior binder s,
    fsem02TypedSenderDecision false prior binder s = FSEM02TSBadSource /\
    fsem02TypedSenderStep false prior binder s = None.
Proof. intros; split; reflexivity. Qed.

Theorem fsem02TypedSenderBinderBeforeResourceFaults :
  forall s,
    fsem02TypedSenderDecision true true false s = FSEM02TSBadMessageBinder /\
    fsem02TypedSenderStep true true false s = None.
Proof. intros; split; reflexivity. Qed.

Theorem fsem02TypedSenderWrongTypeBeforeOccupiedReceiver :
  forall spectator,
    let s := {| fsem02SenderPresent := true;
                fsem02SenderTypeCorrect := false;
                fsem02ReceiverVacant := false;
                fsem02SpectatorFramed := spectator |} in
    fsem02TypedSenderDecision true true true s = FSEM02TSWrongSenderType /\
    fsem02TypedSenderStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem fsem02TypedSenderTypeRepairExposesCollision :
  forall spectator,
    let s := {| fsem02SenderPresent := true;
                fsem02SenderTypeCorrect := true;
                fsem02ReceiverVacant := false;
                fsem02SpectatorFramed := spectator |} in
    fsem02TypedSenderDecision true true true s = FSEM02TSOccupiedReceiver /\
    fsem02TypedSenderStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem fsem02TypedSenderExactTransferAfterBothRepairs :
  forall spectator,
    fsem02TypedSenderStep true true true
      {| fsem02SenderPresent := true;
         fsem02SenderTypeCorrect := true;
         fsem02ReceiverVacant := true;
         fsem02SpectatorFramed := spectator |} =
    Some {| fsem02SenderPresent := false;
            fsem02SenderTypeCorrect := true;
            fsem02ReceiverVacant := false;
            fsem02SpectatorFramed := spectator |}.
Proof. reflexivity. Qed.

Theorem fsem02TypedSenderSuccessNeedsEachAdmittedGate :
  forall source prior binder s next,
    fsem02TypedSenderStep source prior binder s = Some next ->
    source = true /\ prior = true /\ binder = true /\
    fsem02SenderPresent s = true /\
    fsem02SenderTypeCorrect s = true /\
    fsem02ReceiverVacant s = true /\
    fsem02SenderPresent next = false /\
    fsem02ReceiverVacant next = false /\
    fsem02SpectatorFramed next = fsem02SpectatorFramed s.
Proof.
  intros source prior binder [present typed vacant spectator] next H.
  destruct source, prior, binder, present, typed, vacant;
    simpl in H; try discriminate.
  inversion H; subst; repeat split; reflexivity.
Qed.
