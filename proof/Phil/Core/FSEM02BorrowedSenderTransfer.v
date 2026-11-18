From Stdlib Require Import Bool.Bool.

(*
  FSEM-02: non-normative borrowed sender-transfer admission model.
  The concrete production Core path calls consumeLinear/consumeAffine before
  receiver insertion and returns OwnerBorrowed when an owner's shared loan
  is still active. These flags are explicit observational premises, not a
  proof that Haskell Map/Set resources refine this Rocq record. External
  protocol, activation, owner identity, session heads and binder authority
  remain separately required.
*)
Record FSEM02BorrowedSenderState : Type := {
  bsSenderPresent : bool;
  bsSenderLoaned : bool;
  bsSenderTyped : bool;
  bsReceiverOccupied : bool;
  bsSpectatorPreserved : bool
}.

Inductive FSEM02BorrowedDecision : Type :=
| BSBadSource
| BSBadExternalAuthority
| BSBadProtocolBinder
| BSMissingSender
| BSBorrowedSender
| BSWrongSenderType
| BSReceiverCollision
| BSAdmitted.

Definition bsDecision (source external binder : bool)
    (s : FSEM02BorrowedSenderState) : FSEM02BorrowedDecision :=
  if source then
    if external then
      if binder then
        if bsSenderPresent s then
          if bsSenderLoaned s then BSBorrowedSender
          else if bsSenderTyped s then
            if bsReceiverOccupied s then BSReceiverCollision
            else BSAdmitted
          else BSWrongSenderType
        else BSMissingSender
      else BSBadProtocolBinder
    else BSBadExternalAuthority
  else BSBadSource.

Definition bsStep (source external binder : bool)
    (s : FSEM02BorrowedSenderState) : option FSEM02BorrowedSenderState :=
  match bsDecision source external binder s with
  | BSAdmitted =>
      Some {| bsSenderPresent := false;
              bsSenderLoaned := false;
              bsSenderTyped := true;
              bsReceiverOccupied := true;
              bsSpectatorPreserved := bsSpectatorPreserved s |}
  | _ => None
  end.

Theorem bsInvalidSourceWinsOverLoanAndCollision :
  forall external binder s,
    bsDecision false external binder s = BSBadSource /\
    bsStep false external binder s = None.
Proof. intros; split; reflexivity. Qed.

Theorem bsExternalAuthorityMustPrecedeLoanCheck :
  forall binder s,
    bsDecision true false binder s = BSBadExternalAuthority /\
    bsStep true false binder s = None.
Proof. intros; split; reflexivity. Qed.

Theorem bsProtocolBinderMustPrecedeLoanCheck :
  forall s,
    bsDecision true true false s = BSBadProtocolBinder /\
    bsStep true true false s = None.
Proof. intros; split; reflexivity. Qed.

Theorem bsOutstandingLoanWinsOverTypeAndReceiverFaults :
  forall typed occupied spectator,
    let s := {| bsSenderPresent := true;
                bsSenderLoaned := true;
                bsSenderTyped := typed;
                bsReceiverOccupied := occupied;
                bsSpectatorPreserved := spectator |} in
    bsDecision true true true s = BSBorrowedSender /\
    bsStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem bsOutstandingLoanNeverCreatesPartialSuccessor :
  forall source external binder typed occupied spectator,
    let s := {| bsSenderPresent := true;
                bsSenderLoaned := true;
                bsSenderTyped := typed;
                bsReceiverOccupied := occupied;
                bsSpectatorPreserved := spectator |} in
    bsStep source external binder s = None.
Proof.
  intros source external binder typed occupied spectator.
  destruct source, external, binder; reflexivity.
Qed.

Theorem bsRepairReceiverOnlyStillRefusesLoan :
  forall spectator,
    let s := {| bsSenderPresent := true;
                bsSenderLoaned := true;
                bsSenderTyped := true;
                bsReceiverOccupied := false;
                bsSpectatorPreserved := spectator |} in
    bsDecision true true true s = BSBorrowedSender /\
    bsStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem bsRepairLoanOnlyRevealsReceiverCollision :
  forall spectator,
    let s := {| bsSenderPresent := true;
                bsSenderLoaned := false;
                bsSenderTyped := true;
                bsReceiverOccupied := true;
                bsSpectatorPreserved := spectator |} in
    bsDecision true true true s = BSReceiverCollision /\
    bsStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem bsRepairBothPermitsExactTransferAndSpectatorFrame :
  forall spectator,
    bsStep true true true
      {| bsSenderPresent := true;
         bsSenderLoaned := false;
         bsSenderTyped := true;
         bsReceiverOccupied := false;
         bsSpectatorPreserved := spectator |} =
    Some {| bsSenderPresent := false;
            bsSenderLoaned := false;
            bsSenderTyped := true;
            bsReceiverOccupied := true;
            bsSpectatorPreserved := spectator |}.
Proof. reflexivity. Qed.

Theorem bsAdmittedStepRequiresNoOutstandingLoan :
  forall source external binder s next,
    bsStep source external binder s = Some next ->
    source = true /\ external = true /\ binder = true /\
    bsSenderPresent s = true /\
    bsSenderLoaned s = false /\
    bsSenderTyped s = true /\
    bsReceiverOccupied s = false /\
    bsSenderPresent next = false /\
    bsSenderLoaned next = false /\
    bsReceiverOccupied next = true /\
    bsSpectatorPreserved next = bsSpectatorPreserved s.
Proof.
  intros source external binder
    [owner loaned typed receiverBusy spectator] next H.
  destruct source, external, binder, owner, loaned, typed, receiverBusy;
    simpl in H; try discriminate.
  inversion H; subst; repeat split; reflexivity.
Qed.
