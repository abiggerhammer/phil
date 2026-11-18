From Stdlib Require Import Bool.Bool.

(*
  FSEM-02 non-normative finite prefix-gate model. Native source replay calls
  checkProtocolAction on sender, then receiver, and the restricted Core step
  consumes sender payload before receiver insertion. The flags below are
  independent external observations, NOT Haskell ResourceContext refinement,
  dynamic authority or a semantics-preserving source elaborator.
*)
Record FSEM02EndpointPrefix : Type := {
  epSenderEndpointBorrowed : bool;
  epReceiverEndpointBorrowed : bool;
  epSenderPayloadBorrowed : bool;
  epReceiverDestinationBusy : bool;
  epSpectatorFrame : bool
}.

Inductive FSEM02EndpointPrefixDecision : Type :=
| EPBadSource
| EPBadAuthority
| EPBadProtocolBinder
| EPSenderEndpointBorrowed
| EPReceiverEndpointBorrowed
| EPSenderPayloadBorrowed
| EPReceiverDestinationOccupied
| EPAdmitted.

Definition epDecision (source authority binder : bool)
    (s : FSEM02EndpointPrefix) : FSEM02EndpointPrefixDecision :=
  if source then
    if authority then
      if binder then
        if epSenderEndpointBorrowed s then EPSenderEndpointBorrowed
        else if epReceiverEndpointBorrowed s then EPReceiverEndpointBorrowed
        else if epSenderPayloadBorrowed s then EPSenderPayloadBorrowed
        else if epReceiverDestinationBusy s then EPReceiverDestinationOccupied
        else EPAdmitted
      else EPBadProtocolBinder
    else EPBadAuthority
  else EPBadSource.

Definition epStep (source authority binder : bool)
    (s : FSEM02EndpointPrefix) : option FSEM02EndpointPrefix :=
  match epDecision source authority binder s with
  | EPAdmitted =>
      Some {| epSenderEndpointBorrowed := false;
              epReceiverEndpointBorrowed := false;
              epSenderPayloadBorrowed := false;
              epReceiverDestinationBusy := true;
              epSpectatorFrame := epSpectatorFrame s |}
  | _ => None
  end.

Theorem epBadSourcePrecedesEveryResourceGate :
  forall authority binder s,
    epDecision false authority binder s = EPBadSource /\
    epStep false authority binder s = None.
Proof. intros; split; reflexivity. Qed.

Theorem epAuthorityPrecedesBorrowChecks :
  forall binder s,
    epDecision true false binder s = EPBadAuthority /\
    epStep true false binder s = None.
Proof. intros; split; reflexivity. Qed.

Theorem epBinderPrecedesBorrowChecks :
  forall s,
    epDecision true true false s = EPBadProtocolBinder /\
    epStep true true false s = None.
Proof. intros; split; reflexivity. Qed.

Theorem epSenderLoanShadowsThreeLaterFaults :
  forall receiverLoan payloadLoan busy spectator,
    let s := {| epSenderEndpointBorrowed := true;
                epReceiverEndpointBorrowed := receiverLoan;
                epSenderPayloadBorrowed := payloadLoan;
                epReceiverDestinationBusy := busy;
                epSpectatorFrame := spectator |} in
    epDecision true true true s = EPSenderEndpointBorrowed /\
    epStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem epRepairSenderExposesReceiverLoan :
  forall payloadLoan busy spectator,
    let s := {| epSenderEndpointBorrowed := false;
                epReceiverEndpointBorrowed := true;
                epSenderPayloadBorrowed := payloadLoan;
                epReceiverDestinationBusy := busy;
                epSpectatorFrame := spectator |} in
    epDecision true true true s = EPReceiverEndpointBorrowed /\
    epStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem epRepairEndpointsExposesPayloadLoan :
  forall busy spectator,
    let s := {| epSenderEndpointBorrowed := false;
                epReceiverEndpointBorrowed := false;
                epSenderPayloadBorrowed := true;
                epReceiverDestinationBusy := busy;
                epSpectatorFrame := spectator |} in
    epDecision true true true s = EPSenderPayloadBorrowed /\
    epStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem epRepairLoansExposesReceiverCollision :
  forall spectator,
    let s := {| epSenderEndpointBorrowed := false;
                epReceiverEndpointBorrowed := false;
                epSenderPayloadBorrowed := false;
                epReceiverDestinationBusy := true;
                epSpectatorFrame := spectator |} in
    epDecision true true true s = EPReceiverDestinationOccupied /\
    epStep true true true s = None.
Proof. intros; split; reflexivity. Qed.

Theorem epAllRepairedPermitsModeledAtomicTransfer :
  forall spectator,
    epStep true true true
      {| epSenderEndpointBorrowed := false;
         epReceiverEndpointBorrowed := false;
         epSenderPayloadBorrowed := false;
         epReceiverDestinationBusy := false;
         epSpectatorFrame := spectator |} =
    Some {| epSenderEndpointBorrowed := false;
            epReceiverEndpointBorrowed := false;
            epSenderPayloadBorrowed := false;
            epReceiverDestinationBusy := true;
            epSpectatorFrame := spectator |}.
Proof. reflexivity. Qed.

Theorem epSuccessRequiresAllFourIndependentResourceGates :
  forall source authority binder s next,
    epStep source authority binder s = Some next ->
    source = true /\ authority = true /\ binder = true /\
    epSenderEndpointBorrowed s = false /\
    epReceiverEndpointBorrowed s = false /\
    epSenderPayloadBorrowed s = false /\
    epReceiverDestinationBusy s = false /\
    epReceiverDestinationBusy next = true /\
    epSpectatorFrame next = epSpectatorFrame s.
Proof.
  intros source authority binder [sender receiver payload busy spectator] next H.
  destruct source, authority, binder, sender, receiver, payload, busy;
    simpl in H; try discriminate.
  inversion H; subst; repeat split; reflexivity.
Qed.

Theorem epNoBorrowedPrefixProducesAnySuccessor :
  forall source authority binder receiver payload busy spectator,
    epStep source authority binder
      {| epSenderEndpointBorrowed := true;
         epReceiverEndpointBorrowed := receiver;
         epSenderPayloadBorrowed := payload;
         epReceiverDestinationBusy := busy;
         epSpectatorFrame := spectator |} = None.
Proof.
  intros; destruct source, authority, binder; reflexivity.
Qed.
