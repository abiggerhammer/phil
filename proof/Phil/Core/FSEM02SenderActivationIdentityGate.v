From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice FSEM02RestrictedSourceTransfer.

(* FSEM-02 NON-NORMATIVE: sourceSender is the checked declaration-rooted
   parameter identity, not its display spelling. activatedSender is an
   independent activation/owner-ledger premise, never inferred from source.
   The other source/message/head/owner/instance authority remains external.
   No Haskell or parser refinement is established. *)
Definition fsem02SenderActivationIdentityGate
  (sourceSender activatedSender : Name)
  (sourceAccepted messageAdmitted headsValid : bool)
  (owners : FSEM02OwnerLedger)
  (clientOccurrence serverOccurrence payloadOccurrence : string)
  (clientProcess serverProcess : string)
  (clientOld clientNext serverOld serverNext payloadOld payloadReceived : Name)
  : option FSEM02OwnerLedger :=
  if String.eqb sourceSender activatedSender then
    fsem02RestrictedSourceTransfer
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived
  else None.

Theorem fsem02SenderActivationMismatchNoSuccessor :
  forall sourceSender activatedSender sourceAccepted messageAdmitted headsValid
         owners clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived,
    sourceSender <> activatedSender ->
    fsem02SenderActivationIdentityGate sourceSender activatedSender
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived = None.
Proof.
  intros sourceSender activatedSender sourceAccepted messageAdmitted headsValid
    owners clientOccurrence serverOccurrence payloadOccurrence
    clientProcess serverProcess
    clientOld clientNext serverOld serverNext payloadOld payloadReceived Hneq.
  unfold fsem02SenderActivationIdentityGate.
  apply String.eqb_neq in Hneq.
  now rewrite Hneq.
Qed.

Theorem fsem02SenderActivationSuccessExactAndFrame :
  forall sourceSender activatedSender sourceAccepted messageAdmitted headsValid
         owners clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived after,
    fsem02SenderActivationIdentityGate sourceSender activatedSender
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived =
      Some after ->
    sourceSender = activatedSender /\
    sourceAccepted = true /\
    messageAdmitted = true /\
    headsValid = true /\
    owners payloadOccurrence = Some (clientProcess, payloadOld) /\
    after payloadOccurrence = Some (serverProcess, payloadReceived) /\
    after clientOccurrence = Some (clientProcess, clientNext) /\
    after serverOccurrence = Some (serverProcess, serverNext) /\
    (forall spectator,
      spectator <> payloadOccurrence ->
      spectator <> clientOccurrence ->
      spectator <> serverOccurrence ->
      after spectator = owners spectator).
Proof.
  intros sourceSender activatedSender sourceAccepted messageAdmitted headsValid
    owners clientOccurrence serverOccurrence payloadOccurrence
    clientProcess serverProcess
    clientOld clientNext serverOld serverNext payloadOld payloadReceived after
    Hstep.
  unfold fsem02SenderActivationIdentityGate in Hstep.
  destruct (String.eqb sourceSender activatedSender) eqn:Hsender;
    try discriminate.
  apply String.eqb_eq in Hsender.
  split.
  - exact Hsender.
  - eapply fsem02RestrictedSourceSuccessExactAndFrame.
    exact Hstep.
Qed.

Theorem fsem02SenderActivationMatchCannotAdmitBadSource :
  forall sourceSender messageAdmitted headsValid owners
         clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived,
    fsem02SenderActivationIdentityGate sourceSender sourceSender
      false messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived = None.
Proof.
  intros.
  unfold fsem02SenderActivationIdentityGate.
  rewrite String.eqb_refl.
  apply fsem02RestrictedSourceRejectsUnadmitted.
Qed.
