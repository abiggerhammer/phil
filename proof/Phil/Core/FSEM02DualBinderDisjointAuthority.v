From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02RestrictedSourceTransfer FSEM02RestrictedReceiverBinderGate.

(*
  FSEM-02 non-normative dual identity gate. Two distinct source scopes may
  spell their binders alike; sourceSender and sourceReceiver are checked
  semantic identities, NOT display names. activatedSender and
  protocolReceiver remain independently supplied external authority.
  Instance, message, source, role, root and terminal authority are NOT
  constructed by this gate. No Haskell or parser refinement is claimed.
*)
Definition fsem02DualBinderDisjointGate
  (sourceSender activatedSender sourceReceiver protocolReceiver : Name)
  (sourceAccepted messageAdmitted headsValid : bool)
  (owners : FSEM02OwnerLedger)
  (clientOccurrence serverOccurrence payloadOccurrence : string)
  (clientProcess serverProcess : string)
  (clientOld clientNext serverOld serverNext payloadOld payloadReceived : Name)
  : option FSEM02OwnerLedger :=
  if String.eqb sourceSender activatedSender then
    fsem02RestrictedReceiverBinderGate
      sourceReceiver protocolReceiver
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived
  else None.

Theorem fsem02DualWrongActivationNoSuccessor :
  forall sourceSender activatedSender sourceReceiver protocolReceiver
         sourceAccepted messageAdmitted headsValid owners
         clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived,
    sourceSender <> activatedSender ->
    fsem02DualBinderDisjointGate
      sourceSender activatedSender sourceReceiver protocolReceiver
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived = None.
Proof.
  intros sourceSender activatedSender sourceReceiver protocolReceiver
    sourceAccepted messageAdmitted headsValid owners
    clientOccurrence serverOccurrence payloadOccurrence
    clientProcess serverProcess
    clientOld clientNext serverOld serverNext payloadOld payloadReceived Hneq.
  unfold fsem02DualBinderDisjointGate.
  apply String.eqb_neq in Hneq.
  now rewrite Hneq.
Qed.

Theorem fsem02DualWrongProtocolBinderNoSuccessor :
  forall sourceSender activatedSender sourceReceiver protocolReceiver
         sourceAccepted messageAdmitted headsValid owners
         clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived,
    sourceReceiver <> protocolReceiver ->
    fsem02DualBinderDisjointGate
      sourceSender activatedSender sourceReceiver protocolReceiver
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived = None.
Proof.
  intros sourceSender activatedSender sourceReceiver protocolReceiver
    sourceAccepted messageAdmitted headsValid owners
    clientOccurrence serverOccurrence payloadOccurrence
    clientProcess serverProcess
    clientOld clientNext serverOld serverNext payloadOld payloadReceived Hneq.
  unfold fsem02DualBinderDisjointGate.
  destruct (String.eqb sourceSender activatedSender);
    [|reflexivity].
  now apply fsem02RestrictedReceiverBinderMismatchRejects.
Qed.

(* Neither checked source identity may impersonate the other external
   authority, even when their distinct source display spellings coincide. *)
Theorem fsem02DualSenderCannotImpersonateReceiver :
  forall sourceSender sourceReceiver sourceAccepted messageAdmitted headsValid
         owners clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived,
    sourceSender <> sourceReceiver ->
    fsem02DualBinderDisjointGate
      sourceSender sourceSender sourceReceiver sourceSender
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived = None.
Proof.
  intros.
  eapply fsem02DualWrongProtocolBinderNoSuccessor.
  congruence.
Qed.

Theorem fsem02DualReceiverCannotImpersonateSender :
  forall sourceSender sourceReceiver sourceAccepted messageAdmitted headsValid
         owners clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived,
    sourceSender <> sourceReceiver ->
    fsem02DualBinderDisjointGate
      sourceSender sourceReceiver sourceReceiver sourceReceiver
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived = None.
Proof.
  intros.
  eapply fsem02DualWrongActivationNoSuccessor.
  assumption.
Qed.

(* Joint success inherits EVERY checked source/owner/frame premise from
   restricted source transfer, plus both independent semantic equalities. *)
Theorem fsem02DualSuccessExactAndFrame :
  forall sourceSender activatedSender sourceReceiver protocolReceiver
         sourceAccepted messageAdmitted headsValid owners
         clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived after,
    fsem02DualBinderDisjointGate
      sourceSender activatedSender sourceReceiver protocolReceiver
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived =
      Some after ->
    sourceSender = activatedSender /\
    sourceReceiver = protocolReceiver /\
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
  intros sourceSender activatedSender sourceReceiver protocolReceiver
    sourceAccepted messageAdmitted headsValid owners
    clientOccurrence serverOccurrence payloadOccurrence
    clientProcess serverProcess
    clientOld clientNext serverOld serverNext payloadOld payloadReceived after Hstep.
  unfold fsem02DualBinderDisjointGate in Hstep.
  destruct (String.eqb sourceSender activatedSender) eqn:Hsender;
    try discriminate.
  apply String.eqb_eq in Hsender.
  split.
  - exact Hsender.
  - eapply fsem02RestrictedReceiverBinderSuccessExactAndFrame.
    exact Hstep.
Qed.

Theorem fsem02DualMatchesCannotAdmitRejectedSource :
  forall sourceSender sourceReceiver messageAdmitted headsValid owners
         clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived,
    fsem02DualBinderDisjointGate
      sourceSender sourceSender sourceReceiver sourceReceiver
      false messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived = None.
Proof.
  intros.
  unfold fsem02DualBinderDisjointGate.
  rewrite String.eqb_refl.
  apply fsem02RestrictedReceiverBinderMatchCannotAdmitBadSource.
Qed.
