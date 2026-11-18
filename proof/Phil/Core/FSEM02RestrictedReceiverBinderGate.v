From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice FSEM02RestrictedSourceTransfer.

(*
  FSEM-02 bounded source-to-protocol receiver-binder identity gate.
  The source binder is the declaration-rooted resolved binder, NOT its
  display spelling. The separately authorized protocol receiver binder must
  match it exactly before the restricted owner transition is even attempted.

  This is a non-normative conditional functional model. It does not derive
  source parsing fidelity, nominal protocol admission, message authority,
  activation, disposal, or Haskell Map/Set representation correctness.
*)
Definition fsem02RestrictedReceiverBinderGate
  (sourceReceiver protocolReceiver : Name)
  (sourceAccepted messageAdmitted headsValid : bool)
  (owners : FSEM02OwnerLedger)
  (clientOccurrence serverOccurrence payloadOccurrence : string)
  (clientProcess serverProcess : string)
  (clientOld clientNext serverOld serverNext payloadOld payloadReceived : Name)
  : option FSEM02OwnerLedger :=
  if String.eqb sourceReceiver protocolReceiver then
    fsem02RestrictedSourceTransfer
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived
  else None.

(* An externally supplied binder with the wrong semantic identity cannot
   manufacture a transfer, irrespective of message/head admission. *)
Theorem fsem02RestrictedReceiverBinderMismatchRejects :
  forall sourceReceiver protocolReceiver
         sourceAccepted messageAdmitted headsValid owners
         clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived,
    sourceReceiver <> protocolReceiver ->
    fsem02RestrictedReceiverBinderGate sourceReceiver protocolReceiver
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived =
      None.
Proof.
  intros sourceReceiver protocolReceiver
    sourceAccepted messageAdmitted headsValid owners
    clientOccurrence serverOccurrence payloadOccurrence
    clientProcess serverProcess
    clientOld clientNext serverOld serverNext payloadOld payloadReceived
    Hneq.
  unfold fsem02RestrictedReceiverBinderGate.
  apply String.eqb_neq in Hneq.
  rewrite Hneq.
  reflexivity.
Qed.

(* Success requires BOTH the exact source/authorized binder match and every
   admission/ownership premise of the existing restricted-source model. The
   independently owned spectator frame is inherited, not postulated anew. *)
Theorem fsem02RestrictedReceiverBinderSuccessExactAndFrame :
  forall sourceReceiver protocolReceiver
         sourceAccepted messageAdmitted headsValid owners
         clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived after,
    fsem02RestrictedReceiverBinderGate sourceReceiver protocolReceiver
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived =
      Some after ->
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
  intros sourceReceiver protocolReceiver
    sourceAccepted messageAdmitted headsValid owners
    clientOccurrence serverOccurrence payloadOccurrence
    clientProcess serverProcess
    clientOld clientNext serverOld serverNext payloadOld payloadReceived after
    Hstep.
  unfold fsem02RestrictedReceiverBinderGate in Hstep.
  destruct (String.eqb sourceReceiver protocolReceiver) eqn:Hbinder;
    try discriminate.
  apply String.eqb_eq in Hbinder.
  split.
  - exact Hbinder.
  - eapply fsem02RestrictedSourceSuccessExactAndFrame.
    exact Hstep.
Qed.

(* Matching names are necessary but never sufficient: the source itself
   must still be checked. No authority is inferred from an equal string. *)
Theorem fsem02RestrictedReceiverBinderMatchCannotAdmitBadSource :
  forall sourceReceiver messageAdmitted headsValid owners
         clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived,
    fsem02RestrictedReceiverBinderGate sourceReceiver sourceReceiver
      false messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived =
      None.
Proof.
  intros.
  unfold fsem02RestrictedReceiverBinderGate.
  rewrite String.eqb_refl.
  apply fsem02RestrictedSourceRejectsUnadmitted.
Qed.
