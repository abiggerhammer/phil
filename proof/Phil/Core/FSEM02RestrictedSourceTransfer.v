From Stdlib Require Import Strings.String Bool.Bool.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice.

(*
  Non-normative FSEM-02 restricted payload model.

  The source binder/type/mode checks, protocol instance and dual heads,
  payload admission, process identities, and activation-owned ledger are
  external premises. This is a conditional owner transition, NOT a Rocq
  interpreter for arbitrary Grammar-v1 sources or a Haskell refinement.
  Local endpoint resource consumption is checked by the existing Core
  SessionStep/ConcurrencySemantics interfaces and finite Haskell replay.
*)

Definition fsem02RestrictedSourceTransfer
  (sourceAccepted messageAdmitted headsValid : bool)
  (owners : FSEM02OwnerLedger)
  (clientOccurrence serverOccurrence payloadOccurrence : string)
  (clientProcess serverProcess : string)
  (clientOld clientNext serverOld serverNext payloadOld payloadReceived : Name)
  : option FSEM02OwnerLedger :=
  if andb sourceAccepted (andb messageAdmitted headsValid) then
    if orb (String.eqb payloadOccurrence clientOccurrence)
           (String.eqb payloadOccurrence serverOccurrence) then None
    else
      match fsem02AdvanceChoiceOwners owners
        clientOccurrence serverOccurrence clientProcess serverProcess
        clientOld clientNext serverOld serverNext with
      | None => None
      | Some endpointOwners =>
          if fsem02OwnerMatches owners payloadOccurrence clientProcess payloadOld
          then Some
            (fun occurrence =>
              if String.eqb occurrence payloadOccurrence
              then Some (serverProcess, payloadReceived)
              else endpointOwners occurrence)
          else None
      end
  else None.

Theorem fsem02RestrictedSourceRejectsUnadmitted :
  forall messageAdmitted headsValid owners
         clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived,
    fsem02RestrictedSourceTransfer false messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived = None.
Proof.
  intros. reflexivity.
Qed.

Theorem fsem02RestrictedSourceRejectsMissingPayload :
  forall sourceAccepted messageAdmitted headsValid owners
         clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived,
    owners payloadOccurrence = None ->
    fsem02RestrictedSourceTransfer sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived = None.
Proof.
  intros sourceAccepted messageAdmitted headsValid owners
    clientOccurrence serverOccurrence payloadOccurrence
    clientProcess serverProcess clientOld clientNext serverOld serverNext
    payloadOld payloadReceived Hmissing.
  unfold fsem02RestrictedSourceTransfer.
  destruct (andb sourceAccepted (andb messageAdmitted headsValid));
    [|reflexivity].
  destruct (orb (String.eqb payloadOccurrence clientOccurrence)
                (String.eqb payloadOccurrence serverOccurrence));
    [reflexivity|].
  destruct (fsem02AdvanceChoiceOwners owners clientOccurrence serverOccurrence
    clientProcess serverProcess clientOld clientNext serverOld serverNext);
    [|reflexivity].
  unfold fsem02OwnerMatches. now rewrite Hmissing.
Qed.

Lemma fsem02SourceOwnerMatchesTrue :
  forall owners occurrence process localName,
    fsem02OwnerMatches owners occurrence process localName = true ->
    owners occurrence = Some (process, localName).
Proof.
  intros owners occurrence process localName Hmatch.
  unfold fsem02OwnerMatches in Hmatch.
  destruct (owners occurrence) as [[actualProcess actualName]|] eqn:Howner;
    try discriminate.
  apply andb_true_iff in Hmatch as [Hp Hn].
  apply String.eqb_eq in Hp.
  apply String.eqb_eq in Hn.
  subst. reflexivity.
Qed.

Theorem fsem02RestrictedSourceSuccessExactAndFrame :
  forall sourceAccepted messageAdmitted headsValid owners
         clientOccurrence serverOccurrence payloadOccurrence
         clientProcess serverProcess
         clientOld clientNext serverOld serverNext payloadOld payloadReceived
         after,
    fsem02RestrictedSourceTransfer
      sourceAccepted messageAdmitted headsValid owners
      clientOccurrence serverOccurrence payloadOccurrence
      clientProcess serverProcess
      clientOld clientNext serverOld serverNext payloadOld payloadReceived =
      Some after ->
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
  intros sourceAccepted messageAdmitted headsValid owners
    clientOccurrence serverOccurrence payloadOccurrence
    clientProcess serverProcess
    clientOld clientNext serverOld serverNext payloadOld payloadReceived
    after Hstep.
  unfold fsem02RestrictedSourceTransfer in Hstep.
  destruct sourceAccepted eqn:Hsource; try discriminate.
  destruct messageAdmitted eqn:Hmessage; try discriminate.
  destruct headsValid eqn:Hheads; try discriminate.
  simpl in Hstep.
  destruct (orb (String.eqb payloadOccurrence clientOccurrence)
                (String.eqb payloadOccurrence serverOccurrence))
    eqn:Hdistinct; try discriminate.
  destruct (fsem02AdvanceChoiceOwners owners
    clientOccurrence serverOccurrence clientProcess serverProcess
    clientOld clientNext serverOld serverNext)
    as [endpointOwners|] eqn:Howners; try discriminate.
  destruct (fsem02OwnerMatches owners payloadOccurrence clientProcess payloadOld)
    eqn:Hpayload; try discriminate.
  inversion Hstep; subst after; clear Hstep.
  apply orb_false_iff in Hdistinct as [HnotClient HnotServer].
  apply String.eqb_neq in HnotClient.
  apply String.eqb_neq in HnotServer.
  pose proof
    (fsem02AdvanceChoiceOwnersSuccessExactAndFrame
      owners clientOccurrence serverOccurrence clientProcess serverProcess
      clientOld clientNext serverOld serverNext endpointOwners Howners)
    as [Hclient [Hserver Hframe]].
  repeat split.
  - exact Hsource.
  - exact Hmessage.
  - exact Hheads.
  - eapply fsem02SourceOwnerMatchesTrue. exact Hpayload.
  - simpl. now rewrite String.eqb_refl.
  - simpl.
    assert (Hc : String.eqb clientOccurrence payloadOccurrence = false).
    { apply String.eqb_neq. intro Heq. apply HnotClient. symmetry. exact Heq. }
    now rewrite Hc.
  - simpl.
    assert (Hs : String.eqb serverOccurrence payloadOccurrence = false).
    { apply String.eqb_neq. intro Heq. apply HnotServer. symmetry. exact Heq. }
    now rewrite Hs.
  - intros spectator HpayloadFresh HclientFresh HserverFresh.
    simpl.
    assert (HnoPayload :
      String.eqb spectator payloadOccurrence = false).
    { now apply String.eqb_neq. }
    rewrite HnoPayload.
    apply Hframe; assumption.
Qed.
