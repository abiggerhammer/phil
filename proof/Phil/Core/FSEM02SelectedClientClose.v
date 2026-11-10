From Stdlib Require Import Strings.String Bool.Bool.
From Phil.Core Require Import Syntax Context SessionStep
  FSEM02StatefulSourceChoice.

(*
  FSEM-02, bounded non-normative source selected-client close model.
  External premises: a valid checked select/offer source pair; the initial
  activation-derived owner ledger; binary protocol/role/peer choice; and the
  exact authorized terminal Outcome for the selected branch. No offer-arm
  return-unit -> server close inference, no runtime-to-model refinement.
*)
Definition fsem02RetireSelectedClientOwner
  (owners : FSEM02OwnerLedger) (clientOccurrence clientProcess : string)
  (clientNext : Name) : option FSEM02OwnerLedger :=
  if fsem02OwnerMatches owners clientOccurrence clientProcess clientNext
  then Some (fun key =>
    if String.eqb key clientOccurrence then None else owners key)
  else None.

Theorem fsem02SelectedClientCloseRejectsMissingOwner :
  forall owners occurrence process endpoint,
    owners occurrence = None ->
    fsem02RetireSelectedClientOwner owners occurrence process endpoint = None.
Proof.
  intros owners occurrence process endpoint Hmissing.
  unfold fsem02RetireSelectedClientOwner, fsem02OwnerMatches.
  now rewrite Hmissing.
Qed.

Theorem fsem02SelectedClientCloseRequiresExactOwner :
  forall owners occurrence process endpoint after,
    fsem02RetireSelectedClientOwner owners occurrence process endpoint =
      Some after ->
    owners occurrence = Some (process, endpoint).
Proof.
  intros owners occurrence process endpoint after Hstep.
  unfold fsem02RetireSelectedClientOwner in Hstep.
  destruct (fsem02OwnerMatches owners occurrence process endpoint)
    eqn:Hmatched; try discriminate.
  unfold fsem02OwnerMatches in Hmatched.
  destruct (owners occurrence) as [[actualProcess actualEndpoint]|]
    eqn:Howner; try discriminate.
  apply andb_true_iff in Hmatched as [Hprocess Hendpoint].
  apply String.eqb_eq in Hprocess.
  apply String.eqb_eq in Hendpoint.
  subst actualProcess actualEndpoint.
  exact Howner.
Qed.

Theorem fsem02SelectedClientCloseExactRetirementAndFrame :
  forall owners occurrence process endpoint after,
    fsem02RetireSelectedClientOwner owners occurrence process endpoint =
      Some after ->
    after occurrence = None /\
    (forall spectator, spectator <> occurrence ->
      after spectator = owners spectator).
Proof.
  intros owners occurrence process endpoint after Hstep.
  unfold fsem02RetireSelectedClientOwner in Hstep.
  destruct (fsem02OwnerMatches owners occurrence process endpoint);
    try discriminate.
  inversion Hstep; subst after; clear Hstep.
  split.
  - simpl. now rewrite String.eqb_refl.
  - intros spectator Hdistinct. simpl.
    assert (Hneq : String.eqb spectator occurrence = false).
    { apply String.eqb_neq. exact Hdistinct. }
    now rewrite Hneq.
Qed.

(* The actual Haskell adapter executes the native End close, whereas this
   theorem composes the established modeled Core resource and owner steps.
   Source shape and implementation representation remain explicit premises. *)
Theorem fsem02StatefulSelectedClientCloseConditionalFrame :
  forall sourceLabels branches chosen peer clientOld clientNext
         offerOld offerNext clientContext offerContext owners
         clientOccurrence offerOccurrence clientProcess offerProcess
         clientReady offerReady ownersReady clientDone ownersDone,
    clientOccurrence <> offerOccurrence ->
    fsem02StatefulSourceChoice sourceLabels branches chosen peer
      clientOld clientNext offerOld offerNext clientContext offerContext
      owners clientOccurrence offerOccurrence clientProcess offerProcess =
        Some ((clientReady, offerReady), ownersReady) ->
    closeEndpointResource clientNext clientReady = StepSucceeded clientDone ->
    fsem02RetireSelectedClientOwner ownersReady
      clientOccurrence clientProcess clientNext = Some ownersDone ->
    linearBindings clientDone clientNext = None /\
    ownersDone clientOccurrence = None /\
    ownersDone offerOccurrence = Some (offerProcess, offerNext) /\
    (forall spectator,
       spectator <> clientOccurrence ->
       spectator <> offerOccurrence ->
       ownersDone spectator = owners spectator).
Proof.
  intros sourceLabels branches chosen peer clientOld clientNext
    offerOld offerNext clientContext offerContext owners
    clientOccurrence offerOccurrence clientProcess offerProcess
    clientReady offerReady ownersReady clientDone ownersDone
    Hdistinct Hchoice Hclose HownerClose.
  pose proof (fsem02StatefulSourceChoiceSuccessIsJointAndExactOwners
    sourceLabels branches chosen peer clientOld clientNext offerOld offerNext
    clientContext offerContext owners clientOccurrence offerOccurrence
    clientProcess offerProcess clientReady offerReady ownersReady Hchoice)
      as [_ [_ [Hoffer HoriginalFrame]]].
  pose proof (closeEndpointResource_success_exact
    clientNext clientReady clientDone Hclose) as [_ [Hconsumed _]].
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    ownersReady clientOccurrence clientProcess clientNext ownersDone
    HownerClose) as [Hretired HretirementFrame].
  assert (HofferDistinct : offerOccurrence <> clientOccurrence).
  { intro Heq. apply Hdistinct. symmetry. exact Heq. }
  repeat split.
  - exact Hconsumed.
  - exact Hretired.
  - rewrite (HretirementFrame offerOccurrence HofferDistinct).
    exact Hoffer.
  - intros spectator HnotClient HnotOffer.
    rewrite (HretirementFrame spectator HnotClient).
    apply HoriginalFrame; assumption.
Qed.
