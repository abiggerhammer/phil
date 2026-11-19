From Stdlib Require Import Bool.Bool Strings.String Lists.List.
From Phil.Core Require Import
  Syntax Context SessionStep ConcurrencySemantics
  FSEM02ProtocolHeadProgression FSEM02JointSourceChoice.

(*
  FSEM-02 NON-NORMATIVE paired local/joint source Choice model.

  Two independent external conditions gate the already modeled local
  Select/Offer pair. Their Boolean truth is NOT an activation proof and does
  not establish ConcurrencySemantics.RendezvousValid. No source-derived
  selected root, selected peer, nominal protocol instance, authority or
  scheduler is inferred here. The companion Haskell check independently
  executes production local Select/Offer and production joint rendezvous
  on actual checked Grammar-v1 Go/Cancel witnesses and compares full maps.

  SessionStep.endpointType is still an abstract Rocq token, not a proved
  correspondence to native TyEndpoint. No global Haskell refinement follows.
*)

Definition fsem02PairedChoiceReplay
  (sourceAccepted rendezvousAdmitted : bool)
  (sourceLabels : list string) (branches : Branches) (chosen peer : string)
  (clientOld clientNext offerOld offerNext : Name)
  (clientBefore offerBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  if andb sourceAccepted rendezvousAdmitted
  then fsem02JointSourceChoice sourceLabels branches chosen peer
         clientOld clientNext offerOld offerNext clientBefore offerBefore
  else None.

Theorem fsem02PairedChoiceRejectsUnacceptedSource :
  forall admitted labels branches chosen peer co cn oo on cc oc,
    fsem02PairedChoiceReplay false admitted labels branches chosen peer
      co cn oo on cc oc = None.
Proof. intros. reflexivity. Qed.

Theorem fsem02PairedChoiceRejectsMissingAdmission :
  forall accepted labels branches chosen peer co cn oo on cc oc,
    fsem02PairedChoiceReplay accepted false labels branches chosen peer
      co cn oo on cc oc = None.
Proof. intros. destruct accepted; reflexivity. Qed.

Theorem fsem02PairedChoiceRejectsPeerMismatch :
  forall accepted admitted labels branches chosen peer co cn oo on cc oc,
    String.eqb chosen peer = false ->
    fsem02PairedChoiceReplay accepted admitted labels branches chosen peer
      co cn oo on cc oc = None.
Proof.
  intros accepted admitted labels branches chosen peer co cn oo on cc oc Hbad.
  unfold fsem02PairedChoiceReplay.
  destruct (andb accepted admitted).
  - apply fsem02JointSourceChoiceRejectsPeerMismatch. exact Hbad.
  - reflexivity.
Qed.

Theorem fsem02PairedChoiceRejectsUnlistedSourceArm :
  forall accepted admitted labels branches chosen peer co cn oo on cc oc,
    ~ In chosen labels ->
    fsem02PairedChoiceReplay accepted admitted labels branches chosen peer
      co cn oo on cc oc = None.
Proof.
  intros accepted admitted labels branches chosen peer co cn oo on cc oc Habsent.
  unfold fsem02PairedChoiceReplay.
  destruct (andb accepted admitted).
  - apply fsem02JointSourceChoiceRejectsUnlistedLabel. exact Habsent.
  - reflexivity.
Qed.

Theorem fsem02PairedChoiceSuccessExact :
  forall accepted admitted labels branches chosen peer co cn oo on cc oc
         clientAfter offerAfter continuation,
    offeredContinuation chosen branches = Some continuation ->
    fsem02PairedChoiceReplay accepted admitted labels branches chosen peer
      co cn oo on cc oc = Some (clientAfter, offerAfter) ->
    accepted = true /\ admitted = true /\ String.eqb chosen peer = true /\
    linearBindings clientAfter co = None /\
    linearBindings clientAfter cn = Some (endpointType continuation) /\
    linearBindings offerAfter oo = None /\
    linearBindings offerAfter on = Some (endpointType continuation).
Proof.
  intros accepted admitted labels branches chosen peer co cn oo on cc oc
    clientAfter offerAfter continuation Hhead Hstep.
  unfold fsem02PairedChoiceReplay in Hstep.
  destruct (andb accepted admitted) eqn:Hgate; [|discriminate].
  apply andb_true_iff in Hgate as [Haccepted Hadmitted].
  pose proof (fsem02JointSourceChoiceSuccessConsumesBothExactPredecessors
    labels branches chosen peer co cn oo on cc oc
    clientAfter offerAfter continuation Hhead Hstep) as Hlocal.
  destruct Hlocal as [Hpeer [HclientGone [HclientNext
    [HofferGone HofferNext]]]].
  repeat split; assumption.
Qed.

Theorem fsem02PairedChoiceWithIndependentRestrictedRendezvous :
  forall accepted admitted labels branches chosen peer co cn oo on cc oc
         clientAfter offerAfter continuation
         messageAdmission ownershipBefore ownershipAfter rendezvous subject,
    offeredContinuation chosen branches = Some continuation ->
    fsem02PairedChoiceReplay accepted admitted labels branches chosen peer
      co cn oo on cc oc = Some (clientAfter, offerAfter) ->
    RendezvousValid messageAdmission ownershipBefore ownershipAfter rendezvous ->
    rendezvousRestrictedSubject rendezvous = Some subject ->
    linearBindings clientAfter co = None /\
    linearBindings offerAfter oo = None /\
    ownershipBefore subject = Some (rendezvousSenderProcess rendezvous) /\
    ownershipAfter subject = Some (rendezvousReceiverProcess rendezvous).
Proof.
  intros accepted admitted labels branches chosen peer co cn oo on cc oc
    clientAfter offerAfter continuation
    messageAdmission ownershipBefore ownershipAfter rendezvous subject
    Hhead Hstep Hvalid Hsubject.
  pose proof (fsem02PairedChoiceSuccessExact
    accepted admitted labels branches chosen peer co cn oo on cc oc
    clientAfter offerAfter continuation Hhead Hstep) as Hlocal.
  destruct Hlocal as [_ [_ [_ [HclientGone [_ [HofferGone _]]]]]].
  pose proof (restricted_rendezvous_transfers_exact_owner
    messageAdmission ownershipBefore ownershipAfter rendezvous subject
    Hvalid Hsubject) as [Hbefore Hafter].
  repeat split; assumption.
Qed.
