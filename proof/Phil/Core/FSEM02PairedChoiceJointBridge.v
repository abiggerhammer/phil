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


(*
  FSEM-02 NON-NORMATIVE dual-context spectator frame.
  Successful separately accepted Choice replay preserves BOTH local loan sets
  and every unrelated linear observer. "Other" is arbitrary, not a selected
  finite example. No equality to native Haskell Map/Set or TyEndpoint is proved.
  The separate native Go/Cancel test now puts an active affine loan on EACH
  endpoint-owning process and compares full Core successor contexts.
*)
Theorem fsem02PairedChoiceFramesBothLocalLoanSetsAndLinearSpectators :
  forall accepted admitted labels branches chosen peer co cn oo on cc oc
         clientAfter offerAfter continuation,
    offeredContinuation chosen branches = Some continuation ->
    fsem02PairedChoiceReplay accepted admitted labels branches chosen peer
      co cn oo on cc oc = Some (clientAfter, offerAfter) ->
    sharedLoans clientAfter = sharedLoans cc /\
    sharedLoans offerAfter = sharedLoans oc /\
    (forall other,
      String.eqb other co = false ->
      String.eqb other cn = false ->
      linearBindings clientAfter other = linearBindings cc other) /\
    (forall other,
      String.eqb other oo = false ->
      String.eqb other on = false ->
      linearBindings offerAfter other = linearBindings oc other).
Proof.
  intros accepted admitted labels branches chosen peer co cn oo on cc oc
    clientAfter offerAfter continuation Hcontinuation Hpair.
  unfold fsem02PairedChoiceReplay in Hpair.
  destruct (andb accepted admitted) eqn:Hgate; [|discriminate].
  unfold fsem02JointSourceChoice in Hpair.
  destruct (String.eqb chosen peer) eqn:Hpeer; [|discriminate].
  destruct (fsem02SourceContainsLabel chosen labels) eqn:Hlisted; [|discriminate].
  destruct (fsem02Progression (FSEM02Select chosen) (Select branches)
    co cn cc) as [|c] eqn:Hclient; [discriminate|].
  destruct (fsem02SourceOfferReplay labels branches chosen oo on oc)
    as [|o] eqn:Hoffer; [discriminate|].
  inversion Hpair; subst; clear Hpair.
  assert (Hselected :
    selectedContinuation (FSEM02Select chosen) (Select branches) =
      Some (Some continuation)).
  { simpl. now rewrite Hcontinuation. }
  pose proof (continuing_head_exact_predecessor_and_successor
    (FSEM02Select chosen) (Select branches)
    co cn cc clientAfter continuation Hselected Hclient) as HclientFrame.
  unfold fsem02SourceOfferReplay in Hoffer.
  rewrite Hlisted in Hoffer.
  assert (Hoffered :
    selectedContinuation (FSEM02Offer chosen) (Offer branches) =
      Some (Some continuation)).
  { simpl. now rewrite Hcontinuation. }
  pose proof (continuing_head_exact_predecessor_and_successor
    (FSEM02Offer chosen) (Offer branches)
    oo on oc offerAfter continuation Hoffered Hoffer) as HofferFrame.
  destruct HclientFrame as [_ [_ [_ [_ [HclientOther HclientLoans]]]]].
  destruct HofferFrame as [_ [_ [_ [_ [HofferOther HofferLoans]]]]].
  repeat split; assumption.
Qed.
