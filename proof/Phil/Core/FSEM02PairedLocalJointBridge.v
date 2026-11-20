From Stdlib Require Import Bool.Bool Strings.String.
From Phil.Core Require Import Syntax Context SessionStep
  ConcurrencySemantics FSEM02ProtocolHeadProgression.

(*
  FSEM-02 NON-NORMATIVE paired-local/joint observation model.

  This is a *pair of conditional local resource steps*, not a derivation of
  synchronous rendezvous from source syntax. A separate production Haskell
  regression compares exact two-process Core results against the independently
  executed local send/receive checks on one checked Ping fixture.

  sourceAccepted and rendezvousAdmitted are EXTERNAL, separately checked
  Boolean premises. In particular, rendezvousAdmitted does NOT establish
  RendezvousValid: a proof using ConcurrencySemantics must supply that
  independent proposition. Endpoint nominal authority, activation, typing,
  selected root and disposition cannot be manufactured by these flags.

  The historical SessionStep.endpointType remains an abstract imported token;
  no equality to the Haskell TyEndpoint representation is asserted here.
*)

Definition fsem02PairedLocalReplay
  (sourceAccepted rendezvousAdmitted : bool)
  (senderAction receiverAction : FSEM02Action)
  (senderHead receiverHead : Session)
  (senderOld senderNext receiverOld receiverNext : Name)
  (senderBefore receiverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  if andb sourceAccepted rendezvousAdmitted then
    match fsem02Progression senderAction senderHead senderOld senderNext senderBefore with
    | StepFailed => None
    | StepSucceeded senderAfter =>
        match fsem02Progression receiverAction receiverHead receiverOld receiverNext receiverBefore with
        | StepFailed => None
        | StepSucceeded receiverAfter => Some (senderAfter, receiverAfter)
        end
    end
  else None.

Theorem fsem02PairedReplayRejectsUnacceptedSource :
  forall admitted sa ra sh rh so sn ro rn sc rc,
    fsem02PairedLocalReplay false admitted sa ra sh rh so sn ro rn sc rc = None.
Proof. intros. reflexivity. Qed.

Theorem fsem02PairedReplayRejectsMissingAdmission :
  forall source sa ra sh rh so sn ro rn sc rc,
    fsem02PairedLocalReplay source false sa ra sh rh so sn ro rn sc rc = None.
Proof. intros. destruct source; reflexivity. Qed.

Theorem fsem02PairedReplayRejectsMissingSender :
  forall source admitted sa ra sh rh so sn ro rn sc rc,
    linearBindings sc so = None ->
    fsem02PairedLocalReplay source admitted sa ra sh rh so sn ro rn sc rc = None.
Proof.
  intros source admitted sa ra sh rh so sn ro rn sc rc Hmissing.
  unfold fsem02PairedLocalReplay.
  destruct (andb source admitted); [|reflexivity].
  destruct (fsem02Progression sa sh so sn sc) as [|senderAfter]
    eqn:Hsender; [reflexivity|].
  exfalso.
  eapply (stale_linear_predecessor_cannot_succeed
    sa sh so sn sc senderAfter Hmissing Hsender).
Qed.

Theorem fsem02PairedReplayRejectsMissingReceiver :
  forall source admitted sa ra sh rh so sn ro rn sc rc,
    linearBindings rc ro = None ->
    fsem02PairedLocalReplay source admitted sa ra sh rh so sn ro rn sc rc = None.
Proof.
  intros source admitted sa ra sh rh so sn ro rn sc rc Hmissing.
  unfold fsem02PairedLocalReplay.
  destruct (andb source admitted); [|reflexivity].
  destruct (fsem02Progression sa sh so sn sc); [reflexivity|].
  destruct (fsem02Progression ra rh ro rn rc) as [|receiverAfter]
    eqn:Hreceiver; [reflexivity|].
  exfalso.
  eapply (stale_linear_predecessor_cannot_succeed
    ra rh ro rn rc receiverAfter Hmissing Hreceiver).
Qed.

(*
  A successful paired replay has no partial successor: BOTH independent
  SessionStep resource transitions must succeed and preserve their own loans.
  This theorem does not identify the pair with production Haskell Maps.
*)
Theorem fsem02PairedReplaySuccessExact :
  forall source admitted sa ra sh rh so sn ro rn sc rc
         senderAfter receiverAfter senderContinuation receiverContinuation,
    selectedContinuation sa sh = Some (Some senderContinuation) ->
    selectedContinuation ra rh = Some (Some receiverContinuation) ->
    fsem02PairedLocalReplay source admitted sa ra sh rh
      so sn ro rn sc rc = Some (senderAfter, receiverAfter) ->
    source = true /\ admitted = true /\
    linearBindings senderAfter so = None /\
    linearBindings senderAfter sn = Some (endpointType senderContinuation) /\
    linearBindings receiverAfter ro = None /\
    linearBindings receiverAfter rn = Some (endpointType receiverContinuation) /\
    sharedLoans senderAfter = sharedLoans sc /\
    sharedLoans receiverAfter = sharedLoans rc.
Proof.
  intros source admitted sa ra sh rh so sn ro rn sc rc
    senderAfter receiverAfter senderContinuation receiverContinuation
    HsenderHead HreceiverHead Hpair.
  unfold fsem02PairedLocalReplay in Hpair.
  destruct (andb source admitted) eqn:Hgate; [|discriminate].
  apply andb_true_iff in Hgate as [Hsource Hadmitted].
  destruct (fsem02Progression sa sh so sn sc) as [|sNext]
    eqn:HsenderStep; [discriminate|].
  destruct (fsem02Progression ra rh ro rn rc) as [|rNext]
    eqn:HreceiverStep; [discriminate|].
  inversion Hpair; subst; clear Hpair.
  pose proof (continuing_head_exact_predecessor_and_successor
    sa sh so sn sc senderAfter senderContinuation HsenderHead HsenderStep)
    as Hsender.
  pose proof (continuing_head_exact_predecessor_and_successor
    ra rh ro rn rc receiverAfter receiverContinuation HreceiverHead HreceiverStep)
    as Hreceiver.
  destruct Hsender as [_ [_ [HsenderGone [HsenderNext [_ HsenderLoans]]]]].
  destruct Hreceiver as [_ [_ [HreceiverGone [HreceiverNext [_ HreceiverLoans]]]]].
  repeat split; assumption.
Qed.

(*
  This bridge is deliberately conditional on actual ConcurrencySemantics
  RendezvousValid, rather than assuming a Boolean admission flag entails it.
  Exact restricted payload movement follows from THAT independent premise.
*)
Theorem fsem02PairedReplayWithAdmittedRestrictedRendezvous :
  forall source admitted sa ra sh rh so sn ro rn sc rc
         senderAfter receiverAfter senderContinuation receiverContinuation
         messageAdmission ownershipBefore ownershipAfter rendezvous subject,
    selectedContinuation sa sh = Some (Some senderContinuation) ->
    selectedContinuation ra rh = Some (Some receiverContinuation) ->
    fsem02PairedLocalReplay source admitted sa ra sh rh
      so sn ro rn sc rc = Some (senderAfter, receiverAfter) ->
    RendezvousValid messageAdmission ownershipBefore ownershipAfter rendezvous ->
    rendezvousRestrictedSubject rendezvous = Some subject ->
    linearBindings senderAfter so = None /\
    linearBindings receiverAfter ro = None /\
    ownershipBefore subject = Some (rendezvousSenderProcess rendezvous) /\
    ownershipAfter subject = Some (rendezvousReceiverProcess rendezvous).
Proof.
  intros source admitted sa ra sh rh so sn ro rn sc rc
    senderAfter receiverAfter senderContinuation receiverContinuation
    messageAdmission ownershipBefore ownershipAfter rendezvous subject
    Hsender Hreceiver Hpair Hrendezvous Hsubject.
  pose proof (fsem02PairedReplaySuccessExact
    source admitted sa ra sh rh so sn ro rn sc rc
    senderAfter receiverAfter senderContinuation receiverContinuation
    Hsender Hreceiver Hpair)
    as Hresources.
  destruct Hresources as [_ [_ [HsenderGone [_ [HreceiverGone _]]]]].
  pose proof (restricted_rendezvous_transfers_exact_owner
    messageAdmission ownershipBefore ownershipAfter rendezvous subject
    Hrendezvous Hsubject) as [Hbefore Hafter].
  repeat split; assumption.
Qed.


(* NON-NORMATIVE FSEM-02: symmetric paired Ping frame.
   Both exact continuing local steps preserve each own full abstract loan
   function and every unrelated linear binding. These Boolean gates are not
   a proof of RendezvousValid or of native Haskell Map/Set refinement. *)
Theorem fsem02PairedReplayFramesBothLoansAndIndependentLinearSpectators :
  forall source admitted sa ra sh rh so sn ro rn sc rc
         senderAfter receiverAfter senderContinuation receiverContinuation,
    selectedContinuation sa sh = Some (Some senderContinuation) ->
    selectedContinuation ra rh = Some (Some receiverContinuation) ->
    fsem02PairedLocalReplay source admitted sa ra sh rh
      so sn ro rn sc rc = Some (senderAfter, receiverAfter) ->
    sharedLoans senderAfter = sharedLoans sc /\
    sharedLoans receiverAfter = sharedLoans rc /\
    (forall other,
      String.eqb other so = false ->
      String.eqb other sn = false ->
      linearBindings senderAfter other = linearBindings sc other) /\
    (forall other,
      String.eqb other ro = false ->
      String.eqb other rn = false ->
      linearBindings receiverAfter other = linearBindings rc other).
Proof.
  intros source admitted sa ra sh rh so sn ro rn sc rc
    senderAfter receiverAfter senderContinuation receiverContinuation
    HsenderHead HreceiverHead Hpair.
  unfold fsem02PairedLocalReplay in Hpair.
  destruct (andb source admitted) eqn:Hgate; [|discriminate].
  destruct (fsem02Progression sa sh so sn sc) as [|sNext]
    eqn:HsenderStep; [discriminate|].
  destruct (fsem02Progression ra rh ro rn rc) as [|rNext]
    eqn:HreceiverStep; [discriminate|].
  inversion Hpair; subst; clear Hpair.
  pose proof (continuing_head_exact_predecessor_and_successor
    sa sh so sn sc sNext senderContinuation HsenderHead HsenderStep)
    as HsenderFrame.
  pose proof (continuing_head_exact_predecessor_and_successor
    ra rh ro rn rc rNext receiverContinuation HreceiverHead HreceiverStep)
    as HreceiverFrame.
  destruct HsenderFrame as [_ [_ [_ [_ [HsenderOther HsenderLoans]]]]].
  destruct HreceiverFrame as [_ [_ [_ [_ [HreceiverOther HreceiverLoans]]]]].
  repeat split; assumption.
Qed.
