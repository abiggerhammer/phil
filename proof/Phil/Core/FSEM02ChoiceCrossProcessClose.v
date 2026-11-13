From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ExplicitPeerClose.

(* FSEM-02 NON-NORMATIVE. A terminal End occurrence belongs to its exact
   process, not merely to its protocol instance, role, outcome or endpoint
   spelling. Source admission and projection, activation, these process
   identities and terminal permission are external premises. This finite
   owner-ledger model is not a Haskell-to-Rocq refinement theorem. *)

Theorem fsem02CrossProcessCloseRejectsLiveOwner :
  forall owners occurrence process other endpoint,
    process <> other ->
    owners occurrence = Some (process, endpoint) ->
    fsem02RetireSelectedClientOwner owners occurrence other endpoint = None.
Proof.
  intros owners occurrence process other endpoint Hdifferent Howner.
  unfold fsem02RetireSelectedClientOwner, fsem02OwnerMatches.
  rewrite Howner.
  assert (Hneq : String.eqb process other = false).
  { apply String.eqb_neq. exact Hdifferent. }
  rewrite Hneq. reflexivity.
Qed.

Theorem fsem02SourceChoiceCannotCrossCloseLiveEndOwners :
  forall labels branches chosen peer clientOld clientNext peerOld peerNext
         clientContext peerContext owners
         co po cp pp cr pr ready,
    cp <> pp ->
    fsem02StatefulSourceChoice labels branches chosen peer
      clientOld clientNext peerOld peerNext clientContext peerContext
      owners co po cp pp = Some ((cr, pr), ready) ->
    fsem02RetireSelectedClientOwner ready co pp clientNext = None /\
    fsem02RetireExplicitPeerEnd ready po cp peerNext = None /\
    ready co = Some (cp, clientNext) /\
    ready po = Some (pp, peerNext) /\
    (forall spectator, spectator <> co -> spectator <> po ->
       ready spectator = owners spectator).
Proof.
  intros labels branches chosen peer clientOld clientNext peerOld peerNext
    clientContext peerContext owners co po cp pp cr pr ready
    Hprocess Hchoice.
  pose proof (fsem02StatefulSourceChoiceSuccessIsJointAndExactOwners
    labels branches chosen peer clientOld clientNext peerOld peerNext
    clientContext peerContext owners co po cp pp cr pr ready Hchoice)
    as [_ [Hclient [Hpeer Hframe]]].
  repeat split.
  - eapply fsem02CrossProcessCloseRejectsLiveOwner.
    + exact Hprocess.
    + exact Hclient.
  - unfold fsem02RetireExplicitPeerEnd.
    eapply fsem02CrossProcessCloseRejectsLiveOwner.
    + intro Heq. apply Hprocess. symmetry. exact Heq.
    + exact Hpeer.
  - exact Hclient.
  - exact Hpeer.
  - exact Hframe.
Qed.

(* In either fully retired ledger, process swapping is still no substitute
   for an owner occurrence. This explicitly covers both authorized orders. *)
Theorem fsem02SourceChoiceCrossProcessRefusalPersistsAfterBothCloses :
  forall ready co po cp pp clientNext peerNext
         afterClient afterForward afterPeer afterReverse,
    co <> po ->
    fsem02RetireSelectedClientOwner ready co cp clientNext =
      Some afterClient ->
    fsem02RetireExplicitPeerEnd afterClient po pp peerNext =
      Some afterForward ->
    fsem02RetireExplicitPeerEnd ready po pp peerNext =
      Some afterPeer ->
    fsem02RetireSelectedClientOwner afterPeer co cp clientNext =
      Some afterReverse ->
    fsem02RetireSelectedClientOwner afterForward co pp clientNext = None /\
    fsem02RetireExplicitPeerEnd afterForward po cp peerNext = None /\
    fsem02RetireSelectedClientOwner afterReverse co pp clientNext = None /\
    fsem02RetireExplicitPeerEnd afterReverse po cp peerNext = None.
Proof.
  intros ready co po cp pp clientNext peerNext
    afterClient afterForward afterPeer afterReverse
    Hdistinct Hclient Hforward HpeerFirst Hreverse.
  pose proof (fsem02ExplicitPeerPairRetiresExactlyBothAndFrames
    ready co cp clientNext afterClient po pp peerNext afterForward
    Hdistinct Hclient Hforward)
    as [HfClient [HfPeer _]].
  assert (HreverseDistinct : po <> co).
  { intro Heq. apply Hdistinct. symmetry. exact Heq. }
  change (fsem02RetireSelectedClientOwner ready po pp peerNext =
    Some afterPeer) in HpeerFirst.
  change (fsem02RetireExplicitPeerEnd afterPeer co cp clientNext =
    Some afterReverse) in Hreverse.
  pose proof (fsem02ExplicitPeerPairRetiresExactlyBothAndFrames
    ready po pp peerNext afterPeer co cp clientNext afterReverse
    HreverseDistinct HpeerFirst Hreverse)
    as [HrPeer [HrClient _]].
  repeat split.
  - apply fsem02SelectedClientCloseRejectsMissingOwner. exact HfClient.
  - apply fsem02ExplicitPeerCloseRejectsMissingOwner. exact HfPeer.
  - apply fsem02SelectedClientCloseRejectsMissingOwner. exact HrClient.
  - apply fsem02ExplicitPeerCloseRejectsMissingOwner. exact HrPeer.
Qed.
