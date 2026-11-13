From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ExplicitPeerClose
  FSEM02ChoiceHalfClosePredecessorReplay.

(* FSEM-02 NON-NORMATIVE: a fully closed two-owner source choice has no
   source-choice predecessor and neither End owner can be reused.  The
   accepted source projection and BOTH separately authorized close orders
   are premises; no source-to-Rocq refinement or root authority is inferred. *)
Theorem fsem02ChoiceFullyClosedNeitherOrderCanResurrect :
  forall labels branches chosen peer old next peerOld peerNext
         clientContext peerContext owners
         co po cp pp cr pr ready afterClient afterForward afterPeer afterReverse,
    co <> po ->
    fsem02StatefulSourceChoice labels branches chosen peer
      old next peerOld peerNext clientContext peerContext
      owners co po cp pp = Some ((cr, pr), ready) ->
    fsem02RetireSelectedClientOwner ready co cp next = Some afterClient ->
    fsem02RetireExplicitPeerEnd afterClient po pp peerNext = Some afterForward ->
    fsem02RetireExplicitPeerEnd ready po pp peerNext = Some afterPeer ->
    fsem02RetireSelectedClientOwner afterPeer co cp next = Some afterReverse ->
    fsem02AdvanceChoiceOwners afterForward co po cp pp
      old next peerOld peerNext = None /\
    fsem02AdvanceChoiceOwners afterReverse co po cp pp
      old next peerOld peerNext = None /\
    fsem02RetireSelectedClientOwner afterForward co cp next = None /\
    fsem02RetireExplicitPeerEnd afterForward po pp peerNext = None /\
    fsem02RetireSelectedClientOwner afterReverse co cp next = None /\
    fsem02RetireExplicitPeerEnd afterReverse po pp peerNext = None /\
    (forall spectator, spectator <> co -> spectator <> po ->
      afterForward spectator = owners spectator /\
      afterReverse spectator = owners spectator).
Proof.
  intros labels branches chosen peer old next peerOld peerNext
    clientContext peerContext owners co po cp pp cr pr ready
    afterClient afterForward afterPeer afterReverse
    Hdistinct Hsource Hclient Hforward HpeerFirst Hreverse.
  pose proof (fsem02StatefulSourceChoiceSuccessIsJointAndExactOwners
    labels branches chosen peer old next peerOld peerNext
    clientContext peerContext owners co po cp pp cr pr ready Hsource)
    as [_ [_ [_ HsourceFrame]]].
  pose proof (fsem02ExplicitPeerPairRetiresExactlyBothAndFrames
    ready co cp next afterClient po pp peerNext afterForward
    Hdistinct Hclient Hforward) as [HforwardClient [HforwardPeer HforwardFrame]].
  assert (HpeerDistinct : po <> co).
  { intro Heq. apply Hdistinct. symmetry. exact Heq. }
  change (fsem02RetireSelectedClientOwner ready po pp peerNext =
    Some afterPeer) in HpeerFirst.
  change (fsem02RetireExplicitPeerEnd afterPeer co cp next =
    Some afterReverse) in Hreverse.
  pose proof (fsem02ExplicitPeerPairRetiresExactlyBothAndFrames
    ready po pp peerNext afterPeer co cp next afterReverse
    HpeerDistinct HpeerFirst Hreverse)
    as [HreversePeer [HreverseClient HreverseFrame]].
  repeat split.
  - apply fsem02AdvanceChoiceOwnersRejectsMissingClient.
    exact HforwardClient.
  - apply fsem02AdvanceChoiceOwnersRejectsMissingClient.
    exact HreverseClient.
  - apply fsem02SelectedClientCloseRejectsMissingOwner.
    exact HforwardClient.
  - apply fsem02ExplicitPeerCloseRejectsMissingOwner.
    exact HforwardPeer.
  - apply fsem02SelectedClientCloseRejectsMissingOwner.
    exact HreverseClient.
  - apply fsem02ExplicitPeerCloseRejectsMissingOwner.
    exact HreversePeer.
  - intros spectator HnotClient HnotPeer. split.
    + rewrite (HforwardFrame spectator HnotClient HnotPeer).
      apply HsourceFrame; assumption.
    + rewrite (HreverseFrame spectator HnotPeer HnotClient).
      apply HsourceFrame; assumption.
Qed.
