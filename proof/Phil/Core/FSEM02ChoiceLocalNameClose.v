From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ExplicitPeerClose.

(* FSEM-02 NON-NORMATIVE. Exact terminal occurrence ownership is conjunctive:
   the active process AND the local endpoint Name must agree. Source checking,
   activation, external protocol/role authority, scheduler and separately
   granted End disposal are premises, not conclusions of this ledger model. *)
Theorem fsem02WrongLocalTerminalNameRejectsLiveOwner :
  forall owners occurrence process goodName wrongName,
    goodName <> wrongName ->
    owners occurrence = Some (process, goodName) ->
    fsem02RetireSelectedClientOwner owners occurrence process wrongName = None.
Proof.
  intros owners occurrence process goodName wrongName Hname Howner.
  unfold fsem02RetireSelectedClientOwner, fsem02OwnerMatches.
  rewrite Howner, String.eqb_refl.
  assert (Hwrong : String.eqb goodName wrongName = false).
  { apply String.eqb_neq. exact Hname. }
  now rewrite Hwrong.
Qed.

Theorem fsem02SourceChoiceWrongLocalTerminalNamesCannotClose :
  forall labels branches chosen peer clientOld clientNext peerOld peerNext
         clientContext peerContext owners co po cp pp cr pr ready
         wrongClient wrongPeer,
    clientNext <> wrongClient ->
    peerNext <> wrongPeer ->
    fsem02StatefulSourceChoice labels branches chosen peer
      clientOld clientNext peerOld peerNext clientContext peerContext
      owners co po cp pp = Some ((cr, pr), ready) ->
    fsem02RetireSelectedClientOwner ready co cp wrongClient = None /\
    fsem02RetireExplicitPeerEnd ready po pp wrongPeer = None /\
    ready co = Some (cp, clientNext) /\
    ready po = Some (pp, peerNext) /\
    (forall spectator, spectator <> co -> spectator <> po ->
      ready spectator = owners spectator).
Proof.
  intros labels branches chosen peer clientOld clientNext peerOld peerNext
    clientContext peerContext owners co po cp pp cr pr ready
    wrongClient wrongPeer HclientName HpeerName Hsource.
  pose proof (fsem02StatefulSourceChoiceSuccessIsJointAndExactOwners
    labels branches chosen peer clientOld clientNext peerOld peerNext
    clientContext peerContext owners co po cp pp cr pr ready Hsource)
    as [_ [Hclient [Hpeer Hframe]]].
  repeat split.
  - eapply fsem02WrongLocalTerminalNameRejectsLiveOwner; eassumption.
  - unfold fsem02RetireExplicitPeerEnd.
    eapply fsem02WrongLocalTerminalNameRejectsLiveOwner; eassumption.
  - exact Hclient.
  - exact Hpeer.
  - exact Hframe.
Qed.

(* After both independently granted Closes, even an attempted same-process
   name substitution has no owner occurrence from which to proceed.
   No universal Haskell-to-Rocq refinement is asserted. *)
Theorem fsem02WrongLocalNameCannotResurrectEitherCloseOrder :
  forall ready co po cp pp clientNext peerNext wrongClient wrongPeer
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
    fsem02RetireSelectedClientOwner afterForward co cp wrongClient = None /\
    fsem02RetireExplicitPeerEnd afterForward po pp wrongPeer = None /\
    fsem02RetireSelectedClientOwner afterReverse co cp wrongClient = None /\
    fsem02RetireExplicitPeerEnd afterReverse po pp wrongPeer = None.
Proof.
  intros ready co po cp pp clientNext peerNext wrongClient wrongPeer
    afterClient afterForward afterPeer afterReverse
    Hdistinct Hclient Hforward HpeerFirst Hreverse.
  pose proof (fsem02ExplicitPeerPairRetiresExactlyBothAndFrames
    ready co cp clientNext afterClient po pp peerNext afterForward
    Hdistinct Hclient Hforward) as [HfClient [HfPeer _]].
  assert (HreverseDistinct : po <> co).
  { intro Heq. apply Hdistinct. symmetry. exact Heq. }
  change (fsem02RetireSelectedClientOwner ready po pp peerNext =
    Some afterPeer) in HpeerFirst.
  change (fsem02RetireExplicitPeerEnd afterPeer co cp clientNext =
    Some afterReverse) in Hreverse.
  pose proof (fsem02ExplicitPeerPairRetiresExactlyBothAndFrames
    ready po pp peerNext afterPeer co cp clientNext afterReverse
    HreverseDistinct HpeerFirst Hreverse) as [HrPeer [HrClient _]].
  repeat split.
  - apply fsem02SelectedClientCloseRejectsMissingOwner. exact HfClient.
  - apply fsem02ExplicitPeerCloseRejectsMissingOwner. exact HfPeer.
  - apply fsem02SelectedClientCloseRejectsMissingOwner. exact HrClient.
  - apply fsem02ExplicitPeerCloseRejectsMissingOwner. exact HrPeer.
Qed.
