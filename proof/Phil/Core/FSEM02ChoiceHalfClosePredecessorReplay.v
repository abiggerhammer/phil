From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ExplicitPeerClose.

(* FSEM-02 NON-NORMATIVE. Owner ledger replay models only the already
   consumed original source-choice predecessor after a successful choice.
   Source parsing, protocol-instance grants, activation, selected outcome,
   and real Haskell owner-map correspondence remain external obligations. *)

Theorem fsem02ChoiceReplayRejectsMissingClientOccurrence :
  forall (ready afterClient : FSEM02OwnerLedger)
         (co po cp pp : string)
         (clientOld clientNext peerOld peerNext : Name),
    fsem02RetireSelectedClientOwner ready co cp clientNext =
      Some afterClient ->
    fsem02AdvanceChoiceOwners afterClient co po cp pp
      clientOld clientNext peerOld peerNext = None.
Proof.
  intros ready afterClient co po cp pp old next peerOld peerNext Hclosed.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    ready co cp next afterClient Hclosed) as [Hmissing _].
  apply fsem02AdvanceChoiceOwnersRejectsMissingClient.
  exact Hmissing.
Qed.

(* On the peer-first prefix, the Client owner still names the *successor*.
   A replay requiring its distinct original predecessor must fail. *)
Theorem fsem02ChoiceReplayRejectsConsumedClientName :
  forall (owners : FSEM02OwnerLedger)
         (co po cp pp : string)
         (old next peerOld peerNext : Name),
    old <> next ->
    owners co = Some (cp, next) ->
    fsem02AdvanceChoiceOwners owners co po cp pp
      old next peerOld peerNext = None.
Proof.
  intros owners co po cp pp old next peerOld peerNext Hdistinct Howner.
  unfold fsem02AdvanceChoiceOwners.
  destruct (String.eqb co po); [reflexivity|].
  unfold fsem02OwnerMatches at 1.
  rewrite Howner, String.eqb_refl.
  assert (Hname : String.eqb next old = false).
  { apply String.eqb_neq. intro Heq. apply Hdistinct. symmetry. exact Heq. }
  rewrite Hname. reflexivity.
Qed.

Theorem fsem02ChoiceReplayRejectsAfterPeerFirstClose :
  forall (ready afterPeer : FSEM02OwnerLedger)
         (co po cp pp : string)
         (old next peerOld peerNext : Name),
    co <> po ->
    old <> next ->
    ready co = Some (cp, next) ->
    fsem02RetireExplicitPeerEnd ready po pp peerNext = Some afterPeer ->
    fsem02AdvanceChoiceOwners afterPeer co po cp pp
      old next peerOld peerNext = None.
Proof.
  intros ready afterPeer co po cp pp old next peerOld peerNext
    Hdistinct Hnames Howner Hpeer.
  unfold fsem02RetireExplicitPeerEnd in Hpeer.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    ready po pp peerNext afterPeer Hpeer) as [_ Hframe].
  apply fsem02ChoiceReplayRejectsConsumedClientName.
  - exact Hnames.
  - rewrite (Hframe co Hdistinct). exact Howner.
Qed.

(* Finite owner-ledger correspondence conditioned on the checked source
   choice and BOTH separately authorized one-sided End operations.
   These are not machine-code/scheduler/source-authority theorems. *)
Theorem fsem02ChoiceSourceHalfCloseOriginalReplayRejectedBothOrders :
  forall labels branches chosen peer clientOld clientNext peerOld peerNext
         clientContext peerContext owners
         co po cp pp clientReady peerReady ready afterClient afterPeer,
    co <> po ->
    clientOld <> clientNext ->
    fsem02StatefulSourceChoice labels branches chosen peer
      clientOld clientNext peerOld peerNext clientContext peerContext
      owners co po cp pp = Some ((clientReady, peerReady), ready) ->
    fsem02RetireSelectedClientOwner ready co cp clientNext =
      Some afterClient ->
    fsem02RetireExplicitPeerEnd ready po pp peerNext =
      Some afterPeer ->
    fsem02AdvanceChoiceOwners afterClient co po cp pp
      clientOld clientNext peerOld peerNext = None /\
    fsem02AdvanceChoiceOwners afterPeer co po cp pp
      clientOld clientNext peerOld peerNext = None.
Proof.
  intros labels branches chosen peer clientOld clientNext peerOld peerNext
    clientContext peerContext owners co po cp pp cr pr ready ac ap
    Hdistinct Hnames Hsource Hclient Hpeer.
  pose proof (fsem02StatefulSourceChoiceSuccessIsJointAndExactOwners
    labels branches chosen peer clientOld clientNext peerOld peerNext
    clientContext peerContext owners co po cp pp cr pr ready Hsource)
    as [_ [HclientReady _]].
  split.
  - eapply fsem02ChoiceReplayRejectsMissingClientOccurrence.
    exact Hclient.
  - eapply fsem02ChoiceReplayRejectsAfterPeerFirstClose; eauto.
Qed.
