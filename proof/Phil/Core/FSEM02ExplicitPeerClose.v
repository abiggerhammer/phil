From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02SelectedClientClose.

(*
  FSEM-02: conditional explicit Server End retirement after the already
  source-checked Client select/offer and Client close. The second Core
  close is NOT a source offer-arm evaluation or a root discharge.
  Both original owner identities and the separate Server terminal
  authority are premises; no Haskell implementation refinement is inferred.
*)
Definition fsem02RetireExplicitPeerEnd
  (owners : FSEM02OwnerLedger) (occurrence process : string)
  (endpoint : Name) : option FSEM02OwnerLedger :=
  fsem02RetireSelectedClientOwner owners occurrence process endpoint.

Theorem fsem02ExplicitPeerCloseRequiresExactLiveServerOwner :
  forall owners occurrence process endpoint after,
    fsem02RetireExplicitPeerEnd owners occurrence process endpoint =
      Some after ->
    owners occurrence = Some (process, endpoint).
Proof.
  intros owners occurrence process endpoint after Hclose.
  exact (fsem02SelectedClientCloseRequiresExactOwner
    owners occurrence process endpoint after Hclose).
Qed.

Theorem fsem02ExplicitPeerCloseRejectsMissingOwner :
  forall owners occurrence process endpoint,
    owners occurrence = None ->
    fsem02RetireExplicitPeerEnd owners occurrence process endpoint = None.
Proof.
  intros owners occurrence process endpoint Hmissing.
  exact (fsem02SelectedClientCloseRejectsMissingOwner
    owners occurrence process endpoint Hmissing).
Qed.

Theorem fsem02ExplicitPeerPairRetiresExactlyBothAndFrames :
  forall owners clientOccurrence clientProcess clientNext afterClient
         peerOccurrence peerProcess peerNext afterBoth,
    clientOccurrence <> peerOccurrence ->
    fsem02RetireSelectedClientOwner owners
      clientOccurrence clientProcess clientNext = Some afterClient ->
    fsem02RetireExplicitPeerEnd afterClient
      peerOccurrence peerProcess peerNext = Some afterBoth ->
    afterBoth clientOccurrence = None /\
    afterBoth peerOccurrence = None /\
    (forall spectator,
      spectator <> clientOccurrence ->
      spectator <> peerOccurrence ->
      afterBoth spectator = owners spectator).
Proof.
  intros owners clientOccurrence clientProcess clientNext afterClient
    peerOccurrence peerProcess peerNext afterBoth Hdistinct Hclient Hpeer.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    owners clientOccurrence clientProcess clientNext afterClient Hclient)
      as [HclientGone HclientFrame].
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    afterClient peerOccurrence peerProcess peerNext afterBoth Hpeer)
      as [HpeerGone HpeerFrame].
  repeat split.
  - rewrite (HpeerFrame clientOccurrence Hdistinct).
    exact HclientGone.
  - exact HpeerGone.
  - intros spectator HnotClient HnotPeer.
    rewrite (HpeerFrame spectator HnotPeer).
    apply HclientFrame. exact HnotClient.
Qed.

Theorem fsem02ExplicitPeerCannotCloseSameOwnerTwice :
  forall owners occurrence process endpoint after,
    fsem02RetireExplicitPeerEnd owners occurrence process endpoint =
      Some after ->
    fsem02RetireExplicitPeerEnd after occurrence process endpoint = None.
Proof.
  intros owners occurrence process endpoint after Hstep.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    owners occurrence process endpoint after Hstep) as [Hgone _].
  apply fsem02ExplicitPeerCloseRejectsMissingOwner.
  exact Hgone.
Qed.
