From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ExplicitPeerClose.

(*
  FSEM-02 non-normative terminal diamond for DISTINCT activation owners.
  Independently given Client and Server End outcomes, correct source-choice
  authority, and both successful orders are hypotheses. The theorem only
  compares finite Rocq owner ledgers extensionally; the Haskell adapter
  independently tests whole Core state for the two real close orders.
  No Server source-close authority, scheduler fairness, or implementation
  refinement is asserted.
*)
Theorem fsem02ConditionalTerminalCloseDiamond :
  forall owners clientOccurrence clientProcess clientEndpoint
         peerOccurrence peerProcess peerEndpoint
         afterClient afterForward afterPeer afterReverse,
    clientOccurrence <> peerOccurrence ->
    fsem02RetireSelectedClientOwner owners
      clientOccurrence clientProcess clientEndpoint = Some afterClient ->
    fsem02RetireExplicitPeerEnd afterClient
      peerOccurrence peerProcess peerEndpoint = Some afterForward ->
    fsem02RetireExplicitPeerEnd owners
      peerOccurrence peerProcess peerEndpoint = Some afterPeer ->
    fsem02RetireSelectedClientOwner afterPeer
      clientOccurrence clientProcess clientEndpoint = Some afterReverse ->
    forall observed, afterForward observed = afterReverse observed.
Proof.
  intros owners clientOccurrence clientProcess clientEndpoint
    peerOccurrence peerProcess peerEndpoint
    afterClient afterForward afterPeer afterReverse
    Hdistinct Hclient Hpeer HpeerFirst HclientSecond observed.
  pose proof (fsem02ExplicitPeerPairRetiresExactlyBothAndFrames
    owners clientOccurrence clientProcess clientEndpoint afterClient
    peerOccurrence peerProcess peerEndpoint afterForward
    Hdistinct Hclient Hpeer)
    as [HforwardClient [HforwardPeer HforwardFrame]].
  assert (HreverseDistinct : peerOccurrence <> clientOccurrence).
  { intro Hsame. apply Hdistinct. symmetry. exact Hsame. }
  change (fsem02RetireSelectedClientOwner owners
    peerOccurrence peerProcess peerEndpoint = Some afterPeer)
    in HpeerFirst.
  change (fsem02RetireExplicitPeerEnd afterPeer
    clientOccurrence clientProcess clientEndpoint = Some afterReverse)
    in HclientSecond.
  pose proof (fsem02ExplicitPeerPairRetiresExactlyBothAndFrames
    owners peerOccurrence peerProcess peerEndpoint afterPeer
    clientOccurrence clientProcess clientEndpoint afterReverse
    HreverseDistinct HpeerFirst HclientSecond)
    as [HreversePeer [HreverseClient HreverseFrame]].
  destruct (string_dec observed clientOccurrence) as [HclientKey|HnotClient].
  - subst observed. now rewrite HforwardClient, HreverseClient.
  - destruct (string_dec observed peerOccurrence) as [HpeerKey|HnotPeer].
    + subst observed. now rewrite HforwardPeer, HreversePeer.
    + rewrite (HforwardFrame observed HnotClient HnotPeer).
      symmetry. apply HreverseFrame; assumption.
Qed.
