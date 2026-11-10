From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ExplicitPeerClose
  FSEM02TerminalCloseDiamond.

(* FSEM-02 NON-NORMATIVE: distinct nominal owners, successful source choice,
   and both independently authorized terminal End orders are premises.
   Only the modeled finite owner ledger is proved, not Haskell representation,
   source Server disposition, root validity, scheduler or assurance authority. *)
Theorem fsem02ChoiceSourceBothOneSidedClosePrefixes :
  forall sourceLabels branches chosen peer clientOld clientNext
         offerOld offerNext clientContext offerContext owners
         clientOccurrence offerOccurrence clientProcess offerProcess
         clientReady offerReady afterChoice afterClient afterForward
         afterPeer afterReverse,
    clientOccurrence <> offerOccurrence ->
    fsem02StatefulSourceChoice sourceLabels branches chosen peer
      clientOld clientNext offerOld offerNext clientContext offerContext
      owners clientOccurrence offerOccurrence clientProcess offerProcess =
      Some ((clientReady, offerReady), afterChoice) ->
    fsem02RetireSelectedClientOwner afterChoice
      clientOccurrence clientProcess clientNext = Some afterClient ->
    fsem02RetireExplicitPeerEnd afterClient
      offerOccurrence offerProcess offerNext = Some afterForward ->
    fsem02RetireExplicitPeerEnd afterChoice
      offerOccurrence offerProcess offerNext = Some afterPeer ->
    fsem02RetireSelectedClientOwner afterPeer
      clientOccurrence clientProcess clientNext = Some afterReverse ->
    afterClient clientOccurrence = None /\
    afterClient offerOccurrence = Some (offerProcess, offerNext) /\
    afterPeer clientOccurrence = Some (clientProcess, clientNext) /\
    afterPeer offerOccurrence = None /\
    (forall spectator,
      spectator <> clientOccurrence ->
      spectator <> offerOccurrence ->
      afterClient spectator = owners spectator /\
      afterPeer spectator = owners spectator) /\
    (forall observed, afterForward observed = afterReverse observed).
Proof.
  intros sourceLabels branches chosen peer clientOld clientNext
    offerOld offerNext clientContext offerContext owners
    clientOccurrence offerOccurrence clientProcess offerProcess
    clientReady offerReady afterChoice afterClient afterForward
    afterPeer afterReverse Hdistinct Hchoice Hclient Hpeer HpeerFirst HclientSecond.
  pose proof (fsem02StatefulSourceChoiceSuccessIsJointAndExactOwners
    sourceLabels branches chosen peer clientOld clientNext offerOld offerNext
    clientContext offerContext owners clientOccurrence offerOccurrence
    clientProcess offerProcess clientReady offerReady afterChoice Hchoice)
    as [_ [HclientReady [HofferReady HinitialFrame]]].
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    afterChoice clientOccurrence clientProcess clientNext afterClient Hclient)
    as [HclientGone HclientFrame].
  unfold fsem02RetireExplicitPeerEnd in HpeerFirst.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    afterChoice offerOccurrence offerProcess offerNext afterPeer HpeerFirst)
    as [HpeerGone HpeerFrame].
  assert (HofferDistinct : offerOccurrence <> clientOccurrence).
  { intro Heq. apply Hdistinct. symmetry. exact Heq. }
  pose proof (fsem02ConditionalTerminalCloseDiamond
    afterChoice clientOccurrence clientProcess clientNext
    offerOccurrence offerProcess offerNext
    afterClient afterForward afterPeer afterReverse
    Hdistinct Hclient Hpeer HpeerFirst HclientSecond) as Hdiamond.
  repeat split.
  - exact HclientGone.
  - rewrite (HclientFrame offerOccurrence HofferDistinct).
    exact HofferReady.
  - rewrite (HpeerFrame clientOccurrence Hdistinct).
    exact HclientReady.
  - exact HpeerGone.
  - intros spectator HnotClient HnotOffer.
    split.
    + rewrite (HclientFrame spectator HnotClient).
      apply HinitialFrame; assumption.
    + rewrite (HpeerFrame spectator HnotOffer).
      apply HinitialFrame; assumption.
  - exact Hdiamond.
Qed.

(* Exact stale-prefix refusals: the retired occurrence is absent. *)
Theorem fsem02ChoiceClientFirstPrefixCannotReuseRetiredOwner :
  forall before occurrence process endpoint after,
    fsem02RetireSelectedClientOwner before occurrence
      process endpoint = Some after ->
    fsem02RetireSelectedClientOwner after occurrence
      process endpoint = None.
Proof.
  intros before occurrence process endpoint after Hstep.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    before occurrence process endpoint after Hstep) as [Hgone _].
  apply fsem02SelectedClientCloseRejectsMissingOwner. exact Hgone.
Qed.

Theorem fsem02ChoicePeerFirstPrefixCannotReuseRetiredOwner :
  forall before occurrence process endpoint after,
    fsem02RetireExplicitPeerEnd before occurrence
      process endpoint = Some after ->
    fsem02RetireExplicitPeerEnd after occurrence
      process endpoint = None.
Proof.
  intros before occurrence process endpoint after Hstep.
  eapply fsem02ExplicitPeerCannotCloseSameOwnerTwice.
  exact Hstep.
Qed.
