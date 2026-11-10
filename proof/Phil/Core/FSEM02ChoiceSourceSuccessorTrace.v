From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ExplicitPeerClose
  FSEM02TerminalCloseDiamond.

(*
  FSEM-02 NON-NORMATIVE: conditional source-select/offer owner trace from
  ORIGINAL predecessor through two externally authorized End orders.
  The parsed source/protocol family, selected peer label, external Server
  continuation identity and End outcomes, exact activation and process
  occurrence identities, and every successful step are explicit premises.
  Neither full Haskell-to-Rocq implementation refinement nor source Server
  disposition, architecture/root/assurance authority is established.
*)

Theorem fsem02ChoiceSourceSuccessorTraceThroughBothClosures :
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
    fsem02JointSourceChoice sourceLabels branches chosen peer
      clientOld clientNext offerOld offerNext clientContext offerContext =
      Some (clientReady, offerReady) /\
    afterChoice clientOccurrence = Some (clientProcess, clientNext) /\
    afterChoice offerOccurrence = Some (offerProcess, offerNext) /\
    afterForward clientOccurrence = None /\
    afterForward offerOccurrence = None /\
    (forall spectator,
      spectator <> clientOccurrence ->
      spectator <> offerOccurrence ->
      afterForward spectator = owners spectator /\
      afterReverse spectator = owners spectator) /\
    (forall observed, afterForward observed = afterReverse observed).
Proof.
  intros sourceLabels branches chosen peer clientOld clientNext
    offerOld offerNext clientContext offerContext owners
    clientOccurrence offerOccurrence clientProcess offerProcess
    clientReady offerReady afterChoice afterClient afterForward
    afterPeer afterReverse Hdistinct Hchoice HclientClose HpeerClose
    HpeerFirst HclientSecond.
  pose proof (fsem02StatefulSourceChoiceSuccessIsJointAndExactOwners
    sourceLabels branches chosen peer clientOld clientNext offerOld offerNext
    clientContext offerContext owners clientOccurrence offerOccurrence
    clientProcess offerProcess clientReady offerReady afterChoice Hchoice)
    as [Hjoint [HclientNext [HofferNext HoriginalFrame]]].
  pose proof (fsem02ExplicitPeerPairRetiresExactlyBothAndFrames
    afterChoice clientOccurrence clientProcess clientNext afterClient
    offerOccurrence offerProcess offerNext afterForward
    Hdistinct HclientClose HpeerClose)
    as [HclientGone [HofferGone HcloseFrame]].
  pose proof (fsem02ConditionalTerminalCloseDiamond
    afterChoice clientOccurrence clientProcess clientNext
    offerOccurrence offerProcess offerNext
    afterClient afterForward afterPeer afterReverse
    Hdistinct HclientClose HpeerClose HpeerFirst HclientSecond)
    as Hdiamond.
  repeat (apply conj).
  - exact Hjoint.
  - exact HclientNext.
  - exact HofferNext.
  - exact HclientGone.
  - exact HofferGone.
  - intros spectator HnotClient HnotOffer.
    split.
    + rewrite (HcloseFrame spectator HnotClient HnotOffer).
      apply HoriginalFrame; assumption.
    + rewrite <- (Hdiamond spectator).
      rewrite (HcloseFrame spectator HnotClient HnotOffer).
      apply HoriginalFrame; assumption.
  - exact Hdiamond.
Qed.

Theorem fsem02ChoiceSourceSuccessorTraceRetiredPeerCannotCloseAgain :
  forall afterForward offerOccurrence offerProcess offerNext,
    afterForward offerOccurrence = None ->
    fsem02RetireExplicitPeerEnd afterForward
      offerOccurrence offerProcess offerNext = None.
Proof.
  intros afterForward offerOccurrence offerProcess offerNext Hretired.
  apply fsem02ExplicitPeerCloseRejectsMissingOwner.
  exact Hretired.
Qed.

Theorem fsem02ChoiceSourceSuccessorTraceRejectsAliasedOwners :
  forall owners occurrence clientProcess offerProcess
         clientOld clientNext offerOld offerNext,
    fsem02AdvanceChoiceOwners owners occurrence occurrence
      clientProcess offerProcess clientOld clientNext offerOld offerNext = None.
Proof.
  intros.
  apply fsem02AdvanceChoiceOwnersRejectsAliasedOccurrence.
Qed.
