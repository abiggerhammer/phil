From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax
  FSEM02RestrictedSourceTransfer FSEM02SelectedClientClose
  FSEM02ExplicitPeerClose FSEM02RestrictedCloseDiamond.

(*
  FSEM-02 NON-NORMATIVE: complete owner-ledger observations after either
  first End retirement of a restricted send/receive. Success of the admitted
  source, concrete message, checked protocol heads, exact distinct activation
  occurrences, and BOTH externally authorized close orders are premises.
  Payload and spectators remain owned while only the selected End endpoint
  retires. Haskell independently tests real Core state transitions. This is
  NOT a source interpreter, native-to-Rocq refinement, endpoint-disposal
  authority, selected-root certification, fairness, or assurance discharge.
*)

Theorem fsem02RestrictedSourceBothOneSidedClosePrefixes :
  forall sourceAccepted messageAdmitted headsValid owners
         senderOccurrence receiverOccurrence payloadOccurrence
         senderProcess receiverProcess
         senderOld senderNext receiverOld receiverNext payloadOld payloadNext
         afterTransfer afterSender afterForward afterReceiver afterReverse,
    senderOccurrence <> receiverOccurrence ->
    payloadOccurrence <> senderOccurrence ->
    payloadOccurrence <> receiverOccurrence ->
    fsem02RestrictedSourceTransfer
      sourceAccepted messageAdmitted headsValid owners
      senderOccurrence receiverOccurrence payloadOccurrence
      senderProcess receiverProcess senderOld senderNext
      receiverOld receiverNext payloadOld payloadNext = Some afterTransfer ->
    fsem02RetireSelectedClientOwner afterTransfer
      senderOccurrence senderProcess senderNext = Some afterSender ->
    fsem02RetireExplicitPeerEnd afterSender
      receiverOccurrence receiverProcess receiverNext = Some afterForward ->
    fsem02RetireExplicitPeerEnd afterTransfer
      receiverOccurrence receiverProcess receiverNext = Some afterReceiver ->
    fsem02RetireSelectedClientOwner afterReceiver
      senderOccurrence senderProcess senderNext = Some afterReverse ->
    afterSender senderOccurrence = None /\
    afterSender receiverOccurrence = Some (receiverProcess, receiverNext) /\
    afterSender payloadOccurrence = Some (receiverProcess, payloadNext) /\
    afterReceiver senderOccurrence = Some (senderProcess, senderNext) /\
    afterReceiver receiverOccurrence = None /\
    afterReceiver payloadOccurrence = Some (receiverProcess, payloadNext) /\
    (forall spectator,
       spectator <> payloadOccurrence ->
       spectator <> senderOccurrence ->
       spectator <> receiverOccurrence ->
       afterSender spectator = owners spectator /\
       afterReceiver spectator = owners spectator) /\
    (forall observed, afterForward observed = afterReverse observed).
Proof.
  intros sourceAccepted messageAdmitted headsValid owners
    senderOccurrence receiverOccurrence payloadOccurrence
    senderProcess receiverProcess
    senderOld senderNext receiverOld receiverNext payloadOld payloadNext
    afterTransfer afterSender afterForward afterReceiver afterReverse
    Hdistinct HpayloadSender HpayloadReceiver Htransfer
    Hsender Hforward Hreceiver Hreverse.
  pose proof (fsem02RestrictedSourceSuccessExactAndFrame
    sourceAccepted messageAdmitted headsValid owners
    senderOccurrence receiverOccurrence payloadOccurrence
    senderProcess receiverProcess
    senderOld senderNext receiverOld receiverNext payloadOld payloadNext
    afterTransfer Htransfer)
    as [_ [_ [_ [_ [HpayloadReady
       [HsenderReady [HreceiverReady HtransferFrame]]]]]]].
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    afterTransfer senderOccurrence senderProcess senderNext afterSender
    Hsender) as [HsenderGone HsenderFrame].
  unfold fsem02RetireExplicitPeerEnd in Hreceiver.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    afterTransfer receiverOccurrence receiverProcess receiverNext
    afterReceiver Hreceiver) as [HreceiverGone HreceiverFrame].
  assert (HreverseDistinct : receiverOccurrence <> senderOccurrence).
  { intro Heq. apply Hdistinct. symmetry. exact Heq. }
  pose proof (fsem02RestrictedCloseOrderDiamondPayloadAndFrame
    afterTransfer senderOccurrence receiverOccurrence payloadOccurrence
    senderProcess receiverProcess senderNext receiverNext payloadNext
    afterSender afterForward afterReceiver afterReverse
    Hdistinct HpayloadSender HpayloadReceiver HpayloadReady
    Hsender Hforward Hreceiver Hreverse)
    as [_ [_ [_ [_ [_ Hdiamond]]]]].
  repeat (apply conj).
  - exact HsenderGone.
  - rewrite (HsenderFrame receiverOccurrence HreverseDistinct).
    exact HreceiverReady.
  - rewrite (HsenderFrame payloadOccurrence HpayloadSender).
    exact HpayloadReady.
  - rewrite (HreceiverFrame senderOccurrence Hdistinct).
    exact HsenderReady.
  - exact HreceiverGone.
  - rewrite (HreceiverFrame payloadOccurrence HpayloadReceiver).
    exact HpayloadReady.
  - intros spectator HnotPayload HnotSender HnotReceiver.
    split.
    + rewrite (HsenderFrame spectator HnotSender).
      apply HtransferFrame; assumption.
    + rewrite (HreceiverFrame spectator HnotReceiver).
      apply HtransferFrame; assumption.
  - exact Hdiamond.
Qed.

Theorem fsem02RestrictedSenderPrefixCannotRetireTwice :
  forall owners occurrence process endpoint after,
    fsem02RetireSelectedClientOwner owners occurrence process endpoint =
      Some after ->
    fsem02RetireSelectedClientOwner after occurrence process endpoint = None.
Proof.
  intros owners occurrence process endpoint after Hstep.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    owners occurrence process endpoint after Hstep) as [Hgone _].
  now apply fsem02SelectedClientCloseRejectsMissingOwner.
Qed.

Theorem fsem02RestrictedReceiverPrefixCannotRetireTwice :
  forall owners occurrence process endpoint after,
    fsem02RetireExplicitPeerEnd owners occurrence process endpoint =
      Some after ->
    fsem02RetireExplicitPeerEnd after occurrence process endpoint = None.
Proof.
  intros owners occurrence process endpoint after Hstep.
  exact (fsem02ExplicitPeerCannotCloseSameOwnerTwice
    owners occurrence process endpoint after Hstep).
Qed.
