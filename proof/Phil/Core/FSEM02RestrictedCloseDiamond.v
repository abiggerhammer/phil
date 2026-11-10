From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ExplicitPeerClose
  FSEM02TerminalCloseDiamond FSEM02RestrictedSourceTransfer.

(*
  Bounded, NON-NORMATIVE FSEM-02 restricted send/receive terminal diamond.
  The exact checked source send/receive, accepted restricted message boundary,
  live protocol heads, original activation index, distinct owners, external
  End outcomes and success of both individual orders are PREMISES.
  The transferred payload already belongs to the receiver in 'owners'.
  Both endpoint closes must retire only endpoint occurrences; the payload
  remains owned, not implicitly disposed. This proves extensional Rocq owner
  ledger equality, NOT native Haskell/Core refinement, process completion,
  root validity, effects, assurance, scheduling or Phase 1 normativity.
*)

Theorem fsem02RestrictedCloseOrderDiamondPayloadAndFrame :
  forall owners senderOccurrence receiverOccurrence payloadOccurrence
         senderProcess receiverProcess
         senderEnd receiverEnd payloadName
         afterSender afterForward afterReceiver afterReverse,
    senderOccurrence <> receiverOccurrence ->
    payloadOccurrence <> senderOccurrence ->
    payloadOccurrence <> receiverOccurrence ->
    owners payloadOccurrence = Some (receiverProcess, payloadName) ->
    fsem02RetireSelectedClientOwner owners
      senderOccurrence senderProcess senderEnd = Some afterSender ->
    fsem02RetireExplicitPeerEnd afterSender
      receiverOccurrence receiverProcess receiverEnd = Some afterForward ->
    fsem02RetireExplicitPeerEnd owners
      receiverOccurrence receiverProcess receiverEnd = Some afterReceiver ->
    fsem02RetireSelectedClientOwner afterReceiver
      senderOccurrence senderProcess senderEnd = Some afterReverse ->
    afterForward senderOccurrence = None /\
    afterForward receiverOccurrence = None /\
    afterForward payloadOccurrence = Some (receiverProcess, payloadName) /\
    afterReverse payloadOccurrence = Some (receiverProcess, payloadName) /\
    (forall spectator,
       spectator <> senderOccurrence ->
       spectator <> receiverOccurrence ->
       afterForward spectator = owners spectator) /\
    (forall observed, afterForward observed = afterReverse observed).
Proof.
  intros owners senderOccurrence receiverOccurrence payloadOccurrence
    senderProcess receiverProcess senderEnd receiverEnd payloadName
    afterSender afterForward afterReceiver afterReverse
    Hdistinct HpayloadSender HpayloadReceiver HpayloadOwner
    Hsender Hreceiver HreceiverFirst HsenderSecond.
  pose proof (fsem02ExplicitPeerPairRetiresExactlyBothAndFrames
    owners senderOccurrence senderProcess senderEnd afterSender
    receiverOccurrence receiverProcess receiverEnd afterForward
    Hdistinct Hsender Hreceiver) as [HsenderGone [HreceiverGone Hframe]].
  pose proof (fsem02ConditionalTerminalCloseDiamond
    owners senderOccurrence senderProcess senderEnd
    receiverOccurrence receiverProcess receiverEnd
    afterSender afterForward afterReceiver afterReverse
    Hdistinct Hsender Hreceiver HreceiverFirst HsenderSecond)
    as Hdiamond.
  repeat split.
  - exact HsenderGone.
  - exact HreceiverGone.
  - rewrite (Hframe payloadOccurrence HpayloadSender HpayloadReceiver).
    exact HpayloadOwner.
  - rewrite <- (Hdiamond payloadOccurrence).
    rewrite (Hframe payloadOccurrence HpayloadSender HpayloadReceiver).
    exact HpayloadOwner.
  - exact Hframe.
  - exact Hdiamond.
Qed.

Theorem fsem02RestrictedCloseOrderRejectsStaleReceiver :
  forall owners receiverOccurrence receiverProcess receiverEnd,
    owners receiverOccurrence = None ->
    fsem02RetireExplicitPeerEnd owners
      receiverOccurrence receiverProcess receiverEnd = None.
Proof.
  intros owners receiverOccurrence receiverProcess receiverEnd Hmissing.
  exact (fsem02ExplicitPeerCloseRejectsMissingOwner
    owners receiverOccurrence receiverProcess receiverEnd Hmissing).
Qed.
