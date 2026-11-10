From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02RestrictedSourceTransfer FSEM02SelectedClientClose
  FSEM02ExplicitPeerClose FSEM02RestrictedCloseDiamond.

(*
  FSEM-02 NON-NORMATIVE, finite end-to-end source successor owner trace.
  Source acceptance, concrete protocol/message admission, dual heads, exact
  activation occurrence identities and End close authorizations are EXTERNAL
  premises. Haskell independently rechecks the source and original Core state.
  Neither parser correctness nor Haskell-to-Rocq refinement is proved.
*)

Theorem fsem02RestrictedSuccessorTraceFromPredecessorToBothClosures :
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
    sourceAccepted = true /\
    messageAdmitted = true /\
    headsValid = true /\
    owners payloadOccurrence = Some (senderProcess, payloadOld) /\
    afterTransfer senderOccurrence = Some (senderProcess, senderNext) /\
    afterTransfer receiverOccurrence = Some (receiverProcess, receiverNext) /\
    afterForward senderOccurrence = None /\
    afterForward receiverOccurrence = None /\
    afterForward payloadOccurrence = Some (receiverProcess, payloadNext) /\
    afterReverse payloadOccurrence = Some (receiverProcess, payloadNext) /\
    (forall spectator,
       spectator <> payloadOccurrence ->
       spectator <> senderOccurrence ->
       spectator <> receiverOccurrence ->
       afterForward spectator = owners spectator /\
       afterReverse spectator = owners spectator) /\
    (forall observed, afterForward observed = afterReverse observed).
Proof.
  intros sourceAccepted messageAdmitted headsValid owners
    senderOccurrence receiverOccurrence payloadOccurrence
    senderProcess receiverProcess
    senderOld senderNext receiverOld receiverNext payloadOld payloadNext
    afterTransfer afterSender afterForward afterReceiver afterReverse
    Hdistinct HpayloadSender HpayloadReceiver Htransfer
    HsenderClose HreceiverClose HreceiverFirst HsenderSecond.
  pose proof (fsem02RestrictedSourceSuccessExactAndFrame
    sourceAccepted messageAdmitted headsValid owners
    senderOccurrence receiverOccurrence payloadOccurrence
    senderProcess receiverProcess
    senderOld senderNext receiverOld receiverNext payloadOld payloadNext
    afterTransfer Htransfer)
    as [Hsource [Hmessage [Hheads [HpayloadBefore
      [HpayloadAfter [HsenderNext [HreceiverNext HtransferFrame]]]]]]].
  pose proof (fsem02RestrictedCloseOrderDiamondPayloadAndFrame
    afterTransfer senderOccurrence receiverOccurrence payloadOccurrence
    senderProcess receiverProcess senderNext receiverNext payloadNext
    afterSender afterForward afterReceiver afterReverse
    Hdistinct HpayloadSender HpayloadReceiver HpayloadAfter
    HsenderClose HreceiverClose HreceiverFirst HsenderSecond)
    as [HsenderGone [HreceiverGone [HforwardPayload
      [HreversePayload [HcloseFrame Hdiamond]]]]].
  repeat split.
  - exact Hsource.
  - exact Hmessage.
  - exact Hheads.
  - exact HpayloadBefore.
  - exact HsenderNext.
  - exact HreceiverNext.
  - exact HsenderGone.
  - exact HreceiverGone.
  - exact HforwardPayload.
  - exact HreversePayload.
  - intros spectator HnotPayload HnotSender HnotReceiver.
    split.
    + rewrite (HcloseFrame spectator HnotSender HnotReceiver).
      apply HtransferFrame; assumption.
    + rewrite <- (Hdiamond spectator).
      rewrite (HcloseFrame spectator HnotSender HnotReceiver).
      apply HtransferFrame; assumption.
  - exact Hdiamond.
Qed.

(* Once a proven successor is retired, an additional End close of that
   occurrence cannot succeed. This does not prove termination of the process. *)
Theorem fsem02RestrictedSuccessorTraceRejectsRetiredSender :
  forall afterForward senderOccurrence senderProcess senderNext,
    afterForward senderOccurrence = None ->
    fsem02RetireSelectedClientOwner afterForward
      senderOccurrence senderProcess senderNext = None.
Proof.
  intros afterForward senderOccurrence senderProcess senderNext Hgone.
  apply fsem02SelectedClientCloseRejectsMissingOwner.
  exact Hgone.
Qed.

Theorem fsem02RestrictedSuccessorTraceRejectsUnacceptedSource :
  forall messageAdmitted headsValid owners
         senderOccurrence receiverOccurrence payloadOccurrence
         senderProcess receiverProcess
         senderOld senderNext receiverOld receiverNext payloadOld payloadNext,
    fsem02RestrictedSourceTransfer
      false messageAdmitted headsValid owners
      senderOccurrence receiverOccurrence payloadOccurrence
      senderProcess receiverProcess senderOld senderNext
      receiverOld receiverNext payloadOld payloadNext = None.
Proof.
  intros.
  apply fsem02RestrictedSourceRejectsUnadmitted.
Qed.
