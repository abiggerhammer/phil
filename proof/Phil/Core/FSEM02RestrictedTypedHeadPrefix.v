From Stdlib Require Import Strings.String Bool.Bool.
From Phil.Core Require Import Syntax FSEM02RestrictedTerminalHeads
  FSEM02RestrictedClosePrefixLedgers FSEM02SelectedClientClose
  FSEM02ExplicitPeerClose.

(*
  FSEM-02 NON-NORMATIVE: a typed terminal Send/Receive head gate is composed
  with the two separately authorized first-End owner prefixes. The admitted
  source, boundary/message authority, independent activation occurrences,
  terminal End outcomes, and the two actual first-close transitions are all
  premises. Native Haskell independently replays BOTH from original state.
  This is NOT a source-to-Rocq refinement theorem, source disposal authority,
  an assurance claim, or a global progress/fairness theorem.
*)
Theorem fsem02TypedHeadGateComposesWithBothClosePrefixes :
  forall sourceAccepted messageAdmitted
         senderSend receiverReceive senderEndMatch receiverEndMatch
         (owners : FSEM02OwnerLedger)
         senderOccurrence receiverOccurrence payloadOccurrence
         senderProcess receiverProcess
         senderOld senderNext receiverOld receiverNext payloadOld payloadNext
         afterTransfer afterSender afterForward afterReceiver afterReverse,
    senderOccurrence <> receiverOccurrence ->
    payloadOccurrence <> senderOccurrence ->
    payloadOccurrence <> receiverOccurrence ->
    fsem02RestrictedTerminalHeadAdvance
      sourceAccepted messageAdmitted senderSend receiverReceive
      senderEndMatch receiverEndMatch owners
      senderOccurrence receiverOccurrence payloadOccurrence
      senderProcess receiverProcess
      senderOld senderNext receiverOld receiverNext payloadOld payloadNext =
      Some afterTransfer ->
    fsem02RetireSelectedClientOwner afterTransfer senderOccurrence
      senderProcess senderNext = Some afterSender ->
    fsem02RetireExplicitPeerEnd afterSender receiverOccurrence
      receiverProcess receiverNext = Some afterForward ->
    fsem02RetireExplicitPeerEnd afterTransfer receiverOccurrence
      receiverProcess receiverNext = Some afterReceiver ->
    fsem02RetireSelectedClientOwner afterReceiver senderOccurrence
      senderProcess senderNext = Some afterReverse ->
    (senderSend = true /\ receiverReceive = true /\
     senderEndMatch = true /\ receiverEndMatch = true) /\
    (afterSender senderOccurrence = None /\
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
     (forall observed, afterForward observed = afterReverse observed)).
Proof.
  intros sourceAccepted messageAdmitted
    senderSend receiverReceive senderEndMatch receiverEndMatch
    owners sc rc pc sp rp so sn ro rn po pn
    afterTransfer afterSender afterForward afterReceiver afterReverse
    Hdistinct HpayloadSender HpayloadReceiver Hhead
    Hsender Hforward Hreceiver Hreverse.
  pose proof (fsem02RestrictedTerminalHeadSuccessExact
    sourceAccepted messageAdmitted
    senderSend receiverReceive senderEndMatch receiverEndMatch
    owners sc rc pc sp rp so sn ro rn po pn afterTransfer Hhead)
    as [Hs [Hr [HeS [HeR _]]]].
  unfold fsem02RestrictedTerminalHeadAdvance in Hhead.
  rewrite Hs, Hr, HeS, HeR in Hhead.
  simpl in Hhead.
  pose proof (fsem02RestrictedSourceBothOneSidedClosePrefixes
    sourceAccepted messageAdmitted true owners
    sc rc pc sp rp so sn ro rn po pn
    afterTransfer afterSender afterForward afterReceiver afterReverse
    Hdistinct HpayloadSender HpayloadReceiver Hhead
    Hsender Hforward Hreceiver Hreverse) as Hprefixes.
  split.
  - repeat split; assumption.
  - exact Hprefixes.
Qed.

Theorem fsem02TypedHeadWrongSenderCannotExposePrefix :
  forall sourceAccepted messageAdmitted receiverReceive
    senderEndMatch receiverEndMatch owners sc rc pc sp rp so sn ro rn po pn,
    fsem02RestrictedTerminalHeadAdvance
      sourceAccepted messageAdmitted false receiverReceive
      senderEndMatch receiverEndMatch owners
      sc rc pc sp rp so sn ro rn po pn = None.
Proof.
  intros.
  apply fsem02RestrictedTerminalHeadNoSenderHead.
Qed.

Theorem fsem02TypedHeadWrongReceiverCannotExposePrefix :
  forall sourceAccepted messageAdmitted senderSend
    senderEndMatch receiverEndMatch owners sc rc pc sp rp so sn ro rn po pn,
    fsem02RestrictedTerminalHeadAdvance
      sourceAccepted messageAdmitted senderSend false
      senderEndMatch receiverEndMatch owners
      sc rc pc sp rp so sn ro rn po pn = None.
Proof.
  intros.
  apply fsem02RestrictedTerminalHeadNoReceiverHead.
Qed.
