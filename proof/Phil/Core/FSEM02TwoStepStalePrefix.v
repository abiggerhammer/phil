From Stdlib Require Import Strings.String.
From Phil.Core Require Import
  Context FSEM02PairedLocalJointBridge FSEM02PairedChoiceJointBridge
  FSEM02PairedSourceFamilyEnvelope FSEM02PairedTwoStepOutcomes.

(*
 FSEM-02 NON-NORMATIVE: finite cross-family stale-prefix refusal.
 The first admitted step may be either Ping or Choice, but a later
 Ping cannot reuse a consumed sender or receiver predecessor.
 All source/rendezvous admission and continuing-head hypotheses remain
 independent external inputs; no source-derived protocol authority,
 error-priority refinement or general Haskell Map/Set simulation follows.
*)

Theorem fsem02SuccessfulRequestConsumesBothExactPredecessors :
  forall request beforeSender beforeReceiver afterSender afterReceiver
         senderContinuation receiverContinuation choiceContinuation,
    fsem02RequestContinuations request
      senderContinuation receiverContinuation choiceContinuation ->
    fsem02ReplayRequest request (beforeSender, beforeReceiver) =
      Some (afterSender, afterReceiver) ->
    linearBindings afterSender (fsem02ReqSenderOld request) = None /\
    linearBindings afterReceiver (fsem02ReqReceiverOld request) = None.
Proof.
  intros request beforeSender beforeReceiver afterSender afterReceiver
    senderContinuation receiverContinuation choiceContinuation
    [Hping Hchoice] Hsuccess.
  unfold fsem02ReplayRequest, fsem02PairedSourceFamilyReplay in Hsuccess.
  destruct (fsem02PairedFamilyGuard
    (fsem02ReqFamily request)
    (fsem02ReqSenderAction request)
    (fsem02ReqReceiverAction request)
    (fsem02ReqChosen request)
    (fsem02ReqPeer request)) eqn:Hshape; [|discriminate].
  destruct (fsem02ReqFamily request) eqn:Hfamily.
  - destruct (Hping Hfamily) as [Hsend Hreceive].
    eapply fsem02PairedReplaySuccessExact in Hsuccess;
      [|exact Hsend|exact Hreceive].
    destruct Hsuccess as [_ [_ [HsenderGone [_ [HreceiverGone _]]]]].
    split; assumption.
  - pose proof (Hchoice Hfamily) as Hoffered.
    eapply fsem02PairedChoiceSuccessExact in Hsuccess;
      [|exact Hoffered].
    destruct Hsuccess as [_ [_ [_ [HsenderGone [_ [HreceiverGone _]]]]]].
    split; assumption.
Qed.

Theorem fsem02TwoStepStaleSenderPingRefusesWithoutRollback :
  forall first second beforeSender beforeReceiver afterSender afterReceiver
         senderContinuation receiverContinuation choiceContinuation,
    fsem02RequestContinuations first
      senderContinuation receiverContinuation choiceContinuation ->
    fsem02ReqFamily second = FSEM02PairedPing ->
    fsem02ReqSenderOld second = fsem02ReqSenderOld first ->
    fsem02ReplayRequest first (beforeSender, beforeReceiver) =
      Some (afterSender, afterReceiver) ->
    fsem02PairedTwoStepReplay first second (beforeSender, beforeReceiver) =
      FSEM02SecondRefused (afterSender, afterReceiver).
Proof.
  intros first second beforeSender beforeReceiver afterSender afterReceiver
    senderContinuation receiverContinuation choiceContinuation
    Hheads Hfamily Hsame Hfirst.
  pose proof (fsem02SuccessfulRequestConsumesBothExactPredecessors
    first beforeSender beforeReceiver afterSender afterReceiver
    senderContinuation receiverContinuation choiceContinuation Hheads Hfirst)
    as [HsenderGone _].
  apply fsem02TwoStepRejectedSuffixRetainsCommittedPrefix.
  - exact Hfirst.
  - unfold fsem02ReplayRequest.
    simpl.
    rewrite Hfamily.
    eapply fsem02FamilyPingMissingFirstPredecessorRejects.
    rewrite Hsame.
    exact HsenderGone.
Qed.

Theorem fsem02TwoStepStaleReceiverPingRefusesWithoutRollback :
  forall first second beforeSender beforeReceiver afterSender afterReceiver
         senderContinuation receiverContinuation choiceContinuation,
    fsem02RequestContinuations first
      senderContinuation receiverContinuation choiceContinuation ->
    fsem02ReqFamily second = FSEM02PairedPing ->
    fsem02ReqReceiverOld second = fsem02ReqReceiverOld first ->
    fsem02ReplayRequest first (beforeSender, beforeReceiver) =
      Some (afterSender, afterReceiver) ->
    fsem02PairedTwoStepReplay first second (beforeSender, beforeReceiver) =
      FSEM02SecondRefused (afterSender, afterReceiver).
Proof.
  intros first second beforeSender beforeReceiver afterSender afterReceiver
    senderContinuation receiverContinuation choiceContinuation
    Hheads Hfamily Hsame Hfirst.
  pose proof (fsem02SuccessfulRequestConsumesBothExactPredecessors
    first beforeSender beforeReceiver afterSender afterReceiver
    senderContinuation receiverContinuation choiceContinuation Hheads Hfirst)
    as [_ HreceiverGone].
  apply fsem02TwoStepRejectedSuffixRetainsCommittedPrefix.
  - exact Hfirst.
  - unfold fsem02ReplayRequest.
    simpl.
    rewrite Hfamily.
    eapply fsem02FamilyPingMissingSecondPredecessorRejects.
    rewrite Hsame.
    exact HreceiverGone.
Qed.
