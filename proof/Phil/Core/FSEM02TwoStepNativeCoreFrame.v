From Stdlib Require Import Strings.String.
From Phil.Core Require Import
  Context FSEM02PairedTwoStepOutcomes FSEM02TwoStepStalePrefix
  FSEM02TwoStepSuccessorChain.

(*
  FSEM-02 NON-NORMATIVE: conditional two-generation extensional observation.
  Pair a previously established exact predecessor-consumption theorem with
  two-peer shared-loan / disjoint-spectator frame preservation. Native
  Core.Protocol two-step transitions are independently tested, not proved
  generally equivalent to this model. All source/activation/authority and
  exact chaining/continuation admissions remain premises.
*)

Theorem fsem02TwoStepChainedOwnersAndSpectators :
  forall first second beforeSender beforeReceiver
         middleSender middleReceiver finalSender finalReceiver
         sender1 receiver1 choice1 sender2 receiver2 choice2,
    fsem02RequestContinuations first sender1 receiver1 choice1 ->
    fsem02RequestContinuations second sender2 receiver2 choice2 ->
    fsem02ReqSenderOld second = fsem02ReqSenderNext first ->
    fsem02ReqReceiverOld second = fsem02ReqReceiverNext first ->
    fsem02PairedTwoStepReplay first second
      (beforeSender, beforeReceiver) =
      FSEM02BothAccepted
        (middleSender, middleReceiver) (finalSender, finalReceiver) ->
    sharedLoans finalSender = sharedLoans beforeSender /\
    sharedLoans finalReceiver = sharedLoans beforeReceiver /\
    linearBindings middleSender (fsem02ReqSenderOld first) = None /\
    linearBindings middleReceiver (fsem02ReqReceiverOld first) = None /\
    linearBindings finalSender (fsem02ReqSenderNext first) = None /\
    linearBindings finalReceiver (fsem02ReqReceiverNext first) = None /\
    (forall spectator,
      String.eqb spectator (fsem02ReqSenderOld first) = false ->
      String.eqb spectator (fsem02ReqSenderNext first) = false ->
      String.eqb spectator (fsem02ReqSenderOld second) = false ->
      String.eqb spectator (fsem02ReqSenderNext second) = false ->
      linearBindings finalSender spectator = linearBindings beforeSender spectator) /\
    (forall spectator,
      String.eqb spectator (fsem02ReqReceiverOld first) = false ->
      String.eqb spectator (fsem02ReqReceiverNext first) = false ->
      String.eqb spectator (fsem02ReqReceiverOld second) = false ->
      String.eqb spectator (fsem02ReqReceiverNext second) = false ->
      linearBindings finalReceiver spectator = linearBindings beforeReceiver spectator).
Proof.
  intros first second beforeSender beforeReceiver
    middleSender middleReceiver finalSender finalReceiver
    sender1 receiver1 choice1 sender2 receiver2 choice2
    Hheads1 Hheads2 HsenderChain HreceiverChain Hboth.
  pose proof (fsem02TwoStepChainedSuccessConsumesBothGenerations
    first second beforeSender beforeReceiver middleSender middleReceiver
    finalSender finalReceiver
    sender1 receiver1 choice1 sender2 receiver2 choice2
    Hheads1 Hheads2 HsenderChain HreceiverChain Hboth)
    as [HoldS [HoldR [HnextS HnextR]]].
  apply fsem02TwoStepSuccessExact in Hboth.
  destruct Hboth as [Hfirst Hsecond].
  pose proof (fsem02TwoStepSuccessFramesTwoLoansAndDisjointSpectators
    first second beforeSender beforeReceiver middleSender middleReceiver
    finalSender finalReceiver
    sender1 receiver1 choice1 sender2 receiver2 choice2
    Hheads1 Hheads2 Hfirst Hsecond)
    as [HloanS [HloanR [HframeS HframeR]]].
  repeat split; assumption.
Qed.
