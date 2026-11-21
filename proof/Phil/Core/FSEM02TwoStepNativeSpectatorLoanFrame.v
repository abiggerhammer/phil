From Stdlib Require Import Strings.String.
From Phil.Core Require Import Context FSEM02PairedTwoStepOutcomes.

(*
  FSEM-02 NON-NORMATIVE. A modeled first Ping/Choice step is assumed to
  succeed, while a second step is explicitly refused. The first committed
  pair is the refusal result. Conditional first-step frame laws then retain
  both shared-loan sets and the named disjoint spectators. This is not a
  proof that native Haskell Map/Set implements this Rocq ResourceContext,
  or that source admission, partner selection or authority was established.
*)

Theorem fsem02SecondRefusalRetainsCommittedSpectatorLoans :
  forall first second beforeSender beforeReceiver
         committedSender committedReceiver
         senderContinuation receiverContinuation choiceContinuation
         senderSpectator receiverSpectator,
    fsem02RequestContinuations first
      senderContinuation receiverContinuation choiceContinuation ->
    fsem02ReplayRequest first (beforeSender, beforeReceiver) =
      Some (committedSender, committedReceiver) ->
    fsem02ReplayRequest second (committedSender, committedReceiver) = None ->
    String.eqb senderSpectator (fsem02ReqSenderOld first) = false ->
    String.eqb senderSpectator (fsem02ReqSenderNext first) = false ->
    String.eqb receiverSpectator (fsem02ReqReceiverOld first) = false ->
    String.eqb receiverSpectator (fsem02ReqReceiverNext first) = false ->
    fsem02PairedTwoStepReplay first second (beforeSender, beforeReceiver) =
      FSEM02SecondRefused (committedSender, committedReceiver) /\
    sharedLoans committedSender = sharedLoans beforeSender /\
    sharedLoans committedReceiver = sharedLoans beforeReceiver /\
    linearBindings committedSender senderSpectator =
      linearBindings beforeSender senderSpectator /\
    linearBindings committedReceiver receiverSpectator =
      linearBindings beforeReceiver receiverSpectator.
Proof.
  intros first second beforeSender beforeReceiver
    committedSender committedReceiver
    senderContinuation receiverContinuation choiceContinuation
    senderSpectator receiverSpectator
    Hheads Hfirst Hsecond HsenderOld HsenderNext HreceiverOld HreceiverNext.
  pose proof (fsem02RequestSuccessFramesBothPeers
    first beforeSender beforeReceiver committedSender committedReceiver
    senderContinuation receiverContinuation choiceContinuation
    Hheads Hfirst) as [HloanS [HloanR [HframeS HframeR]]].
  repeat split.
  - eapply fsem02TwoStepRejectedSuffixRetainsCommittedPrefix; eauto.
  - exact HloanS.
  - exact HloanR.
  - apply HframeS; assumption.
  - apply HframeR; assumption.
Qed.
