From Phil.Core Require Import
  Context FSEM02PairedTwoStepOutcomes FSEM02TwoStepStalePrefix.

(*
  FSEM-02 NON-NORMATIVE: conditional paired two-step successor chaining.

  An admitted second Ping/Choice request can consume the FIRST request's
  successor endpoints only if its exact predecessor identities are those
  successors. The theorem records consumption on both peers, including the
  first committed context, not a proof of native multi-step source execution.
  Independently supplied source/rendezvous admissions and continuing heads
  are still premises. No model predicate creates protocol/architecture
  authority or establishes a native Map/Set-to-Rocq refinement.
*)

Theorem fsem02TwoStepChainedSuccessConsumesBothGenerations :
  forall first second beforeSender beforeReceiver
         middleSender middleReceiver finalSender finalReceiver
         firstSenderHead firstReceiverHead firstChoiceHead
         secondSenderHead secondReceiverHead secondChoiceHead,
    fsem02RequestContinuations first
      firstSenderHead firstReceiverHead firstChoiceHead ->
    fsem02RequestContinuations second
      secondSenderHead secondReceiverHead secondChoiceHead ->
    fsem02ReqSenderOld second = fsem02ReqSenderNext first ->
    fsem02ReqReceiverOld second = fsem02ReqReceiverNext first ->
    fsem02PairedTwoStepReplay first second
      (beforeSender, beforeReceiver) =
      FSEM02BothAccepted (middleSender, middleReceiver)
        (finalSender, finalReceiver) ->
    linearBindings middleSender (fsem02ReqSenderOld first) = None /\
    linearBindings middleReceiver (fsem02ReqReceiverOld first) = None /\
    linearBindings finalSender (fsem02ReqSenderNext first) = None /\
    linearBindings finalReceiver (fsem02ReqReceiverNext first) = None.
Proof.
  intros first second beforeSender beforeReceiver
    middleSender middleReceiver finalSender finalReceiver
    firstSenderHead firstReceiverHead firstChoiceHead
    secondSenderHead secondReceiverHead secondChoiceHead
    HfirstHeads HsecondHeads HsenderChain HreceiverChain Hboth.
  apply fsem02TwoStepSuccessExact in Hboth.
  destruct Hboth as [Hfirst Hsecond].
  pose proof (fsem02SuccessfulRequestConsumesBothExactPredecessors
    first beforeSender beforeReceiver middleSender middleReceiver
    firstSenderHead firstReceiverHead firstChoiceHead HfirstHeads Hfirst)
    as [HoldSender HoldReceiver].
  pose proof (fsem02SuccessfulRequestConsumesBothExactPredecessors
    second middleSender middleReceiver finalSender finalReceiver
    secondSenderHead secondReceiverHead secondChoiceHead HsecondHeads Hsecond)
    as [HmiddleSender HmiddleReceiver].
  repeat split.
  - exact HoldSender.
  - exact HoldReceiver.
  - rewrite <- HsenderChain in HmiddleSender. exact HmiddleSender.
  - rewrite <- HreceiverChain in HmiddleReceiver. exact HmiddleReceiver.
Qed.

Theorem fsem02TwoStepSecondUnadmittedSourcePreservesCommittedPrefix :
  forall first second initial committed,
    fsem02ReplayRequest first initial = Some committed ->
    fsem02ReqSourceAccepted second = false ->
    fsem02PairedTwoStepReplay first second initial =
      FSEM02SecondRefused committed.
Proof.
  intros first second initial committed Hfirst Hmissing.
  apply fsem02TwoStepRejectedSuffixRetainsCommittedPrefix; [exact Hfirst|].
  destruct (fsem02ReplayRequest second committed) as [later|] eqn:Hsecond.
  - pose proof (fsem02RequestSuccessRequiresExternalAdmissions
      second committed later Hsecond) as [Hsource _].
    rewrite Hmissing in Hsource. discriminate.
  - reflexivity.
Qed.

Theorem fsem02TwoStepSecondUnadmittedRendezvousPreservesCommittedPrefix :
  forall first second initial committed,
    fsem02ReplayRequest first initial = Some committed ->
    fsem02ReqRendezvousAdmitted second = false ->
    fsem02PairedTwoStepReplay first second initial =
      FSEM02SecondRefused committed.
Proof.
  intros first second initial committed Hfirst Hmissing.
  apply fsem02TwoStepRejectedSuffixRetainsCommittedPrefix; [exact Hfirst|].
  destruct (fsem02ReplayRequest second committed) as [later|] eqn:Hsecond.
  - pose proof (fsem02RequestSuccessRequiresExternalAdmissions
      second committed later Hsecond) as [_ Hgate].
    rewrite Hmissing in Hgate. discriminate.
  - reflexivity.
Qed.

Theorem fsem02TwoStepFirstUnadmittedSourcePreservesInitial :
  forall first second initial,
    fsem02ReqSourceAccepted first = false ->
    fsem02PairedTwoStepReplay first second initial =
      FSEM02FirstRefused initial.
Proof.
  intros first second initial Hmissing.
  apply fsem02TwoStepFirstRefusalExact.
  destruct (fsem02ReplayRequest first initial) as [later|] eqn:Hfirst.
  - pose proof (fsem02RequestSuccessRequiresExternalAdmissions
      first initial later Hfirst) as [Hsource _].
    rewrite Hmissing in Hsource. discriminate.
  - reflexivity.
Qed.
