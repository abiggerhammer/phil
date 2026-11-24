From Stdlib Require Import Bool.Bool Strings.String Lists.List.
From Phil.Core Require Import
  Syntax Context FSEM02ProtocolHeadProgression FSEM02JointSourceChoice
  FSEM02PairedChoiceJointBridge FSEM02PairedSourceFamilyEnvelope
  FSEM02PairedTwoStepOutcomes FSEM02TwoStepStalePrefix.

(*
  FSEM-02 NON-NORMATIVE conditional two-step stale Choice refusal.

  This extends the existing Ping-suffix theorem to Select/Offer. The first
  *admitted* transition may be Ping or Choice; the second Choice cannot
  reuse either consumed predecessor, and refusal retains the entire
  committed first-step pair. The two source checks are independent real
  Haskell witnesses, NOT a mixed-family source program. External source
  admission, typed heads, peer/instance, rendezvous and ownership remain
  premises. Model None is not a native diagnostic-class theorem.
*)

Theorem fsem02FamilyChoiceMissingSelectorPredecessorRejects :
  forall source admitted sa ra sh rh labels branches chosen peer
         selectorOld selectorNext offerOld offerNext selectorBefore offerBefore,
    linearBindings selectorBefore selectorOld = None ->
    fsem02PairedSourceFamilyReplay FSEM02PairedChoice source admitted
      sa ra sh rh labels branches chosen peer
      selectorOld selectorNext offerOld offerNext selectorBefore offerBefore
      = None.
Proof.
  intros source admitted sa ra sh rh labels branches chosen peer
    selectorOld selectorNext offerOld offerNext selectorBefore offerBefore Hmissing.
  unfold fsem02PairedSourceFamilyReplay.
  destruct (fsem02PairedFamilyGuard FSEM02PairedChoice sa ra chosen peer);
    [|reflexivity].
  unfold fsem02PairedChoiceReplay.
  destruct (andb source admitted); [|reflexivity].
  unfold fsem02JointSourceChoice.
  destruct (String.eqb chosen peer); [|reflexivity].
  destruct (fsem02SourceContainsLabel chosen labels); [|reflexivity].
  destruct (fsem02Progression (FSEM02Select chosen) (Select branches)
    selectorOld selectorNext selectorBefore) as [| actual] eqn:Hselector;
    [reflexivity|].
  exfalso.
  eapply (stale_linear_predecessor_cannot_succeed
    (FSEM02Select chosen) (Select branches)
    selectorOld selectorNext selectorBefore actual Hmissing).
  exact Hselector.
Qed.

Theorem fsem02FamilyChoiceMissingOfferPredecessorRejects :
  forall source admitted sa ra sh rh labels branches chosen peer
         selectorOld selectorNext offerOld offerNext selectorBefore offerBefore,
    linearBindings offerBefore offerOld = None ->
    fsem02PairedSourceFamilyReplay FSEM02PairedChoice source admitted
      sa ra sh rh labels branches chosen peer
      selectorOld selectorNext offerOld offerNext selectorBefore offerBefore
      = None.
Proof.
  intros source admitted sa ra sh rh labels branches chosen peer
    selectorOld selectorNext offerOld offerNext selectorBefore offerBefore Hmissing.
  unfold fsem02PairedSourceFamilyReplay.
  destruct (fsem02PairedFamilyGuard FSEM02PairedChoice sa ra chosen peer);
    [|reflexivity].
  unfold fsem02PairedChoiceReplay.
  destruct (andb source admitted); [|reflexivity].
  unfold fsem02JointSourceChoice.
  destruct (String.eqb chosen peer); [|reflexivity].
  destruct (fsem02SourceContainsLabel chosen labels) eqn:Hcovered;
    [|reflexivity].
  destruct (fsem02Progression (FSEM02Select chosen) (Select branches)
    selectorOld selectorNext selectorBefore) as [| clientAfter] eqn:Hselector;
    [reflexivity|].
  destruct (fsem02SourceOfferReplay labels branches chosen
    offerOld offerNext offerBefore) as [| offerAfter] eqn:Hoffer;
    [reflexivity|].
  unfold fsem02SourceOfferReplay in Hoffer.
  rewrite Hcovered in Hoffer.
  exfalso.
  eapply (stale_linear_predecessor_cannot_succeed
    (FSEM02Offer chosen) (Offer branches)
    offerOld offerNext offerBefore offerAfter Hmissing).
  exact Hoffer.
Qed.

Theorem fsem02TwoStepStaleSelectorChoiceRefusesWithoutRollback :
  forall first second beforeSender beforeReceiver afterSender afterReceiver
         senderContinuation receiverContinuation choiceContinuation,
    fsem02RequestContinuations first
      senderContinuation receiverContinuation choiceContinuation ->
    fsem02ReqFamily second = FSEM02PairedChoice ->
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
    eapply fsem02FamilyChoiceMissingSelectorPredecessorRejects.
    rewrite Hsame.
    exact HsenderGone.
Qed.

Theorem fsem02TwoStepStaleOfferChoiceRefusesWithoutRollback :
  forall first second beforeSender beforeReceiver afterSender afterReceiver
         senderContinuation receiverContinuation choiceContinuation,
    fsem02RequestContinuations first
      senderContinuation receiverContinuation choiceContinuation ->
    fsem02ReqFamily second = FSEM02PairedChoice ->
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
    eapply fsem02FamilyChoiceMissingOfferPredecessorRejects.
    rewrite Hsame.
    exact HreceiverGone.
Qed.
