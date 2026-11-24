From Stdlib Require Import Bool.Bool Strings.String Lists.List.
From Phil.Core Require Import
  Syntax Context FSEM02ProtocolHeadProgression FSEM02PairedSourceFamilyEnvelope.

(*
 FSEM-02 NON-NORMATIVE bounded paired two-step observation.
 Each step has independent externally supplied source/rendezvous admissions,
 heads, action labels, endpoint identities and contexts. A second refusal
 retains exactly the first committed successor contexts. None of these
 Boolean admissions establishes activation, nominal authority or
 ConcurrencySemantics.RendezvousValid; no combined source program,
 error-code refinement or universal Haskell-to-Rocq simulation is claimed.
*)
Record FSEM02PairedReplayRequest := {
  fsem02ReqFamily : FSEM02PairedSourceFamily;
  fsem02ReqSourceAccepted : bool;
  fsem02ReqRendezvousAdmitted : bool;
  fsem02ReqSenderAction : FSEM02Action;
  fsem02ReqReceiverAction : FSEM02Action;
  fsem02ReqSenderHead : Session;
  fsem02ReqReceiverHead : Session;
  fsem02ReqLabels : list string;
  fsem02ReqBranches : Branches;
  fsem02ReqChosen : string;
  fsem02ReqPeer : string;
  fsem02ReqSenderOld : Name;
  fsem02ReqSenderNext : Name;
  fsem02ReqReceiverOld : Name;
  fsem02ReqReceiverNext : Name
}.

Definition fsem02ReplayRequest
  (request : FSEM02PairedReplayRequest)
  (before : ResourceContext * ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  match before with
  | (senderBefore, receiverBefore) =>
      fsem02PairedSourceFamilyReplay
        (fsem02ReqFamily request)
        (fsem02ReqSourceAccepted request)
        (fsem02ReqRendezvousAdmitted request)
        (fsem02ReqSenderAction request)
        (fsem02ReqReceiverAction request)
        (fsem02ReqSenderHead request)
        (fsem02ReqReceiverHead request)
        (fsem02ReqLabels request)
        (fsem02ReqBranches request)
        (fsem02ReqChosen request)
        (fsem02ReqPeer request)
        (fsem02ReqSenderOld request)
        (fsem02ReqSenderNext request)
        (fsem02ReqReceiverOld request)
        (fsem02ReqReceiverNext request)
        senderBefore receiverBefore
  end.

Inductive FSEM02PairedTwoStepOutcome :=
| FSEM02FirstRefused (initial : ResourceContext * ResourceContext)
| FSEM02SecondRefused (committed : ResourceContext * ResourceContext)
| FSEM02BothAccepted
    (committed final : ResourceContext * ResourceContext).

Definition fsem02PairedTwoStepReplay
  (first second : FSEM02PairedReplayRequest)
  (initial : ResourceContext * ResourceContext)
  : FSEM02PairedTwoStepOutcome :=
  match fsem02ReplayRequest first initial with
  | None => FSEM02FirstRefused initial
  | Some committed =>
      match fsem02ReplayRequest second committed with
      | None => FSEM02SecondRefused committed
      | Some final => FSEM02BothAccepted committed final
      end
  end.

Theorem fsem02TwoStepFirstRefusalExact :
  forall first second initial,
    fsem02PairedTwoStepReplay first second initial =
      FSEM02FirstRefused initial <->
    fsem02ReplayRequest first initial = None.
Proof.
  intros first second initial; split.
  - intro H.
    unfold fsem02PairedTwoStepReplay in H.
    destruct (fsem02ReplayRequest first initial) as [middle|]
      eqn:Hfirst; [|reflexivity].
    destruct (fsem02ReplayRequest second middle); discriminate.
  - intro Hfirst.
    unfold fsem02PairedTwoStepReplay.
    now rewrite Hfirst.
Qed.

Theorem fsem02TwoStepSecondRefusalExact :
  forall first second initial committed,
    fsem02PairedTwoStepReplay first second initial =
      FSEM02SecondRefused committed <->
    fsem02ReplayRequest first initial = Some committed /\
    fsem02ReplayRequest second committed = None.
Proof.
  intros first second initial committed; split.
  - intro H.
    unfold fsem02PairedTwoStepReplay in H.
    destruct (fsem02ReplayRequest first initial) as [middle|]
      eqn:Hfirst; [|discriminate].
    destruct (fsem02ReplayRequest second middle) as [after|]
      eqn:Hsecond; [discriminate|].
    inversion H; subst; split; [reflexivity | exact Hsecond].
  - intros [Hfirst Hsecond].
    unfold fsem02PairedTwoStepReplay.
    now rewrite Hfirst, Hsecond.
Qed.

Theorem fsem02TwoStepSuccessExact :
  forall first second initial committed final,
    fsem02PairedTwoStepReplay first second initial =
      FSEM02BothAccepted committed final <->
    fsem02ReplayRequest first initial = Some committed /\
    fsem02ReplayRequest second committed = Some final.
Proof.
  intros first second initial committed final; split.
  - intro H.
    unfold fsem02PairedTwoStepReplay in H.
    destruct (fsem02ReplayRequest first initial) as [middle|]
      eqn:Hfirst; [|discriminate].
    destruct (fsem02ReplayRequest second middle) as [after|]
      eqn:Hsecond; [|discriminate].
    inversion H; subst; split; [reflexivity | exact Hsecond].
  - intros [Hfirst Hsecond].
    unfold fsem02PairedTwoStepReplay.
    now rewrite Hfirst, Hsecond.
Qed.

Theorem fsem02RequestSuccessRequiresExternalAdmissions :
  forall request before after,
    fsem02ReplayRequest request before = Some after ->
    fsem02ReqSourceAccepted request = true /\
    fsem02ReqRendezvousAdmitted request = true.
Proof.
  intros request [before1 before2] [after1 after2] Hstep.
  unfold fsem02ReplayRequest in Hstep.
  eapply fsem02FamilySuccessfulReplayRequiresBothAdmissions; eauto.
Qed.

Theorem fsem02TwoStepSuccessRequiresFourAdmissions :
  forall first second initial committed final,
    fsem02PairedTwoStepReplay first second initial =
      FSEM02BothAccepted committed final ->
    fsem02ReqSourceAccepted first = true /\
    fsem02ReqRendezvousAdmitted first = true /\
    fsem02ReqSourceAccepted second = true /\
    fsem02ReqRendezvousAdmitted second = true.
Proof.
  intros first second initial committed final Hsuccess.
  apply fsem02TwoStepSuccessExact in Hsuccess.
  destruct Hsuccess as [Hfirst Hsecond].
  pose proof (fsem02RequestSuccessRequiresExternalAdmissions
    first initial committed Hfirst) as [Hsource1 Hgate1].
  pose proof (fsem02RequestSuccessRequiresExternalAdmissions
    second committed final Hsecond) as [Hsource2 Hgate2].
  repeat split; assumption.
Qed.

Theorem fsem02TwoStepRejectedSuffixRetainsCommittedPrefix :
  forall first second initial committed,
    fsem02ReplayRequest first initial = Some committed ->
    fsem02ReplayRequest second committed = None ->
    fsem02PairedTwoStepReplay first second initial =
      FSEM02SecondRefused committed.
Proof.
  intros first second initial committed Hfirst Hsecond.
  unfold fsem02PairedTwoStepReplay.
  now rewrite Hfirst, Hsecond.
Qed.

Theorem fsem02TwoStepBadSecondFamilyGuardRetainsPrefix :
  forall first second initial committed,
    fsem02ReplayRequest first initial = Some committed ->
    fsem02PairedFamilyGuard
      (fsem02ReqFamily second)
      (fsem02ReqSenderAction second)
      (fsem02ReqReceiverAction second)
      (fsem02ReqChosen second)
      (fsem02ReqPeer second) = false ->
    fsem02PairedTwoStepReplay first second initial =
      FSEM02SecondRefused committed.
Proof.
  intros first second initial committed Hfirst Hguard.
  unfold fsem02PairedTwoStepReplay.
  rewrite Hfirst.
  destruct committed as [before1 before2].
  unfold fsem02ReplayRequest, fsem02PairedSourceFamilyReplay.
  rewrite Hguard.
  reflexivity.
Qed.

Definition fsem02RequestContinuations
  (request : FSEM02PairedReplayRequest)
  (senderContinuation receiverContinuation choiceContinuation : Session)
  : Prop :=
  (fsem02ReqFamily request = FSEM02PairedPing ->
    selectedContinuation
      (fsem02ReqSenderAction request) (fsem02ReqSenderHead request) =
        Some (Some senderContinuation) /\
    selectedContinuation
      (fsem02ReqReceiverAction request) (fsem02ReqReceiverHead request) =
        Some (Some receiverContinuation)) /\
  (fsem02ReqFamily request = FSEM02PairedChoice ->
    offeredContinuation (fsem02ReqChosen request)
      (fsem02ReqBranches request) = Some choiceContinuation).

Theorem fsem02RequestSuccessFramesBothPeers :
  forall request before1 before2 after1 after2
         senderContinuation receiverContinuation choiceContinuation,
    fsem02RequestContinuations request
      senderContinuation receiverContinuation choiceContinuation ->
    fsem02ReplayRequest request (before1, before2) =
      Some (after1, after2) ->
    sharedLoans after1 = sharedLoans before1 /\
    sharedLoans after2 = sharedLoans before2 /\
    (forall other,
      String.eqb other (fsem02ReqSenderOld request) = false ->
      String.eqb other (fsem02ReqSenderNext request) = false ->
      linearBindings after1 other = linearBindings before1 other) /\
    (forall other,
      String.eqb other (fsem02ReqReceiverOld request) = false ->
      String.eqb other (fsem02ReqReceiverNext request) = false ->
      linearBindings after2 other = linearBindings before2 other).
Proof.
  intros request before1 before2 after1 after2
    senderContinuation receiverContinuation choiceContinuation
    [Hping Hchoice] Hstep.
  unfold fsem02ReplayRequest in Hstep.
  eapply fsem02FamilySuccessfulReplayFramesBothPeers; eauto.
Qed.

Theorem fsem02TwoStepSuccessFramesTwoLoansAndDisjointSpectators :
  forall first second before1 before2 middle1 middle2 after1 after2
         sender1 receiver1 choice1 sender2 receiver2 choice2,
    fsem02RequestContinuations first sender1 receiver1 choice1 ->
    fsem02RequestContinuations second sender2 receiver2 choice2 ->
    fsem02ReplayRequest first (before1, before2) =
      Some (middle1, middle2) ->
    fsem02ReplayRequest second (middle1, middle2) =
      Some (after1, after2) ->
    sharedLoans after1 = sharedLoans before1 /\
    sharedLoans after2 = sharedLoans before2 /\
    (forall spectator,
      String.eqb spectator (fsem02ReqSenderOld first) = false ->
      String.eqb spectator (fsem02ReqSenderNext first) = false ->
      String.eqb spectator (fsem02ReqSenderOld second) = false ->
      String.eqb spectator (fsem02ReqSenderNext second) = false ->
      linearBindings after1 spectator = linearBindings before1 spectator) /\
    (forall spectator,
      String.eqb spectator (fsem02ReqReceiverOld first) = false ->
      String.eqb spectator (fsem02ReqReceiverNext first) = false ->
      String.eqb spectator (fsem02ReqReceiverOld second) = false ->
      String.eqb spectator (fsem02ReqReceiverNext second) = false ->
      linearBindings after2 spectator = linearBindings before2 spectator).
Proof.
  intros first second before1 before2 middle1 middle2 after1 after2
    sender1 receiver1 choice1 sender2 receiver2 choice2
    Hcontinue1 Hcontinue2 Hfirst Hsecond.
  pose proof (fsem02RequestSuccessFramesBothPeers
    first before1 before2 middle1 middle2
    sender1 receiver1 choice1 Hcontinue1 Hfirst)
    as [Hloan11 [Hloan12 [Hframe11 Hframe12]]].
  pose proof (fsem02RequestSuccessFramesBothPeers
    second middle1 middle2 after1 after2
    sender2 receiver2 choice2 Hcontinue2 Hsecond)
    as [Hloan21 [Hloan22 [Hframe21 Hframe22]]].
  repeat split.
  - now rewrite Hloan21, Hloan11.
  - now rewrite Hloan22, Hloan12.
  - intros spectator HfirstOld HfirstNext HsecondOld HsecondNext.
    rewrite (Hframe21 spectator HsecondOld HsecondNext).
    apply Hframe11; assumption.
  - intros spectator HfirstOld HfirstNext HsecondOld HsecondNext.
    rewrite (Hframe22 spectator HsecondOld HsecondNext).
    apply Hframe12; assumption.
Qed.
