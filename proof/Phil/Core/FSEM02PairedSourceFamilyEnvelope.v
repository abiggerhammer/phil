From Stdlib Require Import Bool.Bool Strings.String Lists.List.
From Phil.Core Require Import
  Syntax Context FSEM02ProtocolHeadProgression
  FSEM02PairedLocalJointBridge FSEM02PairedChoiceJointBridge.

(*
  FSEM-02 NON-NORMATIVE paired source-family observation envelope.

  This tagged, computable *model* selects one of the already verified
  bounded Ping Send/Receive and Choice Select/Offer paired-local replays.
  Its two admission Booleans are independent external premises, NOT a
  source-derived proof of activation, RendezvousValid, selected root,
  process identity, disposal, authority or payload transport.

  The native Haskell witness suites separately compare actual locally
  checked source-derived successors to actual synchronous joint Core
  successors, and retain exact source/Core rejection classes. This
  option-valued proof model only distinguishes Some from None; it does
  not encode diagnostic priorities, source-to-Rocq refinement, or a
  general Phase 1 operational semantics.
*)

Inductive FSEM02PairedSourceFamily :=
| FSEM02PairedPing
| FSEM02PairedChoice.

(* A source-family shape check, NOT nominal or protocol-instance authority. *)
Definition fsem02PairedFamilyGuard
  (family : FSEM02PairedSourceFamily)
  (senderAction receiverAction : FSEM02Action)
  (chosen peer : string) : bool :=
  match family with
  | FSEM02PairedPing =>
      match senderAction, receiverAction with
      | FSEM02Send, FSEM02Receive => true
      | _, _ => false
      end
  | FSEM02PairedChoice =>
      match senderAction, receiverAction with
      | FSEM02Select selected, FSEM02Offer offered =>
          andb (String.eqb selected chosen) (String.eqb offered peer)
      | _, _ => false
      end
  end.

Theorem fsem02PingGuardRequiresExactActionPair :
  forall sa ra chosen peer,
    fsem02PairedFamilyGuard FSEM02PairedPing sa ra chosen peer = true ->
    sa = FSEM02Send /\ ra = FSEM02Receive.
Proof.
  intros sa ra chosen peer H.
  destruct sa; destruct ra; simpl in H; try discriminate;
    split; reflexivity.
Qed.

Theorem fsem02ChoiceGuardRequiresExactChoiceLabels :
  forall sa ra chosen peer,
    fsem02PairedFamilyGuard FSEM02PairedChoice sa ra chosen peer = true ->
    exists selected offered,
      sa = FSEM02Select selected /\
      ra = FSEM02Offer offered /\
      String.eqb selected chosen = true /\
      String.eqb offered peer = true.
Proof.
  intros sa ra chosen peer H.
  destruct sa as [| | selected | otherLabel | otherOutcome];
  destruct ra as [| | otherSelected | offered | otherTerminal];
    simpl in H; try discriminate.
  apply andb_true_iff in H as [Hselected Hoffered].
  exists selected, offered.
  repeat split; try reflexivity; assumption.
Qed.

Definition fsem02PairedSourceFamilyReplay
  (family : FSEM02PairedSourceFamily)
  (sourceAccepted rendezvousAdmitted : bool)
  (senderAction receiverAction : FSEM02Action)
  (senderHead receiverHead : Session)
  (sourceLabels : list string) (branches : Branches)
  (chosen peer : string)
  (firstOld firstNext secondOld secondNext : Name)
  (firstBefore secondBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  if fsem02PairedFamilyGuard family senderAction receiverAction chosen peer
  then
    match family with
    | FSEM02PairedPing =>
        fsem02PairedLocalReplay sourceAccepted rendezvousAdmitted
          senderAction receiverAction senderHead receiverHead
          firstOld firstNext secondOld secondNext firstBefore secondBefore
    | FSEM02PairedChoice =>
        fsem02PairedChoiceReplay sourceAccepted rendezvousAdmitted
          sourceLabels branches chosen peer
          firstOld firstNext secondOld secondNext firstBefore secondBefore
    end
  else None.

Theorem fsem02FamilyRejectsUnacceptedSource :
  forall family admitted sa ra sh rh labels branches chosen peer
         old1 next1 old2 next2 before1 before2,
    fsem02PairedSourceFamilyReplay family false admitted
      sa ra sh rh labels branches chosen peer
      old1 next1 old2 next2 before1 before2 = None.
Proof.
  intros.
  unfold fsem02PairedSourceFamilyReplay.
  destruct (fsem02PairedFamilyGuard family sa ra chosen peer);
    destruct family; reflexivity.
Qed.

Theorem fsem02FamilyRejectsMissingRendezvousAdmission :
  forall family source sa ra sh rh labels branches chosen peer
         old1 next1 old2 next2 before1 before2,
    fsem02PairedSourceFamilyReplay family source false
      sa ra sh rh labels branches chosen peer
      old1 next1 old2 next2 before1 before2 = None.
Proof.
  intros.
  unfold fsem02PairedSourceFamilyReplay.
  destruct (fsem02PairedFamilyGuard family sa ra chosen peer);
    destruct family, source; reflexivity.
Qed.

Theorem fsem02FamilySuccessfulReplayRequiresBothAdmissions :
  forall family source admitted sa ra sh rh labels branches chosen peer
         old1 next1 old2 next2 before1 before2 after1 after2,
    fsem02PairedSourceFamilyReplay family source admitted
      sa ra sh rh labels branches chosen peer
      old1 next1 old2 next2 before1 before2 = Some (after1, after2) ->
    source = true /\ admitted = true.
Proof.
  intros family source admitted sa ra sh rh labels branches chosen peer
    old1 next1 old2 next2 before1 before2 after1 after2 Hstep.
  unfold fsem02PairedSourceFamilyReplay in Hstep.
  destruct (fsem02PairedFamilyGuard family sa ra chosen peer) eqn:Hfamily;
    [|discriminate].
  destruct family.
  - unfold fsem02PairedLocalReplay in Hstep.
    destruct (andb source admitted) eqn:Hgate; [|discriminate].
    apply andb_true_iff in Hgate. exact Hgate.
  - unfold fsem02PairedChoiceReplay in Hstep.
    destruct (andb source admitted) eqn:Hgate; [|discriminate].
    apply andb_true_iff in Hgate. exact Hgate.
Qed.

(*
  A single conditional property for both source-checked local families:
  each successful paired result preserves BOTH complete abstract loan
  functions and every other linear name on its own peer. No global
  native Map/Set -> Context simulation is inferred.
*)
Theorem fsem02FamilySuccessfulReplayFramesBothPeers :
  forall family source admitted sa ra sh rh labels branches chosen peer
         old1 next1 old2 next2 before1 before2 after1 after2
         senderContinuation receiverContinuation choiceContinuation,
    (family = FSEM02PairedPing ->
      selectedContinuation sa sh = Some (Some senderContinuation) /\
      selectedContinuation ra rh = Some (Some receiverContinuation)) ->
    (family = FSEM02PairedChoice ->
      offeredContinuation chosen branches = Some choiceContinuation) ->
    fsem02PairedSourceFamilyReplay family source admitted
      sa ra sh rh labels branches chosen peer
      old1 next1 old2 next2 before1 before2 = Some (after1, after2) ->
    sharedLoans after1 = sharedLoans before1 /\
    sharedLoans after2 = sharedLoans before2 /\
    (forall other,
      String.eqb other old1 = false ->
      String.eqb other next1 = false ->
      linearBindings after1 other = linearBindings before1 other) /\
    (forall other,
      String.eqb other old2 = false ->
      String.eqb other next2 = false ->
      linearBindings after2 other = linearBindings before2 other).
Proof.
  intros family source admitted sa ra sh rh labels branches chosen peer
    old1 next1 old2 next2 before1 before2 after1 after2
    senderContinuation receiverContinuation choiceContinuation
    Hping Hchoice Hstep.
  unfold fsem02PairedSourceFamilyReplay in Hstep.
  destruct (fsem02PairedFamilyGuard family sa ra chosen peer) eqn:Hfamily;
    [|discriminate].
  destruct family.
  - destruct (Hping eq_refl) as [Hsender Hreceiver].
    exact (fsem02PairedReplayFramesBothLoansAndIndependentLinearSpectators
      source admitted sa ra sh rh old1 next1 old2 next2
      before1 before2 after1 after2
      senderContinuation receiverContinuation Hsender Hreceiver Hstep).
  - pose proof (Hchoice eq_refl) as Hselected.
    exact (fsem02PairedChoiceFramesBothLocalLoanSetsAndLinearSpectators
      source admitted labels branches chosen peer
      old1 next1 old2 next2 before1 before2 after1 after2
      choiceContinuation Hselected Hstep).
Qed.

Theorem fsem02FamilyPingMissingFirstPredecessorRejects :
  forall source admitted sa ra sh rh labels branches chosen peer
         old1 next1 old2 next2 before1 before2,
    linearBindings before1 old1 = None ->
    fsem02PairedSourceFamilyReplay FSEM02PairedPing source admitted
      sa ra sh rh labels branches chosen peer
      old1 next1 old2 next2 before1 before2 = None.
Proof.
  intros.
  unfold fsem02PairedSourceFamilyReplay.
  destruct (fsem02PairedFamilyGuard FSEM02PairedPing sa ra chosen peer);
    [|reflexivity].
  eapply fsem02PairedReplayRejectsMissingSender; eauto.
Qed.

Theorem fsem02FamilyPingMissingSecondPredecessorRejects :
  forall source admitted sa ra sh rh labels branches chosen peer
         old1 next1 old2 next2 before1 before2,
    linearBindings before2 old2 = None ->
    fsem02PairedSourceFamilyReplay FSEM02PairedPing source admitted
      sa ra sh rh labels branches chosen peer
      old1 next1 old2 next2 before1 before2 = None.
Proof.
  intros.
  unfold fsem02PairedSourceFamilyReplay.
  destruct (fsem02PairedFamilyGuard FSEM02PairedPing sa ra chosen peer);
    [|reflexivity].
  eapply fsem02PairedReplayRejectsMissingReceiver; eauto.
Qed.

Theorem fsem02FamilyChoicePeerMismatchRejects :
  forall source admitted sa ra sh rh labels branches chosen peer
         old1 next1 old2 next2 before1 before2,
    String.eqb chosen peer = false ->
    fsem02PairedSourceFamilyReplay FSEM02PairedChoice source admitted
      sa ra sh rh labels branches chosen peer
      old1 next1 old2 next2 before1 before2 = None.
Proof.
  intros.
  unfold fsem02PairedSourceFamilyReplay.
  destruct (fsem02PairedFamilyGuard FSEM02PairedChoice sa ra chosen peer);
    [|reflexivity].
  eapply fsem02PairedChoiceRejectsPeerMismatch; eauto.
Qed.
