From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ExplicitPeerClose FSEM02TerminalCloseDiamond.

(* FSEM-02 NON-NORMATIVE. The two booleans are externally checked instance
   and role grants. They are NOT recoverable from the local End syntax. *)
Inductive FSEM02ChoiceNominalDecision : Type :=
| FSEM02ChoiceWrongInstance
| FSEM02ChoiceWrongRole
| FSEM02ChoiceNominalAccepted.

Definition fsem02ChoiceNominalGate
  (instanceOK roleOK : bool) : FSEM02ChoiceNominalDecision :=
  if instanceOK then
    if roleOK then FSEM02ChoiceNominalAccepted
    else FSEM02ChoiceWrongRole
  else FSEM02ChoiceWrongInstance.

(* A refusal returns the already committed owner ledger as evidence,
   NOT a successful peer transition. None denotes no committed first step
   or nominal acceptance outside the refusal model. *)
Definition fsem02ChoiceClientCommittedNominalRefusal
  (instanceOK roleOK : bool) (owners : FSEM02OwnerLedger)
  (clientOccurrence clientProcess : string) (clientEndpoint : Name)
  : option (FSEM02ChoiceNominalDecision * FSEM02OwnerLedger) :=
  match fsem02RetireSelectedClientOwner owners
    clientOccurrence clientProcess clientEndpoint with
  | None => None
  | Some afterClient =>
      match fsem02ChoiceNominalGate instanceOK roleOK with
      | FSEM02ChoiceNominalAccepted => None
      | refused => Some (refused, afterClient)
      end
  end.

Definition fsem02ChoicePeerCommittedNominalRefusal
  (instanceOK roleOK : bool) (owners : FSEM02OwnerLedger)
  (peerOccurrence peerProcess : string) (peerEndpoint : Name)
  : option (FSEM02ChoiceNominalDecision * FSEM02OwnerLedger) :=
  match fsem02RetireExplicitPeerEnd owners
    peerOccurrence peerProcess peerEndpoint with
  | None => None
  | Some afterPeer =>
      match fsem02ChoiceNominalGate instanceOK roleOK with
      | FSEM02ChoiceNominalAccepted => None
      | refused => Some (refused, afterPeer)
      end
  end.

Theorem fsem02ChoiceNominalInstancePrecedesRole :
  fsem02ChoiceNominalGate false false = FSEM02ChoiceWrongInstance.
Proof. reflexivity. Qed.

Theorem fsem02ChoiceClientCommittedNominalInstanceRefusal :
  forall owners co cp ce afterClient roleOK,
    fsem02RetireSelectedClientOwner owners co cp ce = Some afterClient ->
    fsem02ChoiceClientCommittedNominalRefusal false roleOK owners co cp ce =
      Some (FSEM02ChoiceWrongInstance, afterClient) /\
    afterClient co = None /\
    (forall spectator, spectator <> co ->
      afterClient spectator = owners spectator).
Proof.
  intros owners co cp ce ac roleOK Hclose.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    owners co cp ce ac Hclose) as [Hgone Hframe].
  unfold fsem02ChoiceClientCommittedNominalRefusal.
  rewrite Hclose. simpl. auto.
Qed.

Theorem fsem02ChoicePeerCommittedNominalInstanceRefusal :
  forall owners po pp pe afterPeer roleOK,
    fsem02RetireExplicitPeerEnd owners po pp pe = Some afterPeer ->
    fsem02ChoicePeerCommittedNominalRefusal false roleOK owners po pp pe =
      Some (FSEM02ChoiceWrongInstance, afterPeer) /\
    afterPeer po = None /\
    (forall spectator, spectator <> po ->
      afterPeer spectator = owners spectator).
Proof.
  intros owners po pp pe ap roleOK Hclose.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    owners po pp pe ap Hclose) as [Hgone Hframe].
  unfold fsem02ChoicePeerCommittedNominalRefusal.
  change (fsem02RetireSelectedClientOwner owners po pp pe = Some ap)
    in Hclose.
  rewrite Hclose. simpl. auto.
Qed.

Theorem fsem02ChoiceClientCommittedNominalRoleRefusal :
  forall owners co cp ce afterClient,
    fsem02RetireSelectedClientOwner owners co cp ce = Some afterClient ->
    fsem02ChoiceClientCommittedNominalRefusal true false owners co cp ce =
      Some (FSEM02ChoiceWrongRole, afterClient).
Proof.
  intros owners co cp ce ac Hclose.
  unfold fsem02ChoiceClientCommittedNominalRefusal.
  now rewrite Hclose.
Qed.

Theorem fsem02ChoicePeerCommittedNominalRoleRefusal :
  forall owners po pp pe afterPeer,
    fsem02RetireExplicitPeerEnd owners po pp pe = Some afterPeer ->
    fsem02ChoicePeerCommittedNominalRefusal true false owners po pp pe =
      Some (FSEM02ChoiceWrongRole, afterPeer).
Proof.
  intros owners po pp pe ap Hclose.
  unfold fsem02ChoicePeerCommittedNominalRefusal.
  now rewrite Hclose.
Qed.

Theorem fsem02ChoiceClientFirstNominalRefusalThenPeerRetry :
  forall owners co cp ce po pp pe afterClient afterForward afterPeer afterReverse,
    co <> po ->
    fsem02RetireSelectedClientOwner owners co cp ce = Some afterClient ->
    fsem02RetireExplicitPeerEnd afterClient po pp pe = Some afterForward ->
    fsem02RetireExplicitPeerEnd owners po pp pe = Some afterPeer ->
    fsem02RetireSelectedClientOwner afterPeer co cp ce = Some afterReverse ->
    fsem02ChoiceClientCommittedNominalRefusal false false owners co cp ce =
      Some (FSEM02ChoiceWrongInstance, afterClient) /\
    (forall observed, afterForward observed = afterReverse observed).
Proof.
  intros owners co cp ce po pp pe ac af ap ar
    Hdistinct Hclient Hretry Hpeer HclientRetry.
  split.
  { unfold fsem02ChoiceClientCommittedNominalRefusal.
    now rewrite Hclient. }
  eapply fsem02ConditionalTerminalCloseDiamond; eauto.
Qed.

Theorem fsem02ChoicePeerFirstNominalRefusalThenClientRetry :
  forall owners co cp ce po pp pe afterClient afterForward afterPeer afterReverse,
    co <> po ->
    fsem02RetireSelectedClientOwner owners co cp ce = Some afterClient ->
    fsem02RetireExplicitPeerEnd afterClient po pp pe = Some afterForward ->
    fsem02RetireExplicitPeerEnd owners po pp pe = Some afterPeer ->
    fsem02RetireSelectedClientOwner afterPeer co cp ce = Some afterReverse ->
    fsem02ChoicePeerCommittedNominalRefusal false false owners po pp pe =
      Some (FSEM02ChoiceWrongInstance, afterPeer) /\
    (forall observed, afterForward observed = afterReverse observed).
Proof.
  intros owners co cp ce po pp pe ac af ap ar
    Hdistinct Hclient HpeerSecond HpeerFirst HclientSecond.
  split.
  { unfold fsem02ChoicePeerCommittedNominalRefusal.
    now rewrite HpeerFirst. }
  eapply fsem02ConditionalTerminalCloseDiamond; eauto.
Qed.
