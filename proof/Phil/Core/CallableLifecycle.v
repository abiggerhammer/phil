From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import CallableMode.

(*
  PHIL-CALL-LIFE-001 — exact callable ownership lifecycle.

  The normalized model starts from the restricted-capture residue already
  justified by PHIL-CALL-MODE-001. Availability is keyed by exact callable
  ownership occurrence, independently of callable interface identity.

  Preserve keeps the exact predecessor and exact restricted residue; consume
  removes the predecessor; replace removes it and installs one fresh, distinct
  successor with the declared interface/state identity.

  Concrete Text keys, Haskell Map/Set operations, complete body resource
  redistribution, and target closure representation remain correspondence
  boundaries.
*)

Definition CaptureSet : Type := nat -> bool.
Definition ResourceState : Type := nat -> bool.

Definition sameCaptureSet (first second : CaptureSet) : Prop :=
  forall capture, first capture = second capture.

Definition captureSetEmpty (captures : CaptureSet) : Prop :=
  forall capture, captures capture = false.

Definition sameResourceState (first second : ResourceState) : Prop :=
  forall occurrence, first occurrence = second occurrence.

Definition removeOccurrence
  (state : ResourceState)
  (removed : nat) : ResourceState :=
  fun occurrence =>
    if Nat.eqb occurrence removed then false else state occurrence.

Definition addOccurrence
  (state : ResourceState)
  (added : nat) : ResourceState :=
  fun occurrence =>
    if Nat.eqb occurrence added then true else state occurrence.

Record CallableSuccessor : Type := mkCallableSuccessor {
  successorOccurrence : nat;
  successorInterface : nat;
  successorState : option nat
}.

Definition preserveTransitionValid
  (expectedResidue actualResidue : CaptureSet)
  (successor : option CallableSuccessor) : Prop :=
  sameCaptureSet expectedResidue actualResidue /\
  successor = None.

Definition consumeTransitionValid
  (actualResidue : CaptureSet)
  (successor : option CallableSuccessor) : Prop :=
  captureSetEmpty actualResidue /\
  successor = None.

Definition replaceTransitionValid
  (predecessor : nat)
  (state : ResourceState)
  (expectedInterface : nat)
  (expectedState : option nat)
  (actualResidue : CaptureSet)
  (successor : option CallableSuccessor) : Prop :=
  captureSetEmpty actualResidue /\
  exists replacement,
    successor = Some replacement /\
    successorOccurrence replacement <> predecessor /\
    state (successorOccurrence replacement) = false /\
    successorInterface replacement = expectedInterface /\
    successorState replacement = expectedState.

Definition preserveResult (state : ResourceState) : ResourceState := state.

Definition consumeResult
  (state : ResourceState)
  (predecessor : nat) : ResourceState :=
  removeOccurrence state predecessor.

Definition replaceResult
  (state : ResourceState)
  (predecessor : nat)
  (successor : CallableSuccessor) : ResourceState :=
  addOccurrence
    (removeOccurrence state predecessor)
    (successorOccurrence successor).

Theorem preserve_requires_exact_restricted_residue :
  forall expected actual successor,
    preserveTransitionValid expected actual successor ->
    sameCaptureSet expected actual.
Proof.
  intros expected actual successor Hvalid.
  exact (proj1 Hvalid).
Qed.

Theorem preserve_rejects_missing_restricted_capture :
  forall expected actual successor capture,
    expected capture = true ->
    actual capture = false ->
    ~ preserveTransitionValid expected actual successor.
Proof.
  intros expected actual successor capture Hexpected Hactual Hvalid.
  destruct Hvalid as [Hsame _].
  specialize (Hsame capture).
  rewrite Hexpected, Hactual in Hsame.
  discriminate.
Qed.

Theorem preserve_rejects_successor :
  forall expected actual replacement,
    ~ preserveTransitionValid expected actual (Some replacement).
Proof.
  intros expected actual replacement Hvalid.
  destruct Hvalid as [_ Hsuccessor].
  discriminate.
Qed.

Theorem preserve_keeps_resource_state_exact :
  forall state,
    sameResourceState (preserveResult state) state.
Proof.
  intros state occurrence.
  reflexivity.
Qed.

Theorem preserve_keeps_predecessor_available :
  forall state predecessor,
    state predecessor = true ->
    preserveResult state predecessor = true.
Proof.
  intros state predecessor Havailable.
  exact Havailable.
Qed.

Theorem preserving_invocation_is_repeatable :
  forall state predecessor,
    state predecessor = true ->
    preserveResult (preserveResult state) predecessor = true.
Proof.
  intros state predecessor Havailable.
  exact Havailable.
Qed.

Theorem consume_requires_empty_restricted_residue :
  forall actual successor,
    consumeTransitionValid actual successor ->
    captureSetEmpty actual.
Proof.
  intros actual successor Hvalid.
  exact (proj1 Hvalid).
Qed.

Theorem consume_rejects_retained_restricted_capture :
  forall actual successor capture,
    actual capture = true ->
    ~ consumeTransitionValid actual successor.
Proof.
  intros actual successor capture Hretained Hvalid.
  destruct Hvalid as [Hempty _].
  specialize (Hempty capture).
  rewrite Hretained in Hempty.
  discriminate.
Qed.

Theorem consume_rejects_successor :
  forall actual replacement,
    ~ consumeTransitionValid actual (Some replacement).
Proof.
  intros actual replacement Hvalid.
  destruct Hvalid as [_ Hsuccessor].
  discriminate.
Qed.

Theorem consume_removes_predecessor :
  forall state predecessor,
    consumeResult state predecessor predecessor = false.
Proof.
  intros state predecessor.
  unfold consumeResult, removeOccurrence.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem consume_preserves_other_occurrences :
  forall state predecessor occurrence,
    occurrence <> predecessor ->
    consumeResult state predecessor occurrence = state occurrence.
Proof.
  intros state predecessor occurrence Hdifferent.
  unfold consumeResult, removeOccurrence.
  destruct (Nat.eqb occurrence predecessor) eqn:Hequal.
  - apply Nat.eqb_eq in Hequal.
    contradiction.
  - reflexivity.
Qed.

Theorem consumed_predecessor_cannot_be_reused :
  forall state predecessor,
    ~ (consumeResult state predecessor predecessor = true).
Proof.
  intros state predecessor Havailable.
  rewrite consume_removes_predecessor in Havailable.
  discriminate.
Qed.

Theorem replace_requires_successor :
  forall predecessor state expectedInterface expectedState actual successor,
    replaceTransitionValid
      predecessor state expectedInterface expectedState actual successor ->
    exists replacement, successor = Some replacement.
Proof.
  intros predecessor state expectedInterface expectedState actual successor Hvalid.
  destruct Hvalid as [_ [replacement [Hsuccessor _]]].
  exists replacement.
  exact Hsuccessor.
Qed.

Theorem replace_requires_distinct_successor_occurrence :
  forall predecessor state expectedInterface expectedState actual successor,
    replaceTransitionValid
      predecessor state expectedInterface expectedState actual (Some successor) ->
    successorOccurrence successor <> predecessor.
Proof.
  intros predecessor state expectedInterface expectedState actual successor Hvalid.
  destruct Hvalid as [_ [replacement [Hsome [Hdistinct _]]]].
  inversion Hsome; subst replacement.
  exact Hdistinct.
Qed.

Theorem replace_requires_fresh_successor_occurrence :
  forall predecessor state expectedInterface expectedState actual successor,
    replaceTransitionValid
      predecessor state expectedInterface expectedState actual (Some successor) ->
    state (successorOccurrence successor) = false.
Proof.
  intros predecessor state expectedInterface expectedState actual successor Hvalid.
  destruct Hvalid as [_ [replacement [Hsome [_ [Hfresh _]]]]].
  inversion Hsome; subst replacement.
  exact Hfresh.
Qed.

Theorem replace_requires_exact_successor_interface :
  forall predecessor state expectedInterface expectedState actual successor,
    replaceTransitionValid
      predecessor state expectedInterface expectedState actual (Some successor) ->
    successorInterface successor = expectedInterface.
Proof.
  intros predecessor state expectedInterface expectedState actual successor Hvalid.
  destruct Hvalid as [_ [replacement [Hsome [_ [_ [Hinterface _]]]]]].
  inversion Hsome; subst replacement.
  exact Hinterface.
Qed.

Theorem replace_requires_exact_successor_state :
  forall predecessor state expectedInterface expectedState actual successor,
    replaceTransitionValid
      predecessor state expectedInterface expectedState actual (Some successor) ->
    successorState successor = expectedState.
Proof.
  intros predecessor state expectedInterface expectedState actual successor Hvalid.
  destruct Hvalid as [_ [replacement [Hsome [_ [_ [_ Hstate]]]]]].
  inversion Hsome; subst replacement.
  exact Hstate.
Qed.

Theorem replace_rejects_missing_successor :
  forall predecessor state expectedInterface expectedState actual,
    ~ replaceTransitionValid
        predecessor state expectedInterface expectedState actual None.
Proof.
  intros predecessor state expectedInterface expectedState actual Hvalid.
  destruct Hvalid as [_ [replacement [Hsuccessor _]]].
  discriminate.
Qed.

Theorem replace_rejects_predecessor_key_reuse :
  forall predecessor state expectedInterface expectedState actual actualInterface actualState,
    ~ replaceTransitionValid
        predecessor state expectedInterface expectedState actual
        (Some (mkCallableSuccessor predecessor actualInterface actualState)).
Proof.
  intros predecessor state expectedInterface expectedState actual actualInterface actualState Hvalid.
  destruct Hvalid as [_ [replacement [Hsome [Hdistinct _]]]].
  inversion Hsome; subst replacement.
  contradiction.
Qed.

Theorem replace_rejects_already_available_successor :
  forall predecessor state expectedInterface expectedState actual successor,
    state (successorOccurrence successor) = true ->
    ~ replaceTransitionValid
        predecessor state expectedInterface expectedState actual (Some successor).
Proof.
  intros predecessor state expectedInterface expectedState actual successor Havailable Hvalid.
  destruct Hvalid as [_ [replacement [Hsome [_ [Hfresh _]]]]].
  inversion Hsome; subst replacement.
  rewrite Havailable in Hfresh.
  discriminate.
Qed.

Theorem replace_rejects_interface_mismatch :
  forall predecessor state expectedInterface expectedState actual successor,
    successorInterface successor <> expectedInterface ->
    ~ replaceTransitionValid
        predecessor state expectedInterface expectedState actual (Some successor).
Proof.
  intros predecessor state expectedInterface expectedState actual successor Hmismatch Hvalid.
  apply Hmismatch.
  eapply replace_requires_exact_successor_interface.
  exact Hvalid.
Qed.

Theorem replace_rejects_state_mismatch :
  forall predecessor state expectedInterface expectedState actual successor,
    successorState successor <> expectedState ->
    ~ replaceTransitionValid
        predecessor state expectedInterface expectedState actual (Some successor).
Proof.
  intros predecessor state expectedInterface expectedState actual successor Hmismatch Hvalid.
  apply Hmismatch.
  eapply replace_requires_exact_successor_state.
  exact Hvalid.
Qed.

Theorem replacement_installs_successor :
  forall state predecessor successor,
    replaceResult state predecessor successor (successorOccurrence successor) = true.
Proof.
  intros state predecessor successor.
  unfold replaceResult, addOccurrence.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem replacement_removes_predecessor :
  forall state predecessor successor,
    successorOccurrence successor <> predecessor ->
    replaceResult state predecessor successor predecessor = false.
Proof.
  intros state predecessor successor Hdifferent.
  unfold replaceResult, addOccurrence.
  destruct (Nat.eqb predecessor (successorOccurrence successor)) eqn:Hequal.
  - apply Nat.eqb_eq in Hequal.
    exfalso.
    apply Hdifferent.
    symmetry.
    exact Hequal.
  - unfold removeOccurrence.
    rewrite Nat.eqb_refl.
    reflexivity.
Qed.

Theorem replacement_preserves_unrelated_occurrences :
  forall state predecessor successor occurrence,
    occurrence <> predecessor ->
    occurrence <> successorOccurrence successor ->
    replaceResult state predecessor successor occurrence = state occurrence.
Proof.
  intros state predecessor successor occurrence Hpredecessor Hsuccessor.
  unfold replaceResult, addOccurrence.
  destruct (Nat.eqb occurrence (successorOccurrence successor)) eqn:HequalSuccessor.
  - apply Nat.eqb_eq in HequalSuccessor.
    contradiction.
  - unfold removeOccurrence.
    destruct (Nat.eqb occurrence predecessor) eqn:HequalPredecessor.
    + apply Nat.eqb_eq in HequalPredecessor.
      contradiction.
    + reflexivity.
Qed.

Theorem equal_interface_replacement_does_not_resurrect_predecessor :
  forall state predecessor successor interface,
    successorInterface successor = interface ->
    successorOccurrence successor <> predecessor ->
    replaceResult state predecessor successor predecessor = false.
Proof.
  intros state predecessor successor interface _ Hdifferent.
  apply replacement_removes_predecessor.
  exact Hdifferent.
Qed.

Theorem equal_interface_does_not_identify_occurrences :
  forall predecessor successor interface,
    successorInterface successor = interface ->
    successorOccurrence successor <> predecessor ->
    successorOccurrence successor <> predecessor.
Proof.
  intros predecessor successor interface _ Hdifferent.
  exact Hdifferent.
Qed.
