From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List.

From Phil.Core Require Import GenericStructural.

Import ListNotations.

(*
  PHIL-CALL-MODE-001 — callable capture ownership and closure structural mode.

  This normalized model reuses the certified GenericStructural.Mode algebra.
  Restricted affine/linear capture occurrences must move into the sealed closure
  environment, cannot be duplicated under the same semantic occurrence identity,
  and are recorded as moved predecessors. The closure's structural mode is the
  least-upper-bound fold under Unrestricted < Affine < Linear.

  Concrete Text occurrence keys, Haskell Map normalization, duplicate diagnostic
  ordering, source capture discovery, and target closure-environment layout remain
  explicit correspondence boundaries.
*)

Inductive CaptureTransfer : Type :=
| CopyCapture
| MoveCapture.

Record ClosureCapture : Type := mkClosureCapture {
  captureOccurrence : nat;
  captureTransfer : CaptureTransfer;
  captureMode : Mode
}.

Definition modeRestricted (mode : Mode) : bool :=
  match mode with
  | Unrestricted => false
  | Affine => true
  | Linear => true
  end.

Definition transferIsMove (transfer : CaptureTransfer) : bool :=
  match transfer with
  | CopyCapture => false
  | MoveCapture => true
  end.

Definition captureTransferAllowed (capture : ClosureCapture) : bool :=
  if modeRestricted (captureMode capture)
  then transferIsMove (captureTransfer capture)
  else true.

Definition captureMovedRestricted (capture : ClosureCapture) : bool :=
  andb
    (modeRestricted (captureMode capture))
    (transferIsMove (captureTransfer capture)).

Definition duplicateCaptureAllowed
  (first second : ClosureCapture) : bool :=
  if Nat.eqb (captureOccurrence first) (captureOccurrence second)
  then negb
    (orb
      (modeRestricted (captureMode first))
      (modeRestricted (captureMode second)))
  else true.

Definition joinMode (first second : Mode) : Mode :=
  match first, second with
  | Linear, _ => Linear
  | _, Linear => Linear
  | Affine, _ => Affine
  | _, Affine => Affine
  | Unrestricted, Unrestricted => Unrestricted
  end.

Definition modeLe (lower upper : Mode) : bool :=
  match lower, upper with
  | Unrestricted, _ => true
  | Affine, Affine => true
  | Affine, Linear => true
  | Linear, Linear => true
  | _, _ => false
  end.

Definition closureStructuralMode
  (captures : list ClosureCapture) : Mode :=
  fold_left
    (fun mode capture => joinMode mode (captureMode capture))
    captures Unrestricted.

Theorem empty_closure_is_unrestricted :
  closureStructuralMode [] = Unrestricted.
Proof.
  reflexivity.
Qed.

Theorem unrestricted_capture_may_copy :
  forall occurrence,
    captureTransferAllowed
      (mkClosureCapture occurrence CopyCapture Unrestricted) = true.
Proof.
  reflexivity.
Qed.

Theorem unrestricted_capture_may_move :
  forall occurrence,
    captureTransferAllowed
      (mkClosureCapture occurrence MoveCapture Unrestricted) = true.
Proof.
  reflexivity.
Qed.

Theorem accepted_affine_capture_must_move :
  forall occurrence transfer,
    captureTransferAllowed
      (mkClosureCapture occurrence transfer Affine) = true ->
    transfer = MoveCapture.
Proof.
  intros occurrence transfer Hallowed.
  destruct transfer; simpl in Hallowed.
  - discriminate.
  - reflexivity.
Qed.

Theorem accepted_linear_capture_must_move :
  forall occurrence transfer,
    captureTransferAllowed
      (mkClosureCapture occurrence transfer Linear) = true ->
    transfer = MoveCapture.
Proof.
  intros occurrence transfer Hallowed.
  destruct transfer; simpl in Hallowed.
  - discriminate.
  - reflexivity.
Qed.

Theorem affine_move_is_recorded_as_restricted_transfer :
  forall occurrence,
    captureMovedRestricted
      (mkClosureCapture occurrence MoveCapture Affine) = true.
Proof.
  reflexivity.
Qed.

Theorem linear_move_is_recorded_as_restricted_transfer :
  forall occurrence,
    captureMovedRestricted
      (mkClosureCapture occurrence MoveCapture Linear) = true.
Proof.
  reflexivity.
Qed.

Theorem affine_copy_is_rejected :
  forall occurrence,
    captureTransferAllowed
      (mkClosureCapture occurrence CopyCapture Affine) = false.
Proof.
  reflexivity.
Qed.

Theorem linear_copy_is_rejected :
  forall occurrence,
    captureTransferAllowed
      (mkClosureCapture occurrence CopyCapture Linear) = false.
Proof.
  reflexivity.
Qed.

Theorem duplicate_affine_occurrence_is_rejected :
  forall occurrence firstTransfer secondTransfer,
    duplicateCaptureAllowed
      (mkClosureCapture occurrence firstTransfer Affine)
      (mkClosureCapture occurrence secondTransfer Affine) = false.
Proof.
  intros occurrence firstTransfer secondTransfer.
  unfold duplicateCaptureAllowed.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem duplicate_linear_occurrence_is_rejected :
  forall occurrence firstTransfer secondTransfer,
    duplicateCaptureAllowed
      (mkClosureCapture occurrence firstTransfer Linear)
      (mkClosureCapture occurrence secondTransfer Linear) = false.
Proof.
  intros occurrence firstTransfer secondTransfer.
  unfold duplicateCaptureAllowed.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem distinct_occurrences_do_not_conflict :
  forall firstOccurrence secondOccurrence firstTransfer secondTransfer
      firstMode secondMode,
    firstOccurrence <> secondOccurrence ->
    duplicateCaptureAllowed
      (mkClosureCapture firstOccurrence firstTransfer firstMode)
      (mkClosureCapture secondOccurrence secondTransfer secondMode) = true.
Proof.
  intros firstOccurrence secondOccurrence firstTransfer secondTransfer
    firstMode secondMode Hdifferent.
  unfold duplicateCaptureAllowed.
  cbn.
  destruct (Nat.eqb firstOccurrence secondOccurrence) eqn:Hequal.
  - apply Nat.eqb_eq in Hequal.
    contradiction.
  - reflexivity.
Qed.

Theorem join_mode_is_commutative :
  forall first second,
    joinMode first second = joinMode second first.
Proof.
  intros first second.
  destruct first, second; reflexivity.
Qed.

Theorem join_mode_is_associative :
  forall first second third,
    joinMode (joinMode first second) third =
    joinMode first (joinMode second third).
Proof.
  intros first second third.
  destruct first, second, third; reflexivity.
Qed.

Theorem join_mode_contains_left :
  forall first second,
    modeLe first (joinMode first second) = true.
Proof.
  intros first second.
  destruct first, second; reflexivity.
Qed.

Theorem join_mode_contains_right :
  forall first second,
    modeLe second (joinMode first second) = true.
Proof.
  intros first second.
  destruct first, second; reflexivity.
Qed.

Theorem join_mode_is_least_upper_bound :
  forall first second upper,
    modeLe first upper = true ->
    modeLe second upper = true ->
    modeLe (joinMode first second) upper = true.
Proof.
  intros first second upper Hfirst Hsecond.
  destruct first, second, upper; simpl in *; try discriminate; reflexivity.
Qed.

Theorem single_affine_capture_makes_affine_closure :
  forall occurrence transfer,
    closureStructuralMode
      [mkClosureCapture occurrence transfer Affine] = Affine.
Proof.
  reflexivity.
Qed.

Theorem single_linear_capture_makes_linear_closure :
  forall occurrence transfer,
    closureStructuralMode
      [mkClosureCapture occurrence transfer Linear] = Linear.
Proof.
  reflexivity.
Qed.

Theorem linear_capture_dominates_mixed_closure_mode :
  forall firstOccurrence secondOccurrence thirdOccurrence
      firstTransfer secondTransfer thirdTransfer,
    closureStructuralMode
      [ mkClosureCapture firstOccurrence firstTransfer Unrestricted
      ; mkClosureCapture secondOccurrence secondTransfer Affine
      ; mkClosureCapture thirdOccurrence thirdTransfer Linear
      ] = Linear.
Proof.
  reflexivity.
Qed.

Theorem three_capture_mode_is_order_independent :
  forall first second third,
    closureStructuralMode [first; second; third] =
    closureStructuralMode [third; first; second].
Proof.
  intros [firstOccurrence firstTransfer firstMode]
    [secondOccurrence secondTransfer secondMode]
    [thirdOccurrence thirdTransfer thirdMode].
  destruct firstMode, secondMode, thirdMode; reflexivity.
Qed.
