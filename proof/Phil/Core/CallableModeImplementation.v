From Stdlib Require Import Bool.Bool Lists.List.

From Phil.Core Require Import CallableMode.

Import ListNotations.

(*
  Executable correspondence layer for PHIL-CALL-MODE-001.

  Concrete capture-occurrence identity remains outside this extracted kernel.
  Production supplies native equality for occurrence keys; the kernel owns the
  resulting structural decision. Mode and CaptureTransfer are finite semantic
  enums and therefore cross the bridge by total constructor mapping.
*)

Inductive CallableCaptureTransferDecision : Type :=
| CallableCaptureTransferAccepted
| CallableRestrictedCaptureMustMove.

Definition decideCallableCaptureTransfer
  (mode : Mode)
  (transfer : CaptureTransfer)
  : CallableCaptureTransferDecision :=
  if captureTransferAllowed (mkClosureCapture 0 transfer mode)
  then CallableCaptureTransferAccepted
  else CallableRestrictedCaptureMustMove.

Definition captureMovedRestrictedByMode
  (mode : Mode)
  (transfer : CaptureTransfer)
  : bool :=
  captureMovedRestricted (mkClosureCapture 0 transfer mode).

Definition duplicateCaptureAllowedByEquality
  (sameOccurrence : bool)
  (firstMode secondMode : Mode)
  : bool :=
  if sameOccurrence
  then negb (orb (modeRestricted firstMode) (modeRestricted secondMode))
  else true.

Inductive CallableDuplicateCaptureDecision : Type :=
| CallableDuplicateCaptureAccepted
| CallableDuplicateRestrictedCapture.

Definition decideCallableDuplicateCapture
  (sameOccurrence : bool)
  (firstMode secondMode : Mode)
  : CallableDuplicateCaptureDecision :=
  if duplicateCaptureAllowedByEquality sameOccurrence firstMode secondMode
  then CallableDuplicateCaptureAccepted
  else CallableDuplicateRestrictedCapture.

Definition closureStructuralModeFromModes
  (modes : list Mode)
  : Mode :=
  fold_left joinMode modes Unrestricted.

Theorem transfer_decision_accept_iff_certified :
  forall occurrence mode transfer,
    decideCallableCaptureTransfer mode transfer =
      CallableCaptureTransferAccepted <->
    captureTransferAllowed
      (mkClosureCapture occurrence transfer mode) = true.
Proof.
  intros occurrence mode transfer.
  destruct mode, transfer; cbn; split; intro H;
    try reflexivity; try discriminate.
Qed.

Theorem moved_restricted_fact_agrees_with_certified :
  forall occurrence mode transfer,
    captureMovedRestrictedByMode mode transfer =
    captureMovedRestricted
      (mkClosureCapture occurrence transfer mode).
Proof.
  intros occurrence mode transfer.
  destruct mode, transfer; reflexivity.
Qed.

Theorem duplicate_decision_accept_iff_certified :
  forall firstOccurrence secondOccurrence firstTransfer secondTransfer
      firstMode secondMode,
    decideCallableDuplicateCapture
      (Nat.eqb firstOccurrence secondOccurrence)
      firstMode secondMode = CallableDuplicateCaptureAccepted <->
    duplicateCaptureAllowed
      (mkClosureCapture firstOccurrence firstTransfer firstMode)
      (mkClosureCapture secondOccurrence secondTransfer secondMode) = true.
Proof.
  intros firstOccurrence secondOccurrence firstTransfer secondTransfer
    firstMode secondMode.
  unfold decideCallableDuplicateCapture,
    duplicateCaptureAllowedByEquality,
    duplicateCaptureAllowed.
  cbn.
  destruct (Nat.eqb firstOccurrence secondOccurrence);
    destruct firstMode, secondMode; cbn; split; intro H;
    try reflexivity; try discriminate.
Qed.

Lemma closure_mode_fold_agrees :
  forall captures initial,
    fold_left
      (fun mode capture => joinMode mode (captureMode capture))
      captures initial =
    fold_left joinMode (map captureMode captures) initial.
Proof.
  induction captures as [|capture rest IH]; intros initial; cbn.
  - reflexivity.
  - apply IH.
Qed.

Theorem closure_mode_from_modes_agrees_with_certified :
  forall captures,
    closureStructuralModeFromModes (map captureMode captures) =
    closureStructuralMode captures.
Proof.
  intros captures.
  unfold closureStructuralModeFromModes, closureStructuralMode.
  symmetry.
  apply closure_mode_fold_agrees.
Qed.

Theorem empty_mode_list_is_unrestricted :
  closureStructuralModeFromModes [] = Unrestricted.
Proof.
  reflexivity.
Qed.

Theorem affine_mode_raises_closure :
  closureStructuralModeFromModes [Affine] = Affine.
Proof.
  reflexivity.
Qed.

Theorem linear_mode_dominates_mixed_closure :
  closureStructuralModeFromModes [Unrestricted; Affine; Linear] = Linear.
Proof.
  reflexivity.
Qed.
