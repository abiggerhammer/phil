From Stdlib Require Import Arith.PeanoNat Bool.Bool.

(*
  PHIL-SYS-OWN-001 — proof-oriented model of ownership and recognition
  realization in Phil.Systems.Verify.

  Concrete Data.Map traversal, textual storage identities, and operation-list
  extraction remain implementation correspondence boundaries.  This model
  starts from the verifier's normalized relations and proves the authority-
  relevant consequences: one owner per storage identity, borrows name owners
  without becoming owners, and recognition commit/destroy operations are tied
  to the exact success/failure branches with no transport use before commit.
*)

Definition ValueId := nat.
Definition StorageId := nat.
Definition BlockId := nat.

Inductive ValueRole : Type :=
| OwningRole
| BorrowedRole : ValueId -> ValueRole
| NonOwningRole.

Record OwnershipModel : Type := mkOwnershipModel {
  ownershipRole : ValueId -> option ValueRole;
  ownershipStorage : ValueId -> option StorageId
}.

Definition OwnershipVerificationSuccess (model : OwnershipModel) : Prop :=
  (forall left right storage,
    ownershipRole model left = Some OwningRole ->
    ownershipRole model right = Some OwningRole ->
    ownershipStorage model left = Some storage ->
    ownershipStorage model right = Some storage ->
    left = right) /\
  (forall view owner,
    ownershipRole model view = Some (BorrowedRole owner) ->
    ownershipRole model owner = Some OwningRole).

Theorem verified_storage_has_at_most_one_owner :
  forall model left right storage,
    OwnershipVerificationSuccess model ->
    ownershipRole model left = Some OwningRole ->
    ownershipRole model right = Some OwningRole ->
    ownershipStorage model left = Some storage ->
    ownershipStorage model right = Some storage ->
    left = right.
Proof.
  intros model left right storage Hverified Hleft Hright HleftStorage HrightStorage.
  destruct Hverified as [Hunique _].
  eapply Hunique; eauto.
Qed.

Theorem verified_borrow_names_existing_owner :
  forall model view owner,
    OwnershipVerificationSuccess model ->
    ownershipRole model view = Some (BorrowedRole owner) ->
    ownershipRole model owner = Some OwningRole.
Proof.
  intros model view owner Hverified Hborrow.
  destruct Hverified as [_ HborrowValid].
  eapply HborrowValid.
  exact Hborrow.
Qed.

Theorem borrowed_value_is_not_an_owner :
  forall model view owner,
    ownershipRole model view = Some (BorrowedRole owner) ->
    ownershipRole model view <> Some OwningRole.
Proof.
  intros model view owner Hborrow Howner.
  rewrite Hborrow in Howner.
  discriminate.
Qed.

Record RecognitionModel : Type := mkRecognitionModel {
  recognitionPending : ValueId;
  recognitionRawView : ValueId;
  recognitionFrameOwner : ValueId;
  recognitionSuccessBlock : BlockId;
  recognitionFailureBlock : BlockId;
  recognitionBorrowOwner : ValueId -> option ValueId;
  recognitionCommitBlock : ValueId -> option BlockId;
  recognitionDestroyBlock : ValueId -> option BlockId;
  recognitionTransportBeforeCommit : ValueId -> bool
}.

Definition RecognitionVerificationSuccess (model : RecognitionModel) : Prop :=
  recognitionBorrowOwner model (recognitionRawView model) =
    Some (recognitionFrameOwner model) /\
  recognitionCommitBlock model (recognitionPending model) =
    Some (recognitionSuccessBlock model) /\
  recognitionDestroyBlock model (recognitionPending model) =
    Some (recognitionFailureBlock model) /\
  recognitionTransportBeforeCommit model (recognitionPending model) = false.

Theorem verified_recognition_raw_view_borrows_frame_owner :
  forall model,
    RecognitionVerificationSuccess model ->
    recognitionBorrowOwner model (recognitionRawView model) =
      Some (recognitionFrameOwner model).
Proof.
  intros model Hverified.
  destruct Hverified as [Hborrow _].
  exact Hborrow.
Qed.

Theorem verified_recognition_success_commits_exact_pending :
  forall model,
    RecognitionVerificationSuccess model ->
    recognitionCommitBlock model (recognitionPending model) =
      Some (recognitionSuccessBlock model).
Proof.
  intros model Hverified.
  destruct Hverified as [_ [Hcommit _]].
  exact Hcommit.
Qed.

Theorem verified_recognition_failure_destroys_exact_pending :
  forall model,
    RecognitionVerificationSuccess model ->
    recognitionDestroyBlock model (recognitionPending model) =
      Some (recognitionFailureBlock model).
Proof.
  intros model Hverified.
  destruct Hverified as [_ [_ [Hdestroy _]]].
  exact Hdestroy.
Qed.

Theorem verified_recognition_has_no_transport_use_before_commit :
  forall model,
    RecognitionVerificationSuccess model ->
    recognitionTransportBeforeCommit model (recognitionPending model) = false.
Proof.
  intros model Hverified.
  destruct Hverified as [_ [_ [_ Hbefore]]].
  exact Hbefore.
Qed.

Inductive PendingOperationKind : Type :=
| CommitOperation
| DestroyOperation.

Record PendingOperationModel : Type := mkPendingOperationModel {
  operationPending : ValueId;
  operationBlock : BlockId;
  operationSuccessTarget : ValueId -> option BlockId;
  operationFailureTarget : ValueId -> option BlockId
}.

Definition PendingOperationVerificationSuccess
  (kind : PendingOperationKind)
  (model : PendingOperationModel) : Prop :=
  match kind with
  | CommitOperation =>
      operationSuccessTarget model (operationPending model) =
        Some (operationBlock model)
  | DestroyOperation =>
      operationFailureTarget model (operationPending model) =
        Some (operationBlock model)
  end.

Theorem verified_commit_has_recognition_success_parent :
  forall model,
    PendingOperationVerificationSuccess CommitOperation model ->
    operationSuccessTarget model (operationPending model) =
      Some (operationBlock model).
Proof.
  intros model Hverified.
  exact Hverified.
Qed.

Theorem verified_destroy_has_recognition_failure_parent :
  forall model,
    PendingOperationVerificationSuccess DestroyOperation model ->
    operationFailureTarget model (operationPending model) =
      Some (operationBlock model).
Proof.
  intros model Hverified.
  exact Hverified.
Qed.

Theorem orphan_commit_is_rejected :
  forall model,
    operationSuccessTarget model (operationPending model) = None ->
    ~ PendingOperationVerificationSuccess CommitOperation model.
Proof.
  intros model Horphan Hverified.
  unfold PendingOperationVerificationSuccess in Hverified.
  rewrite Horphan in Hverified.
  discriminate.
Qed.

Theorem orphan_destroy_is_rejected :
  forall model,
    operationFailureTarget model (operationPending model) = None ->
    ~ PendingOperationVerificationSuccess DestroyOperation model.
Proof.
  intros model Horphan Hverified.
  unfold PendingOperationVerificationSuccess in Hverified.
  rewrite Horphan in Hverified.
  discriminate.
Qed.
