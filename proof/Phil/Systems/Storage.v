From Phil.Systems Require Import Identity DigestValidation.

(*
  PHIL-SYS-STORAGE-001 — normalized proof model for the Phase 0 storage
  boundary materialized by PR #52.

  Storage consumes the exact OwnedBuffer that fed DigestMatches and produces
  the semantic RuntimeScalar UploadId.  The digest-success edge must enter the
  exact storage block, there is exactly one store of that owner, and ownership
  is transferred to storage on every store outcome.  Consequently Phil source
  must not release or clean up that owner in the store/success/failure blocks
  after transfer.

  This proof does not claim that the concrete provider actually persists or
  frees bytes.  Those are external runtime gates.  It also does not choose an
  UploadId layout or wire encoding.
*)

Record SystemsStorageModel : Type := mkSystemsStorageModel {
  systemsStorageDigest : SystemsDigestValidationModel;

  systemsStorageWitnessOwner : ValueId;
  systemsStorageActualOwner : ValueId;
  systemsStorageWitnessResult : ValueId;
  systemsStorageActualResult : ValueId;
  systemsStorageResultIsUploadId : bool;

  systemsStorageWitnessBlock : DigestBlockId;
  systemsStorageActualBlock : DigestBlockId;
  systemsStorageWitnessSuccess : DigestBlockId;
  systemsStorageActualSuccess : DigestBlockId;
  systemsStorageWitnessFailure : DigestBlockId;
  systemsStorageActualFailure : DigestBlockId;

  systemsStorageBoundaryIsStorage : bool;
  systemsStorageCountForOwner : nat;
  systemsStorageTransfersOwnerOnAllOutcomes : bool;

  systemsStorageReleaseInStore : bool;
  systemsStorageReleaseInSuccess : bool;
  systemsStorageReleaseInFailure : bool
}.

Record SystemsStorageVerificationSuccess
  (model : SystemsStorageModel) : Prop :=
  mkSystemsStorageVerificationSuccess {
    systems_storage_success_digest :
      SystemsDigestValidationVerificationSuccess
        (systemsStorageDigest model);
    systems_storage_success_witness_owner :
      systemsStorageWitnessOwner model =
        systemsDigestPayloadOwner (systemsStorageDigest model);
    systems_storage_success_owner :
      systemsStorageActualOwner model = systemsStorageWitnessOwner model;
    systems_storage_success_result :
      systemsStorageActualResult model = systemsStorageWitnessResult model;
    systems_storage_success_upload_id_role :
      systemsStorageResultIsUploadId model = true;
    systems_storage_success_digest_predecessor :
      systemsDigestSuccessBlock (systemsStorageDigest model) =
        systemsStorageWitnessBlock model;
    systems_storage_success_block :
      systemsStorageActualBlock model = systemsStorageWitnessBlock model;
    systems_storage_success_boundary :
      systemsStorageBoundaryIsStorage model = true;
    systems_storage_success_single_store :
      systemsStorageCountForOwner model = 1;
    systems_storage_success_success_edge :
      systemsStorageActualSuccess model = systemsStorageWitnessSuccess model;
    systems_storage_success_failure_edge :
      systemsStorageActualFailure model = systemsStorageWitnessFailure model;
    systems_storage_success_transfer :
      systemsStorageTransfersOwnerOnAllOutcomes model = true;
    systems_storage_success_no_release_in_store :
      systemsStorageReleaseInStore model = false;
    systems_storage_success_no_release_in_success :
      systemsStorageReleaseInSuccess model = false;
    systems_storage_success_no_release_in_failure :
      systemsStorageReleaseInFailure model = false
  }.

Theorem verified_systems_storage_reuses_digest_authority :
  forall model,
    SystemsStorageVerificationSuccess model ->
    SystemsDigestValidationVerificationSuccess (systemsStorageDigest model).
Proof.
  intros model H.
  exact (systems_storage_success_digest model H).
Qed.

Theorem verified_systems_storage_digest_success_enters_exact_store :
  forall model,
    SystemsStorageVerificationSuccess model ->
    systemsDigestSuccessBlock (systemsStorageDigest model) =
      systemsStorageActualBlock model.
Proof.
  intros model H.
  rewrite (systems_storage_success_block model H).
  exact (systems_storage_success_digest_predecessor model H).
Qed.

Theorem verified_systems_storage_transfers_exact_payload_owner_once :
  forall model,
    SystemsStorageVerificationSuccess model ->
    systemsStorageActualOwner model =
      systemsDigestPayloadOwner (systemsStorageDigest model) /\
    systemsStorageCountForOwner model = 1 /\
    systemsStorageTransfersOwnerOnAllOutcomes model = true.
Proof.
  intros model H.
  repeat split.
  - rewrite (systems_storage_success_owner model H).
    exact (systems_storage_success_witness_owner model H).
  - exact (systems_storage_success_single_store model H).
  - exact (systems_storage_success_transfer model H).
Qed.

Theorem verified_systems_storage_produces_exact_upload_id_result :
  forall model,
    SystemsStorageVerificationSuccess model ->
    systemsStorageActualResult model = systemsStorageWitnessResult model /\
    systemsStorageResultIsUploadId model = true.
Proof.
  intros model H.
  split.
  - exact (systems_storage_success_result model H).
  - exact (systems_storage_success_upload_id_role model H).
Qed.

Theorem verified_systems_storage_preserves_exact_success_and_failure_edges :
  forall model,
    SystemsStorageVerificationSuccess model ->
    systemsStorageActualSuccess model = systemsStorageWitnessSuccess model /\
    systemsStorageActualFailure model = systemsStorageWitnessFailure model.
Proof.
  intros model H.
  split.
  - exact (systems_storage_success_success_edge model H).
  - exact (systems_storage_success_failure_edge model H).
Qed.

Theorem verified_systems_storage_has_no_post_transfer_release :
  forall model,
    SystemsStorageVerificationSuccess model ->
    systemsStorageReleaseInStore model = false /\
    systemsStorageReleaseInSuccess model = false /\
    systemsStorageReleaseInFailure model = false.
Proof.
  intros model H.
  repeat split.
  - exact (systems_storage_success_no_release_in_store model H).
  - exact (systems_storage_success_no_release_in_success model H).
  - exact (systems_storage_success_no_release_in_failure model H).
Qed.

Theorem systems_storage_owner_drift_is_rejected :
  forall model,
    systemsStorageActualOwner model <> systemsStorageWitnessOwner model ->
    ~ SystemsStorageVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (systems_storage_success_owner model H).
Qed.

Theorem systems_storage_result_identity_or_role_drift_is_rejected :
  forall model,
    systemsStorageActualResult model <> systemsStorageWitnessResult model \/
    systemsStorageResultIsUploadId model = false ->
    ~ SystemsStorageVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Hresult | Hrole].
  - apply Hresult. exact (systems_storage_success_result model H).
  - rewrite (systems_storage_success_upload_id_role model H) in Hrole.
    discriminate.
Qed.

Theorem systems_storage_multiplicity_or_boundary_drift_is_rejected :
  forall model,
    systemsStorageCountForOwner model <> 1 \/
    systemsStorageBoundaryIsStorage model = false ->
    ~ SystemsStorageVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Hcount | Hboundary].
  - apply Hcount. exact (systems_storage_success_single_store model H).
  - rewrite (systems_storage_success_boundary model H) in Hboundary.
    discriminate.
Qed.

Theorem systems_storage_predecessor_or_block_drift_is_rejected :
  forall model,
    systemsDigestSuccessBlock (systemsStorageDigest model) <>
      systemsStorageWitnessBlock model \/
    systemsStorageActualBlock model <> systemsStorageWitnessBlock model ->
    ~ SystemsStorageVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Hpred | Hblock].
  - apply Hpred. exact (systems_storage_success_digest_predecessor model H).
  - apply Hblock. exact (systems_storage_success_block model H).
Qed.

Theorem systems_storage_edge_drift_is_rejected :
  forall model,
    systemsStorageActualSuccess model <> systemsStorageWitnessSuccess model \/
    systemsStorageActualFailure model <> systemsStorageWitnessFailure model ->
    ~ SystemsStorageVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Hsuccess | Hfailure].
  - apply Hsuccess. exact (systems_storage_success_success_edge model H).
  - apply Hfailure. exact (systems_storage_success_failure_edge model H).
Qed.

Theorem systems_storage_missing_ownership_transfer_is_rejected :
  forall model,
    systemsStorageTransfersOwnerOnAllOutcomes model = false ->
    ~ SystemsStorageVerificationSuccess model.
Proof.
  intros model Hmissing H.
  rewrite (systems_storage_success_transfer model H) in Hmissing.
  discriminate.
Qed.

Theorem systems_storage_post_transfer_release_is_rejected :
  forall model,
    systemsStorageReleaseInStore model = true \/
    systemsStorageReleaseInSuccess model = true \/
    systemsStorageReleaseInFailure model = true ->
    ~ SystemsStorageVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hstore | [Hsuccess | Hfailure]].
  - rewrite (systems_storage_success_no_release_in_store model H) in Hstore.
    discriminate.
  - rewrite (systems_storage_success_no_release_in_success model H) in Hsuccess.
    discriminate.
  - rewrite (systems_storage_success_no_release_in_failure model H) in Hfailure.
    discriminate.
Qed.
