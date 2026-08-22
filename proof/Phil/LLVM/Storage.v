From Phil.Systems Require Import ScalarDataflow Storage.
From Phil.LLVM Require Import DigestValidation RuntimeSymbolIdentity.

(*
  PHIL-LLVM-STORAGE-001 — normalized proof model for the concrete storage-v1
  lowering introduced by PR #52.

  The exact payload owner proven at DigestMatches is passed to the physical
  store primitive, ownership transfers to storage, and the result is carried as
  the exact semantic UploadId handle.  Only status 1 is accepted as success.
  UploadId remains opaque, runtime-managed, non-owning, and usable by identity
  through the calling component return; generated code does not inspect,
  release, or strengthen it.

  The provider-side convention that a conforming failure returns a null
  UploadId is intentionally not a premise of this theorem.  A reserved or
  failure status is rejected independently of pointer contents.  Provider ABI
  conformance, persistence, ownership consumption, LLVM, and native execution
  remain external gates.
*)

Definition StorageOperandId := nat.
Definition StorageLLVMBlockId := nat.
Definition StorageStatusValue := nat.
Definition storageSuccessStatus : StorageStatusValue := 1.

Record StorageLLVMModel : Type := mkStorageLLVMModel {
  llvmStorageSystems : SystemsStorageModel;
  llvmStorageDigest : DigestValidationLLVMModel;
  llvmStorageRuntimeSymbols : RuntimeSymbolModel;

  llvmStoragePayloadSSAFor : ValueId -> StorageOperandId;
  llvmStorageUploadIdSSAFor : ValueId -> StorageOperandId;
  llvmStorageBlockSSAFor : DigestBlockId -> StorageLLVMBlockId;

  llvmStorageExpectedPayloadOperand : StorageOperandId;
  llvmStorageActualPayloadOperand : StorageOperandId;
  llvmStorageExpectedUploadIdResult : StorageOperandId;
  llvmStorageActualUploadIdResult : StorageOperandId;

  llvmStorageComparedStatus : StorageStatusValue;
  llvmStorageUsesExactStatusEquality : bool;
  llvmStorageActualSuccessBlock : StorageLLVMBlockId;
  llvmStorageActualFailureBlock : StorageLLVMBlockId;

  llvmStorageOwnershipTransferred : bool;
  llvmStoragePostTransferReleasePresent : bool;

  llvmStorageUploadIdOpaque : bool;
  llvmStorageUploadIdRuntimeManaged : bool;
  llvmStorageUploadIdNonowning : bool;
  llvmStorageUploadIdLifetimeThroughReturn : bool;
  llvmStorageUploadIdLayoutAccessPresent : bool;
  llvmStorageUploadIdReleasePresent : bool;

  llvmStorageAmbientPayloadPresent : bool;
  llvmStorageAmbientUploadIdPresent : bool;
  llvmStorageNullaryStorePresent : bool;
  llvmStorageUnauthorizedPointerStrengtheningPresent : bool
}.

Record StorageLLVMVerificationSuccess
  (model : StorageLLVMModel) : Prop :=
  mkStorageLLVMVerificationSuccess {
    llvm_storage_success_systems :
      SystemsStorageVerificationSuccess (llvmStorageSystems model);
    llvm_storage_success_digest :
      DigestValidationLLVMVerificationSuccess (llvmStorageDigest model);
    llvm_storage_success_runtime_symbols :
      RuntimeSymbolVerificationSuccess (llvmStorageRuntimeSymbols model);
    llvm_storage_success_digest_systems_align :
      llvmDigestSystems (llvmStorageDigest model) =
        systemsStorageDigest (llvmStorageSystems model);

    llvm_storage_success_expected_payload :
      llvmStorageExpectedPayloadOperand model =
        llvmStoragePayloadSSAFor model
          (systemsStorageWitnessOwner (llvmStorageSystems model));
    llvm_storage_success_digest_payload_correspondence :
      llvmDigestActualPayloadOperand (llvmStorageDigest model) =
        llvmStorageExpectedPayloadOperand model;
    llvm_storage_success_payload_operand :
      llvmStorageActualPayloadOperand model =
        llvmStorageExpectedPayloadOperand model;

    llvm_storage_success_expected_upload_id :
      llvmStorageExpectedUploadIdResult model =
        llvmStorageUploadIdSSAFor model
          (systemsStorageWitnessResult (llvmStorageSystems model));
    llvm_storage_success_upload_id_result :
      llvmStorageActualUploadIdResult model =
        llvmStorageExpectedUploadIdResult model;

    llvm_storage_success_status_one :
      llvmStorageComparedStatus model = storageSuccessStatus;
    llvm_storage_success_exact_status_equality :
      llvmStorageUsesExactStatusEquality model = true;
    llvm_storage_success_success_edge :
      llvmStorageActualSuccessBlock model =
        llvmStorageBlockSSAFor model
          (systemsStorageWitnessSuccess (llvmStorageSystems model));
    llvm_storage_success_failure_edge :
      llvmStorageActualFailureBlock model =
        llvmStorageBlockSSAFor model
          (systemsStorageWitnessFailure (llvmStorageSystems model));

    llvm_storage_success_transfer :
      llvmStorageOwnershipTransferred model = true;
    llvm_storage_success_no_post_transfer_release :
      llvmStoragePostTransferReleasePresent model = false;

    llvm_storage_success_upload_id_opaque :
      llvmStorageUploadIdOpaque model = true;
    llvm_storage_success_upload_id_runtime_managed :
      llvmStorageUploadIdRuntimeManaged model = true;
    llvm_storage_success_upload_id_nonowning :
      llvmStorageUploadIdNonowning model = true;
    llvm_storage_success_upload_id_lifetime :
      llvmStorageUploadIdLifetimeThroughReturn model = true;
    llvm_storage_success_no_upload_id_layout_access :
      llvmStorageUploadIdLayoutAccessPresent model = false;
    llvm_storage_success_no_upload_id_release :
      llvmStorageUploadIdReleasePresent model = false;

    llvm_storage_success_no_ambient_payload :
      llvmStorageAmbientPayloadPresent model = false;
    llvm_storage_success_no_ambient_upload_id :
      llvmStorageAmbientUploadIdPresent model = false;
    llvm_storage_success_no_nullary_store :
      llvmStorageNullaryStorePresent model = false;
    llvm_storage_success_no_unauthorized_strengthening :
      llvmStorageUnauthorizedPointerStrengtheningPresent model = false
  }.

Theorem verified_llvm_storage_reuses_systems_storage_authority :
  forall model,
    StorageLLVMVerificationSuccess model ->
    SystemsStorageVerificationSuccess (llvmStorageSystems model).
Proof.
  intros model H.
  exact (llvm_storage_success_systems model H).
Qed.

Theorem verified_llvm_storage_reuses_digest_authority :
  forall model,
    StorageLLVMVerificationSuccess model ->
    DigestValidationLLVMVerificationSuccess (llvmStorageDigest model) /\
    llvmDigestSystems (llvmStorageDigest model) =
      systemsStorageDigest (llvmStorageSystems model).
Proof.
  intros model H.
  split.
  - exact (llvm_storage_success_digest model H).
  - exact (llvm_storage_success_digest_systems_align model H).
Qed.

Theorem verified_llvm_storage_reuses_runtime_symbol_authority :
  forall model,
    StorageLLVMVerificationSuccess model ->
    RuntimeSymbolVerificationSuccess (llvmStorageRuntimeSymbols model).
Proof.
  intros model H.
  exact (llvm_storage_success_runtime_symbols model H).
Qed.

Theorem verified_llvm_storage_preserves_exact_payload_owner_from_digest :
  forall model,
    StorageLLVMVerificationSuccess model ->
    llvmStorageActualPayloadOperand model =
      llvmStoragePayloadSSAFor model
        (systemsStorageWitnessOwner (llvmStorageSystems model)) /\
    llvmDigestActualPayloadOperand (llvmStorageDigest model) =
      llvmStorageActualPayloadOperand model.
Proof.
  intros model H.
  split.
  - rewrite (llvm_storage_success_payload_operand model H).
    exact (llvm_storage_success_expected_payload model H).
  - rewrite (llvm_storage_success_payload_operand model H).
    exact (llvm_storage_success_digest_payload_correspondence model H).
Qed.

Theorem verified_llvm_storage_preserves_exact_upload_id_identity_and_opacity :
  forall model,
    StorageLLVMVerificationSuccess model ->
    llvmStorageActualUploadIdResult model =
      llvmStorageUploadIdSSAFor model
        (systemsStorageWitnessResult (llvmStorageSystems model)) /\
    llvmStorageUploadIdOpaque model = true /\
    llvmStorageUploadIdRuntimeManaged model = true /\
    llvmStorageUploadIdNonowning model = true /\
    llvmStorageUploadIdLifetimeThroughReturn model = true.
Proof.
  intros model H.
  repeat split.
  - rewrite (llvm_storage_success_upload_id_result model H).
    exact (llvm_storage_success_expected_upload_id model H).
  - exact (llvm_storage_success_upload_id_opaque model H).
  - exact (llvm_storage_success_upload_id_runtime_managed model H).
  - exact (llvm_storage_success_upload_id_nonowning model H).
  - exact (llvm_storage_success_upload_id_lifetime model H).
Qed.

Theorem verified_llvm_storage_uses_exact_status_one_and_exact_edges :
  forall model,
    StorageLLVMVerificationSuccess model ->
    llvmStorageComparedStatus model = 1 /\
    llvmStorageUsesExactStatusEquality model = true /\
    llvmStorageActualSuccessBlock model =
      llvmStorageBlockSSAFor model
        (systemsStorageWitnessSuccess (llvmStorageSystems model)) /\
    llvmStorageActualFailureBlock model =
      llvmStorageBlockSSAFor model
        (systemsStorageWitnessFailure (llvmStorageSystems model)).
Proof.
  intros model H.
  repeat split.
  - exact (llvm_storage_success_status_one model H).
  - exact (llvm_storage_success_exact_status_equality model H).
  - exact (llvm_storage_success_success_edge model H).
  - exact (llvm_storage_success_failure_edge model H).
Qed.

Theorem verified_llvm_storage_transfers_owner_without_generated_release :
  forall model,
    StorageLLVMVerificationSuccess model ->
    llvmStorageOwnershipTransferred model = true /\
    llvmStoragePostTransferReleasePresent model = false.
Proof.
  intros model H.
  split.
  - exact (llvm_storage_success_transfer model H).
  - exact (llvm_storage_success_no_post_transfer_release model H).
Qed.

Theorem verified_llvm_storage_forbids_upload_id_layout_release_ambient_state_and_strengthening :
  forall model,
    StorageLLVMVerificationSuccess model ->
    llvmStorageUploadIdLayoutAccessPresent model = false /\
    llvmStorageUploadIdReleasePresent model = false /\
    llvmStorageAmbientPayloadPresent model = false /\
    llvmStorageAmbientUploadIdPresent model = false /\
    llvmStorageNullaryStorePresent model = false /\
    llvmStorageUnauthorizedPointerStrengtheningPresent model = false.
Proof.
  intros model H.
  repeat split.
  - exact (llvm_storage_success_no_upload_id_layout_access model H).
  - exact (llvm_storage_success_no_upload_id_release model H).
  - exact (llvm_storage_success_no_ambient_payload model H).
  - exact (llvm_storage_success_no_ambient_upload_id model H).
  - exact (llvm_storage_success_no_nullary_store model H).
  - exact (llvm_storage_success_no_unauthorized_strengthening model H).
Qed.

Theorem llvm_storage_payload_identity_drift_is_rejected :
  forall model,
    llvmStorageActualPayloadOperand model <>
      llvmStorageExpectedPayloadOperand model ->
    ~ StorageLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (llvm_storage_success_payload_operand model H).
Qed.

Theorem llvm_storage_upload_id_identity_drift_is_rejected :
  forall model,
    llvmStorageActualUploadIdResult model <>
      llvmStorageExpectedUploadIdResult model ->
    ~ StorageLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (llvm_storage_success_upload_id_result model H).
Qed.

Theorem llvm_storage_status_drift_is_rejected :
  forall model,
    llvmStorageComparedStatus model <> storageSuccessStatus \/
    llvmStorageUsesExactStatusEquality model = false ->
    ~ StorageLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Hstatus | Hequality].
  - apply Hstatus. exact (llvm_storage_success_status_one model H).
  - rewrite (llvm_storage_success_exact_status_equality model H) in Hequality.
    discriminate.
Qed.

Theorem llvm_storage_edge_drift_is_rejected :
  forall model,
    llvmStorageActualSuccessBlock model <>
      llvmStorageBlockSSAFor model
        (systemsStorageWitnessSuccess (llvmStorageSystems model)) \/
    llvmStorageActualFailureBlock model <>
      llvmStorageBlockSSAFor model
        (systemsStorageWitnessFailure (llvmStorageSystems model)) ->
    ~ StorageLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Hsuccess | Hfailure].
  - apply Hsuccess. exact (llvm_storage_success_success_edge model H).
  - apply Hfailure. exact (llvm_storage_success_failure_edge model H).
Qed.

Theorem llvm_storage_missing_transfer_or_post_transfer_release_is_rejected :
  forall model,
    llvmStorageOwnershipTransferred model = false \/
    llvmStoragePostTransferReleasePresent model = true ->
    ~ StorageLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Htransfer | Hrelease].
  - rewrite (llvm_storage_success_transfer model H) in Htransfer.
    discriminate.
  - rewrite (llvm_storage_success_no_post_transfer_release model H) in Hrelease.
    discriminate.
Qed.

Theorem llvm_storage_upload_id_representation_drift_is_rejected :
  forall model,
    llvmStorageUploadIdOpaque model = false \/
    llvmStorageUploadIdRuntimeManaged model = false \/
    llvmStorageUploadIdNonowning model = false \/
    llvmStorageUploadIdLifetimeThroughReturn model = false \/
    llvmStorageUploadIdLayoutAccessPresent model = true \/
    llvmStorageUploadIdReleasePresent model = true ->
    ~ StorageLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hopaque | [Hmanaged | [Hnonowning | [Hlifetime | [Hlayout | Hrelease]]]]].
  - rewrite (llvm_storage_success_upload_id_opaque model H) in Hopaque. discriminate.
  - rewrite (llvm_storage_success_upload_id_runtime_managed model H) in Hmanaged. discriminate.
  - rewrite (llvm_storage_success_upload_id_nonowning model H) in Hnonowning. discriminate.
  - rewrite (llvm_storage_success_upload_id_lifetime model H) in Hlifetime. discriminate.
  - rewrite (llvm_storage_success_no_upload_id_layout_access model H) in Hlayout. discriminate.
  - rewrite (llvm_storage_success_no_upload_id_release model H) in Hrelease. discriminate.
Qed.

Theorem llvm_storage_ambient_or_strengthening_drift_is_rejected :
  forall model,
    llvmStorageAmbientPayloadPresent model = true \/
    llvmStorageAmbientUploadIdPresent model = true \/
    llvmStorageNullaryStorePresent model = true \/
    llvmStorageUnauthorizedPointerStrengtheningPresent model = true ->
    ~ StorageLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hpayload | [Hupload | [Hnullary | Hstrengthening]]].
  - rewrite (llvm_storage_success_no_ambient_payload model H) in Hpayload. discriminate.
  - rewrite (llvm_storage_success_no_ambient_upload_id model H) in Hupload. discriminate.
  - rewrite (llvm_storage_success_no_nullary_store model H) in Hnullary. discriminate.
  - rewrite (llvm_storage_success_no_unauthorized_strengthening model H) in Hstrengthening. discriminate.
Qed.
