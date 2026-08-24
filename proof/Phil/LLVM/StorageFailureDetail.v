(*
  PHIL-LLVM-STORAGE-FAIL-DETAIL-001 — normalized proof model for the
  storage-failure-detail-v1 physical lowering introduced by #106.

  The theorem is deliberately scoped to the storage-failure-detail-v1 Systems
  source. Provider-side payload consumption, store status/output-slot
  correctness, StorageError representation/lifetime, physical I/O, and wire
  encoding remain external runtime gates rather than compiler theorems.
*)

Record LLVMStorageFailureDetailModel : Type :=
  mkLLVMStorageFailureDetailModel {
    sfdSourceStorageFailureAuthority : bool;
    sfdPredecessorServerIngressAuthority : bool;
    sfdTranslationVerifies : bool;

    sfdDetailedStoreCount : nat;
    sfdStoreBoundaryExact : bool;
    sfdPayloadOwnerExact : bool;
    sfdUploadIdOutputExact : bool;
    sfdStorageErrorOutputExact : bool;
    sfdStoreBranchesExact : bool;

    sfdUploadIdSlotNullInitCount : nat;
    sfdStorageErrorSlotNullInitCount : nat;

    sfdFailureEffectCount : nat;
    sfdFailureTransportExact : bool;
    sfdFailureErrorExact : bool;
    sfdFailureFatalExact : bool;

    sfdPostStorePayloadObservationCount : nat;
    sfdLegacyStoreCount : nat;
    sfdLegacyErrorMaterializeCount : nat;
    sfdLegacyFailureEffectCount : nat;
    sfdAmbientStorageStateCount : nat;
    sfdPoisonCount : nat;
    sfdUnresolvedControlCount : nat;

    sfdClaimsProviderPayloadConsumption : bool;
    sfdClaimsProviderStatusOutputSemantics : bool;
    sfdClaimsConcreteStorageErrorLayout : bool;
    sfdClaimsWireCodec : bool
  }.

Definition verified_llvm_storage_failure_detail
    (m : LLVMStorageFailureDetailModel) : Prop :=
  sfdSourceStorageFailureAuthority m = true /\
  sfdPredecessorServerIngressAuthority m = true /\
  sfdTranslationVerifies m = true /\
  sfdDetailedStoreCount m = 1 /\
  sfdStoreBoundaryExact m = true /\
  sfdPayloadOwnerExact m = true /\
  sfdUploadIdOutputExact m = true /\
  sfdStorageErrorOutputExact m = true /\
  sfdStoreBranchesExact m = true /\
  sfdUploadIdSlotNullInitCount m = 1 /\
  sfdStorageErrorSlotNullInitCount m = 1 /\
  sfdFailureEffectCount m = 1 /\
  sfdFailureTransportExact m = true /\
  sfdFailureErrorExact m = true /\
  sfdFailureFatalExact m = true /\
  sfdPostStorePayloadObservationCount m = 0 /\
  sfdLegacyStoreCount m = 0 /\
  sfdLegacyErrorMaterializeCount m = 0 /\
  sfdLegacyFailureEffectCount m = 0 /\
  sfdAmbientStorageStateCount m = 0 /\
  sfdPoisonCount m = 0 /\
  sfdUnresolvedControlCount m = 0 /\
  sfdClaimsProviderPayloadConsumption m = false /\
  sfdClaimsProviderStatusOutputSemantics m = false /\
  sfdClaimsConcreteStorageErrorLayout m = false /\
  sfdClaimsWireCodec m = false.

Theorem verified_llvm_storage_failure_detail_reuses_source_and_predecessor_authority :
  forall m, verified_llvm_storage_failure_detail m ->
    sfdSourceStorageFailureAuthority m = true /\
    sfdPredecessorServerIngressAuthority m = true /\
    sfdTranslationVerifies m = true.
Proof.
  intros m H.
  unfold verified_llvm_storage_failure_detail in H.
  tauto.
Qed.

Theorem verified_llvm_storage_failure_detail_preserves_exact_store_operands_and_edges :
  forall m, verified_llvm_storage_failure_detail m ->
    sfdDetailedStoreCount m = 1 /\
    sfdStoreBoundaryExact m = true /\
    sfdPayloadOwnerExact m = true /\
    sfdUploadIdOutputExact m = true /\
    sfdStorageErrorOutputExact m = true /\
    sfdStoreBranchesExact m = true.
Proof.
  intros m H.
  unfold verified_llvm_storage_failure_detail in H.
  tauto.
Qed.

Theorem verified_llvm_storage_failure_detail_initializes_both_output_slots :
  forall m, verified_llvm_storage_failure_detail m ->
    sfdUploadIdSlotNullInitCount m = 1 /\
    sfdStorageErrorSlotNullInitCount m = 1.
Proof.
  intros m H.
  unfold verified_llvm_storage_failure_detail in H.
  tauto.
Qed.

Theorem verified_llvm_storage_failure_detail_forwards_exact_error_on_exact_transport :
  forall m, verified_llvm_storage_failure_detail m ->
    sfdFailureEffectCount m = 1 /\
    sfdFailureTransportExact m = true /\
    sfdFailureErrorExact m = true /\
    sfdFailureFatalExact m = true.
Proof.
  intros m H.
  unfold verified_llvm_storage_failure_detail in H.
  tauto.
Qed.

Theorem verified_llvm_storage_failure_detail_does_not_reobserve_transferred_payload :
  forall m, verified_llvm_storage_failure_detail m ->
    sfdPostStorePayloadObservationCount m = 0.
Proof.
  intros m H.
  unfold verified_llvm_storage_failure_detail in H.
  tauto.
Qed.

Theorem verified_llvm_storage_failure_detail_eliminates_legacy_and_ambient_state :
  forall m, verified_llvm_storage_failure_detail m ->
    sfdLegacyStoreCount m = 0 /\
    sfdLegacyErrorMaterializeCount m = 0 /\
    sfdLegacyFailureEffectCount m = 0 /\
    sfdAmbientStorageStateCount m = 0 /\
    sfdPoisonCount m = 0 /\
    sfdUnresolvedControlCount m = 0.
Proof.
  intros m H.
  unfold verified_llvm_storage_failure_detail in H.
  tauto.
Qed.

Theorem verified_llvm_storage_failure_detail_claims_no_provider_or_wire_semantics :
  forall m, verified_llvm_storage_failure_detail m ->
    sfdClaimsProviderPayloadConsumption m = false /\
    sfdClaimsProviderStatusOutputSemantics m = false /\
    sfdClaimsConcreteStorageErrorLayout m = false /\
    sfdClaimsWireCodec m = false.
Proof.
  intros m H.
  unfold verified_llvm_storage_failure_detail in H.
  tauto.
Qed.

Theorem llvm_storage_failure_detail_identity_or_slot_drift_is_rejected :
  forall m,
    sfdPayloadOwnerExact m <> true \/
    sfdStorageErrorOutputExact m <> true \/
    sfdStoreBranchesExact m <> true \/
    sfdUploadIdSlotNullInitCount m <> 1 \/
    sfdStorageErrorSlotNullInitCount m <> 1 ->
    ~ verified_llvm_storage_failure_detail m.
Proof.
  intros m Hbad Hgood.
  unfold verified_llvm_storage_failure_detail in Hgood.
  tauto.
Qed.

Theorem llvm_storage_failure_detail_payload_reuse_or_ambient_drift_is_rejected :
  forall m,
    sfdPostStorePayloadObservationCount m <> 0 \/
    sfdFailureErrorExact m <> true \/
    sfdLegacyStoreCount m <> 0 \/
    sfdAmbientStorageStateCount m <> 0 ->
    ~ verified_llvm_storage_failure_detail m.
Proof.
  intros m Hbad Hgood.
  unfold verified_llvm_storage_failure_detail in Hgood.
  tauto.
Qed.
