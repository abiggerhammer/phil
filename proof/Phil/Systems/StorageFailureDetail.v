(*
  PHIL-SYS-STORAGE-FAIL-DETAIL-001 — normalized proof model for the final
  Phase 0 storage failure-detail Systems successor.

  This proof certifies semantic error identity/forwarding and the ownership
  boundary around TermStore. Concrete provider error representation, storage
  ABI revision, diagnostics, physical I/O, and framing remain outside Systems.
*)

Definition StorageFailureDecisionId := nat.

Record SystemsStorageFailureDetailModel : Type :=
  mkSystemsStorageFailureDetailModel {
    storageFailureCurrentSuccessorVerifies : bool;
    storageFailureRecognitionPredecessorPreserved : bool;
    storageFailureClientOutboundPreserved : bool;

    storageFailureTransportExact : bool;
    storageFailurePayloadOwnerExact : bool;
    storageFailureUploadIdExact : bool;
    storageFailureStoreSiteExact : bool;
    storageFailureStoreSuccessContinuationExact : bool;
    storageFailureStoreFailureContinuationExact : bool;
    storageFailureConsumesOwnerOnAllOutcomes : bool;

    storageFailureErrorRoleExact : bool;
    storageFailureMaterializeCount : nat;
    storageFailureMaterializeHasNoInputs : bool;
    storageFailureMaterializeResultExact : bool;
    storageFailureEffectCount : nat;
    storageFailureEffectTransportExact : bool;
    storageFailureEffectErrorExact : bool;
    storageFailureFatalClassExact : bool;
    storageFailureErrorSemanticUseCount : nat;

    storageFailurePostTransferPayloadUseCount : nat;
    storageFailureNewPayloadOwnerCount : nat;
    storageFailureNewPayloadAliasCount : nat;

    storageFailureWitnessDecision : StorageFailureDecisionId;
    storageFailureActualDecision : StorageFailureDecisionId;
    storageFailureDecisionExact : bool;

    storageFailurePhysicalErrorRepresentationClaimed : bool;
    storageFailureRuntimeABIBroadened : bool;
    storageFailureWireEncodingClaimed : bool;
    storageFailureOuterFramingClaimed : bool
  }.

Record SystemsStorageFailureDetailVerificationSuccess
  (model : SystemsStorageFailureDetailModel) : Prop :=
  mkSystemsStorageFailureDetailVerificationSuccess {
    storage_failure_success_current :
      storageFailureCurrentSuccessorVerifies model = true;
    storage_failure_success_recognition :
      storageFailureRecognitionPredecessorPreserved model = true;
    storage_failure_success_client :
      storageFailureClientOutboundPreserved model = true;

    storage_failure_success_transport :
      storageFailureTransportExact model = true;
    storage_failure_success_owner :
      storageFailurePayloadOwnerExact model = true;
    storage_failure_success_upload_id :
      storageFailureUploadIdExact model = true;
    storage_failure_success_site :
      storageFailureStoreSiteExact model = true;
    storage_failure_success_success_cont :
      storageFailureStoreSuccessContinuationExact model = true;
    storage_failure_success_failure_cont :
      storageFailureStoreFailureContinuationExact model = true;
    storage_failure_success_consumes :
      storageFailureConsumesOwnerOnAllOutcomes model = true;

    storage_failure_success_error_role :
      storageFailureErrorRoleExact model = true;
    storage_failure_success_materialize_count :
      storageFailureMaterializeCount model = 1;
    storage_failure_success_materialize_inputs :
      storageFailureMaterializeHasNoInputs model = true;
    storage_failure_success_materialize_result :
      storageFailureMaterializeResultExact model = true;
    storage_failure_success_effect_count :
      storageFailureEffectCount model = 1;
    storage_failure_success_effect_transport :
      storageFailureEffectTransportExact model = true;
    storage_failure_success_effect_error :
      storageFailureEffectErrorExact model = true;
    storage_failure_success_fatal :
      storageFailureFatalClassExact model = true;
    storage_failure_success_error_use_count :
      storageFailureErrorSemanticUseCount model = 1;

    storage_failure_success_no_post_transfer_payload_use :
      storageFailurePostTransferPayloadUseCount model = 0;
    storage_failure_success_no_new_owner :
      storageFailureNewPayloadOwnerCount model = 0;
    storage_failure_success_no_new_alias :
      storageFailureNewPayloadAliasCount model = 0;

    storage_failure_success_decision_identity :
      storageFailureActualDecision model = storageFailureWitnessDecision model;
    storage_failure_success_decision_exact :
      storageFailureDecisionExact model = true;

    storage_failure_success_no_physical_error :
      storageFailurePhysicalErrorRepresentationClaimed model = false;
    storage_failure_success_no_abi_broadening :
      storageFailureRuntimeABIBroadened model = false;
    storage_failure_success_no_wire :
      storageFailureWireEncodingClaimed model = false;
    storage_failure_success_no_framing :
      storageFailureOuterFramingClaimed model = false
  }.

Theorem verified_systems_storage_failure_is_current_successor :
  forall model,
    SystemsStorageFailureDetailVerificationSuccess model ->
    storageFailureCurrentSuccessorVerifies model = true.
Proof. intros model H; exact (storage_failure_success_current model H). Qed.

Theorem verified_systems_storage_failure_preserves_predecessor_authority :
  forall model,
    SystemsStorageFailureDetailVerificationSuccess model ->
    storageFailureRecognitionPredecessorPreserved model = true /\
    storageFailureClientOutboundPreserved model = true.
Proof.
  intros model H; split.
  - exact (storage_failure_success_recognition model H).
  - exact (storage_failure_success_client model H).
Qed.

Theorem verified_systems_storage_failure_preserves_store_transfer_boundary :
  forall model,
    SystemsStorageFailureDetailVerificationSuccess model ->
    storageFailureTransportExact model = true /\
    storageFailurePayloadOwnerExact model = true /\
    storageFailureUploadIdExact model = true /\
    storageFailureStoreSiteExact model = true /\
    storageFailureStoreSuccessContinuationExact model = true /\
    storageFailureStoreFailureContinuationExact model = true /\
    storageFailureConsumesOwnerOnAllOutcomes model = true.
Proof.
  intros model H; repeat split.
  - exact (storage_failure_success_transport model H).
  - exact (storage_failure_success_owner model H).
  - exact (storage_failure_success_upload_id model H).
  - exact (storage_failure_success_site model H).
  - exact (storage_failure_success_success_cont model H).
  - exact (storage_failure_success_failure_cont model H).
  - exact (storage_failure_success_consumes model H).
Qed.

Theorem verified_systems_storage_failure_preserves_exact_error_flow :
  forall model,
    SystemsStorageFailureDetailVerificationSuccess model ->
    storageFailureErrorRoleExact model = true /\
    storageFailureMaterializeCount model = 1 /\
    storageFailureMaterializeHasNoInputs model = true /\
    storageFailureMaterializeResultExact model = true /\
    storageFailureEffectCount model = 1 /\
    storageFailureEffectTransportExact model = true /\
    storageFailureEffectErrorExact model = true /\
    storageFailureFatalClassExact model = true /\
    storageFailureErrorSemanticUseCount model = 1.
Proof.
  intros model H; repeat split.
  - exact (storage_failure_success_error_role model H).
  - exact (storage_failure_success_materialize_count model H).
  - exact (storage_failure_success_materialize_inputs model H).
  - exact (storage_failure_success_materialize_result model H).
  - exact (storage_failure_success_effect_count model H).
  - exact (storage_failure_success_effect_transport model H).
  - exact (storage_failure_success_effect_error model H).
  - exact (storage_failure_success_fatal model H).
  - exact (storage_failure_success_error_use_count model H).
Qed.

Theorem verified_systems_storage_failure_preserves_no_post_transfer_payload_use :
  forall model,
    SystemsStorageFailureDetailVerificationSuccess model ->
    storageFailurePostTransferPayloadUseCount model = 0 /\
    storageFailureNewPayloadOwnerCount model = 0 /\
    storageFailureNewPayloadAliasCount model = 0.
Proof.
  intros model H; repeat split.
  - exact (storage_failure_success_no_post_transfer_payload_use model H).
  - exact (storage_failure_success_no_new_owner model H).
  - exact (storage_failure_success_no_new_alias model H).
Qed.

Theorem verified_systems_storage_failure_binds_decision_and_claims_no_physical_error_abi :
  forall model,
    SystemsStorageFailureDetailVerificationSuccess model ->
    storageFailureActualDecision model = storageFailureWitnessDecision model /\
    storageFailureDecisionExact model = true /\
    storageFailurePhysicalErrorRepresentationClaimed model = false /\
    storageFailureRuntimeABIBroadened model = false /\
    storageFailureWireEncodingClaimed model = false /\
    storageFailureOuterFramingClaimed model = false.
Proof.
  intros model H; repeat split.
  - exact (storage_failure_success_decision_identity model H).
  - exact (storage_failure_success_decision_exact model H).
  - exact (storage_failure_success_no_physical_error model H).
  - exact (storage_failure_success_no_abi_broadening model H).
  - exact (storage_failure_success_no_wire model H).
  - exact (storage_failure_success_no_framing model H).
Qed.

Theorem systems_storage_failure_error_flow_drift_is_rejected :
  forall model,
    storageFailureErrorRoleExact model = false \/
    storageFailureMaterializeCount model <> 1 \/
    storageFailureMaterializeHasNoInputs model = false \/
    storageFailureMaterializeResultExact model = false \/
    storageFailureEffectCount model <> 1 \/
    storageFailureEffectTransportExact model = false \/
    storageFailureEffectErrorExact model = false \/
    storageFailureFatalClassExact model = false \/
    storageFailureErrorSemanticUseCount model <> 1 ->
    ~ SystemsStorageFailureDetailVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hrole | [Hmc | [Hmi | [Hmr | [Hec | [Het | [Hee | [Hfatal | Huse]]]]]]]].
  - rewrite (storage_failure_success_error_role model H) in Hrole. discriminate.
  - apply Hmc. exact (storage_failure_success_materialize_count model H).
  - rewrite (storage_failure_success_materialize_inputs model H) in Hmi. discriminate.
  - rewrite (storage_failure_success_materialize_result model H) in Hmr. discriminate.
  - apply Hec. exact (storage_failure_success_effect_count model H).
  - rewrite (storage_failure_success_effect_transport model H) in Het. discriminate.
  - rewrite (storage_failure_success_effect_error model H) in Hee. discriminate.
  - rewrite (storage_failure_success_fatal model H) in Hfatal. discriminate.
  - apply Huse. exact (storage_failure_success_error_use_count model H).
Qed.

Theorem systems_storage_failure_post_transfer_drift_is_rejected :
  forall model,
    storageFailurePayloadOwnerExact model = false \/
    storageFailureConsumesOwnerOnAllOutcomes model = false \/
    storageFailurePostTransferPayloadUseCount model <> 0 \/
    storageFailureNewPayloadOwnerCount model <> 0 \/
    storageFailureNewPayloadAliasCount model <> 0 ->
    ~ SystemsStorageFailureDetailVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Howner | [Hconsume | [Huse | [Hnew | Halias]]]].
  - rewrite (storage_failure_success_owner model H) in Howner. discriminate.
  - rewrite (storage_failure_success_consumes model H) in Hconsume. discriminate.
  - apply Huse. exact (storage_failure_success_no_post_transfer_payload_use model H).
  - apply Hnew. exact (storage_failure_success_no_new_owner model H).
  - apply Halias. exact (storage_failure_success_no_new_alias model H).
Qed.
