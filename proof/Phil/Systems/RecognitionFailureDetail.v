(*
  PHIL-SYS-RECOG-FAIL-DETAIL-001 — normalized proof model for the current
  Phase 0 recognition-failure detail successor.

  The theorem covers semantic reason identity and failure flow for the frozen
  Hello and Begin recognition failures. Concrete recognizer error objects,
  reason layout/lifetime, diagnostic ABI, wire encoding, and physical runtime
  representation remain outside this Systems theorem.
*)

Definition RecognitionFailureDecisionId := nat.

Record SystemsRecognitionFailureDetailModel : Type :=
  mkSystemsRecognitionFailureDetailModel {
    recognitionFailureCurrentSuccessorVerifies : bool;
    recognitionFailureStorageSuccessorPreservesWitness : bool;
    recognitionFailureClientOutboundAuthorityPreserved : bool;

    recognitionFailureHelloGateExact : bool;
    recognitionFailureHelloPendingExact : bool;
    recognitionFailureHelloFrameOwnerExact : bool;
    recognitionFailureHelloReasonExact : bool;
    recognitionFailureHelloReasonRoleExact : bool;
    recognitionFailureHelloMaterializeCount : nat;
    recognitionFailureHelloMaterializePendingExact : bool;
    recognitionFailureHelloMaterializeFailureOnly : bool;
    recognitionFailureHelloEffectCount : nat;
    recognitionFailureHelloEffectPendingExact : bool;
    recognitionFailureHelloEffectReasonExact : bool;
    recognitionFailureHelloCleanupCount : nat;
    recognitionFailureHelloCleanupPendingExact : bool;
    recognitionFailureHelloCleanupFrameExact : bool;
    recognitionFailureHelloFatalClassExact : bool;
    recognitionFailureHelloReasonUseCount : nat;

    recognitionFailureBeginGateExact : bool;
    recognitionFailureBeginPendingExact : bool;
    recognitionFailureBeginFrameOwnerExact : bool;
    recognitionFailureBeginReasonExact : bool;
    recognitionFailureBeginReasonRoleExact : bool;
    recognitionFailureBeginMaterializeCount : nat;
    recognitionFailureBeginMaterializePendingExact : bool;
    recognitionFailureBeginMaterializeFailureOnly : bool;
    recognitionFailureBeginEffectCount : nat;
    recognitionFailureBeginEffectPendingExact : bool;
    recognitionFailureBeginEffectReasonExact : bool;
    recognitionFailureBeginCleanupCount : nat;
    recognitionFailureBeginCleanupPendingExact : bool;
    recognitionFailureBeginCleanupFrameExact : bool;
    recognitionFailureBeginFatalClassExact : bool;
    recognitionFailureBeginReasonUseCount : nat;

    recognitionFailureReasonIdentitiesDistinct : bool;
    recognitionFailureSuccessPathsUnchanged : bool;

    recognitionFailureWitnessDecision : RecognitionFailureDecisionId;
    recognitionFailureActualDecision : RecognitionFailureDecisionId;
    recognitionFailureDecisionExact : bool;

    recognitionFailurePhysicalReasonRepresentationClaimed : bool;
    recognitionFailureRuntimeABIClaimed : bool;
    recognitionFailureDiagnosticABIClaimed : bool;
    recognitionFailureWireEncodingClaimed : bool;
    recognitionFailureOuterFramingClaimed : bool
  }.

Record SystemsRecognitionFailureDetailVerificationSuccess
  (model : SystemsRecognitionFailureDetailModel) : Prop :=
  mkSystemsRecognitionFailureDetailVerificationSuccess {
    recognition_failure_success_current :
      recognitionFailureCurrentSuccessorVerifies model = true;
    recognition_failure_success_storage_preserves :
      recognitionFailureStorageSuccessorPreservesWitness model = true;
    recognition_failure_success_client_outbound :
      recognitionFailureClientOutboundAuthorityPreserved model = true;

    recognition_failure_success_hello_gate :
      recognitionFailureHelloGateExact model = true;
    recognition_failure_success_hello_pending :
      recognitionFailureHelloPendingExact model = true;
    recognition_failure_success_hello_frame :
      recognitionFailureHelloFrameOwnerExact model = true;
    recognition_failure_success_hello_reason :
      recognitionFailureHelloReasonExact model = true;
    recognition_failure_success_hello_reason_role :
      recognitionFailureHelloReasonRoleExact model = true;
    recognition_failure_success_hello_materialize_count :
      recognitionFailureHelloMaterializeCount model = 1;
    recognition_failure_success_hello_materialize_pending :
      recognitionFailureHelloMaterializePendingExact model = true;
    recognition_failure_success_hello_failure_only :
      recognitionFailureHelloMaterializeFailureOnly model = true;
    recognition_failure_success_hello_effect_count :
      recognitionFailureHelloEffectCount model = 1;
    recognition_failure_success_hello_effect_pending :
      recognitionFailureHelloEffectPendingExact model = true;
    recognition_failure_success_hello_effect_reason :
      recognitionFailureHelloEffectReasonExact model = true;
    recognition_failure_success_hello_cleanup_count :
      recognitionFailureHelloCleanupCount model = 1;
    recognition_failure_success_hello_cleanup_pending :
      recognitionFailureHelloCleanupPendingExact model = true;
    recognition_failure_success_hello_cleanup_frame :
      recognitionFailureHelloCleanupFrameExact model = true;
    recognition_failure_success_hello_fatal :
      recognitionFailureHelloFatalClassExact model = true;
    recognition_failure_success_hello_use_count :
      recognitionFailureHelloReasonUseCount model = 1;

    recognition_failure_success_begin_gate :
      recognitionFailureBeginGateExact model = true;
    recognition_failure_success_begin_pending :
      recognitionFailureBeginPendingExact model = true;
    recognition_failure_success_begin_frame :
      recognitionFailureBeginFrameOwnerExact model = true;
    recognition_failure_success_begin_reason :
      recognitionFailureBeginReasonExact model = true;
    recognition_failure_success_begin_reason_role :
      recognitionFailureBeginReasonRoleExact model = true;
    recognition_failure_success_begin_materialize_count :
      recognitionFailureBeginMaterializeCount model = 1;
    recognition_failure_success_begin_materialize_pending :
      recognitionFailureBeginMaterializePendingExact model = true;
    recognition_failure_success_begin_failure_only :
      recognitionFailureBeginMaterializeFailureOnly model = true;
    recognition_failure_success_begin_effect_count :
      recognitionFailureBeginEffectCount model = 1;
    recognition_failure_success_begin_effect_pending :
      recognitionFailureBeginEffectPendingExact model = true;
    recognition_failure_success_begin_effect_reason :
      recognitionFailureBeginEffectReasonExact model = true;
    recognition_failure_success_begin_cleanup_count :
      recognitionFailureBeginCleanupCount model = 1;
    recognition_failure_success_begin_cleanup_pending :
      recognitionFailureBeginCleanupPendingExact model = true;
    recognition_failure_success_begin_cleanup_frame :
      recognitionFailureBeginCleanupFrameExact model = true;
    recognition_failure_success_begin_fatal :
      recognitionFailureBeginFatalClassExact model = true;
    recognition_failure_success_begin_use_count :
      recognitionFailureBeginReasonUseCount model = 1;

    recognition_failure_success_distinct_reasons :
      recognitionFailureReasonIdentitiesDistinct model = true;
    recognition_failure_success_success_paths :
      recognitionFailureSuccessPathsUnchanged model = true;

    recognition_failure_success_decision_identity :
      recognitionFailureActualDecision model =
        recognitionFailureWitnessDecision model;
    recognition_failure_success_decision_exact :
      recognitionFailureDecisionExact model = true;

    recognition_failure_success_no_reason_representation :
      recognitionFailurePhysicalReasonRepresentationClaimed model = false;
    recognition_failure_success_no_runtime_abi :
      recognitionFailureRuntimeABIClaimed model = false;
    recognition_failure_success_no_diagnostic_abi :
      recognitionFailureDiagnosticABIClaimed model = false;
    recognition_failure_success_no_wire_encoding :
      recognitionFailureWireEncodingClaimed model = false;
    recognition_failure_success_no_outer_framing :
      recognitionFailureOuterFramingClaimed model = false
  }.

Theorem verified_systems_recognition_failure_is_preserved_by_current_successor :
  forall model,
    SystemsRecognitionFailureDetailVerificationSuccess model ->
    recognitionFailureCurrentSuccessorVerifies model = true /\
    recognitionFailureStorageSuccessorPreservesWitness model = true /\
    recognitionFailureClientOutboundAuthorityPreserved model = true.
Proof.
  intros model H; repeat split.
  - exact (recognition_failure_success_current model H).
  - exact (recognition_failure_success_storage_preserves model H).
  - exact (recognition_failure_success_client_outbound model H).
Qed.

Theorem verified_systems_recognition_failure_preserves_exact_hello_failure_flow :
  forall model,
    SystemsRecognitionFailureDetailVerificationSuccess model ->
    recognitionFailureHelloGateExact model = true /\
    recognitionFailureHelloPendingExact model = true /\
    recognitionFailureHelloFrameOwnerExact model = true /\
    recognitionFailureHelloReasonExact model = true /\
    recognitionFailureHelloReasonRoleExact model = true /\
    recognitionFailureHelloMaterializeCount model = 1 /\
    recognitionFailureHelloMaterializePendingExact model = true /\
    recognitionFailureHelloMaterializeFailureOnly model = true /\
    recognitionFailureHelloEffectCount model = 1 /\
    recognitionFailureHelloEffectPendingExact model = true /\
    recognitionFailureHelloEffectReasonExact model = true /\
    recognitionFailureHelloCleanupCount model = 1 /\
    recognitionFailureHelloCleanupPendingExact model = true /\
    recognitionFailureHelloCleanupFrameExact model = true /\
    recognitionFailureHelloFatalClassExact model = true /\
    recognitionFailureHelloReasonUseCount model = 1.
Proof.
  intros model H; repeat split.
  - exact (recognition_failure_success_hello_gate model H).
  - exact (recognition_failure_success_hello_pending model H).
  - exact (recognition_failure_success_hello_frame model H).
  - exact (recognition_failure_success_hello_reason model H).
  - exact (recognition_failure_success_hello_reason_role model H).
  - exact (recognition_failure_success_hello_materialize_count model H).
  - exact (recognition_failure_success_hello_materialize_pending model H).
  - exact (recognition_failure_success_hello_failure_only model H).
  - exact (recognition_failure_success_hello_effect_count model H).
  - exact (recognition_failure_success_hello_effect_pending model H).
  - exact (recognition_failure_success_hello_effect_reason model H).
  - exact (recognition_failure_success_hello_cleanup_count model H).
  - exact (recognition_failure_success_hello_cleanup_pending model H).
  - exact (recognition_failure_success_hello_cleanup_frame model H).
  - exact (recognition_failure_success_hello_fatal model H).
  - exact (recognition_failure_success_hello_use_count model H).
Qed.

Theorem verified_systems_recognition_failure_preserves_exact_begin_failure_flow :
  forall model,
    SystemsRecognitionFailureDetailVerificationSuccess model ->
    recognitionFailureBeginGateExact model = true /\
    recognitionFailureBeginPendingExact model = true /\
    recognitionFailureBeginFrameOwnerExact model = true /\
    recognitionFailureBeginReasonExact model = true /\
    recognitionFailureBeginReasonRoleExact model = true /\
    recognitionFailureBeginMaterializeCount model = 1 /\
    recognitionFailureBeginMaterializePendingExact model = true /\
    recognitionFailureBeginMaterializeFailureOnly model = true /\
    recognitionFailureBeginEffectCount model = 1 /\
    recognitionFailureBeginEffectPendingExact model = true /\
    recognitionFailureBeginEffectReasonExact model = true /\
    recognitionFailureBeginCleanupCount model = 1 /\
    recognitionFailureBeginCleanupPendingExact model = true /\
    recognitionFailureBeginCleanupFrameExact model = true /\
    recognitionFailureBeginFatalClassExact model = true /\
    recognitionFailureBeginReasonUseCount model = 1.
Proof.
  intros model H; repeat split.
  - exact (recognition_failure_success_begin_gate model H).
  - exact (recognition_failure_success_begin_pending model H).
  - exact (recognition_failure_success_begin_frame model H).
  - exact (recognition_failure_success_begin_reason model H).
  - exact (recognition_failure_success_begin_reason_role model H).
  - exact (recognition_failure_success_begin_materialize_count model H).
  - exact (recognition_failure_success_begin_materialize_pending model H).
  - exact (recognition_failure_success_begin_failure_only model H).
  - exact (recognition_failure_success_begin_effect_count model H).
  - exact (recognition_failure_success_begin_effect_pending model H).
  - exact (recognition_failure_success_begin_effect_reason model H).
  - exact (recognition_failure_success_begin_cleanup_count model H).
  - exact (recognition_failure_success_begin_cleanup_pending model H).
  - exact (recognition_failure_success_begin_cleanup_frame model H).
  - exact (recognition_failure_success_begin_fatal model H).
  - exact (recognition_failure_success_begin_use_count model H).
Qed.

Theorem verified_systems_recognition_failure_preserves_distinct_single_use_reasons :
  forall model,
    SystemsRecognitionFailureDetailVerificationSuccess model ->
    recognitionFailureReasonIdentitiesDistinct model = true /\
    recognitionFailureHelloReasonUseCount model = 1 /\
    recognitionFailureBeginReasonUseCount model = 1 /\
    recognitionFailureSuccessPathsUnchanged model = true.
Proof.
  intros model H; repeat split.
  - exact (recognition_failure_success_distinct_reasons model H).
  - exact (recognition_failure_success_hello_use_count model H).
  - exact (recognition_failure_success_begin_use_count model H).
  - exact (recognition_failure_success_success_paths model H).
Qed.

Theorem verified_systems_recognition_failure_binds_decision_and_claims_no_physical_representation :
  forall model,
    SystemsRecognitionFailureDetailVerificationSuccess model ->
    recognitionFailureActualDecision model =
      recognitionFailureWitnessDecision model /\
    recognitionFailureDecisionExact model = true /\
    recognitionFailurePhysicalReasonRepresentationClaimed model = false /\
    recognitionFailureRuntimeABIClaimed model = false /\
    recognitionFailureDiagnosticABIClaimed model = false /\
    recognitionFailureWireEncodingClaimed model = false /\
    recognitionFailureOuterFramingClaimed model = false.
Proof.
  intros model H; repeat split.
  - exact (recognition_failure_success_decision_identity model H).
  - exact (recognition_failure_success_decision_exact model H).
  - exact (recognition_failure_success_no_reason_representation model H).
  - exact (recognition_failure_success_no_runtime_abi model H).
  - exact (recognition_failure_success_no_diagnostic_abi model H).
  - exact (recognition_failure_success_no_wire_encoding model H).
  - exact (recognition_failure_success_no_outer_framing model H).
Qed.

Theorem systems_recognition_failure_reason_or_provenance_drift_is_rejected :
  forall model,
    recognitionFailureReasonIdentitiesDistinct model = false \/
    recognitionFailureHelloReasonRoleExact model = false \/
    recognitionFailureBeginReasonRoleExact model = false \/
    recognitionFailureHelloMaterializePendingExact model = false \/
    recognitionFailureBeginMaterializePendingExact model = false \/
    recognitionFailureHelloEffectReasonExact model = false \/
    recognitionFailureBeginEffectReasonExact model = false ->
    ~ SystemsRecognitionFailureDetailVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hdistinct | [Hhr | [Hbr | [Hhp | [Hbp | [Hhe | Hbe]]]]]].
  - rewrite (recognition_failure_success_distinct_reasons model H) in Hdistinct. discriminate.
  - rewrite (recognition_failure_success_hello_reason_role model H) in Hhr. discriminate.
  - rewrite (recognition_failure_success_begin_reason_role model H) in Hbr. discriminate.
  - rewrite (recognition_failure_success_hello_materialize_pending model H) in Hhp. discriminate.
  - rewrite (recognition_failure_success_begin_materialize_pending model H) in Hbp. discriminate.
  - rewrite (recognition_failure_success_hello_effect_reason model H) in Hhe. discriminate.
  - rewrite (recognition_failure_success_begin_effect_reason model H) in Hbe. discriminate.
Qed.

Theorem systems_recognition_failure_cleanup_or_terminal_drift_is_rejected :
  forall model,
    recognitionFailureHelloCleanupCount model <> 1 \/
    recognitionFailureBeginCleanupCount model <> 1 \/
    recognitionFailureHelloCleanupPendingExact model = false \/
    recognitionFailureBeginCleanupPendingExact model = false \/
    recognitionFailureHelloCleanupFrameExact model = false \/
    recognitionFailureBeginCleanupFrameExact model = false \/
    recognitionFailureHelloFatalClassExact model = false \/
    recognitionFailureBeginFatalClassExact model = false ->
    ~ SystemsRecognitionFailureDetailVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hhc | [Hbc | [Hhp | [Hbp | [Hhf | [Hbf | [Hht | Hbt]]]]]]].
  - apply Hhc. exact (recognition_failure_success_hello_cleanup_count model H).
  - apply Hbc. exact (recognition_failure_success_begin_cleanup_count model H).
  - rewrite (recognition_failure_success_hello_cleanup_pending model H) in Hhp. discriminate.
  - rewrite (recognition_failure_success_begin_cleanup_pending model H) in Hbp. discriminate.
  - rewrite (recognition_failure_success_hello_cleanup_frame model H) in Hhf. discriminate.
  - rewrite (recognition_failure_success_begin_cleanup_frame model H) in Hbf. discriminate.
  - rewrite (recognition_failure_success_hello_fatal model H) in Hht. discriminate.
  - rewrite (recognition_failure_success_begin_fatal model H) in Hbt. discriminate.
Qed.

Theorem systems_recognition_failure_physical_claim_drift_is_rejected :
  forall model,
    recognitionFailurePhysicalReasonRepresentationClaimed model = true \/
    recognitionFailureRuntimeABIClaimed model = true \/
    recognitionFailureDiagnosticABIClaimed model = true \/
    recognitionFailureWireEncodingClaimed model = true \/
    recognitionFailureOuterFramingClaimed model = true ->
    ~ SystemsRecognitionFailureDetailVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hr | [Habi | [Hdiag | [Hwire | Hframe]]]].
  - rewrite (recognition_failure_success_no_reason_representation model H) in Hr. discriminate.
  - rewrite (recognition_failure_success_no_runtime_abi model H) in Habi. discriminate.
  - rewrite (recognition_failure_success_no_diagnostic_abi model H) in Hdiag. discriminate.
  - rewrite (recognition_failure_success_no_wire_encoding model H) in Hwire. discriminate.
  - rewrite (recognition_failure_success_no_outer_framing model H) in Hframe. discriminate.
Qed.
