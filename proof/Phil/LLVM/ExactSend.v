From Phil.Systems Require Import ExactSend.
From Phil.LLVM Require Import HelloPolicyValidation.

(*
  PHIL-LLVM-EXACT-SEND-001 — normalized proof model for the current
  transport-exact-send-v1 lowering after the client-outbound Systems successor.

  The exact-send target selects only the physical transport/payload operation.
  The newly explicit Hello/Begin construction and send semantics remain outside
  this theorem's physical competence and may remain generic target operations.
  The theorem proves the exact client.payload -> client.payload.owner relation,
  retained ExactSendBoundary, one exact runtime primitive, no introduced copy,
  and no invented recoverable failure edge.
*)

Record LLVMExactSendModel : Type :=
  mkLLVMExactSendModel {
    llvmExactSendSystems : SystemsExactSendModel;
    llvmExactSendHelloPolicyPredecessor : LLVMHelloPolicyValidationModel;

    llvmExactSendTargetExact : bool;
    llvmExactSendDataLayoutExact : bool;
    llvmExactSendABIProfileExact : bool;

    llvmExactSendClientTransportParameterExact : bool;
    llvmExactSendClientPayloadParameterCount : nat;
    llvmExactSendPayloadSourceTargetRelationExact : bool;
    llvmExactSendPayloadTargetOwnerNameExact : bool;

    llvmExactSendOperationCount : nat;
    llvmExactSendRuntimeSiteExact : bool;
    llvmExactSendRuntimeSiteKindExact : bool;
    llvmExactSendTransportOperandExact : bool;
    llvmExactSendPayloadOperandExact : bool;
    llvmExactSendRuntimeDeclarationExact : bool;

    llvmExactSendPayloadCopyCount : nat;
    llvmExactSendRecoverableFailureEdgeIntroduced : bool;
    llvmExactSendGenericExactSendCallPresent : bool;
    llvmExactSendAmbientTransportStatePresent : bool;
    llvmExactSendAmbientPayloadStatePresent : bool;

    llvmExactSendOutboundRecordPhysicalLoweringClaimed : bool;
    llvmExactSendOutboundGenericSemanticsPreserved : bool;

    llvmExactSendProviderWholeSendSemanticsProved : bool;
    llvmExactSendOpaqueBufferImplementationProved : bool;
    llvmExactSendPhysicalIOProved : bool;
    llvmExactSendLLVMImplementationCorrectnessProved : bool;
    llvmExactSendLinkingProved : bool;
    llvmExactSendNativeExecutionProved : bool;
    llvmExactSendOuterFramingDefined : bool
  }.

Record LLVMExactSendVerificationSuccess
  (model : LLVMExactSendModel) : Prop :=
  mkLLVMExactSendVerificationSuccess {
    llvm_exact_send_success_systems :
      SystemsExactSendVerificationSuccess (llvmExactSendSystems model);
    llvm_exact_send_success_hello_policy_predecessor :
      LLVMHelloPolicyValidationVerificationSuccess
        (llvmExactSendHelloPolicyPredecessor model);

    llvm_exact_send_success_target : llvmExactSendTargetExact model = true;
    llvm_exact_send_success_layout : llvmExactSendDataLayoutExact model = true;
    llvm_exact_send_success_abi : llvmExactSendABIProfileExact model = true;

    llvm_exact_send_success_transport_parameter :
      llvmExactSendClientTransportParameterExact model = true;
    llvm_exact_send_success_payload_parameter_count :
      llvmExactSendClientPayloadParameterCount model = 1;
    llvm_exact_send_success_payload_relation :
      llvmExactSendPayloadSourceTargetRelationExact model = true;
    llvm_exact_send_success_payload_owner_name :
      llvmExactSendPayloadTargetOwnerNameExact model = true;

    llvm_exact_send_success_operation_count :
      llvmExactSendOperationCount model = 1;
    llvm_exact_send_success_site : llvmExactSendRuntimeSiteExact model = true;
    llvm_exact_send_success_site_kind :
      llvmExactSendRuntimeSiteKindExact model = true;
    llvm_exact_send_success_transport_operand :
      llvmExactSendTransportOperandExact model = true;
    llvm_exact_send_success_payload_operand :
      llvmExactSendPayloadOperandExact model = true;
    llvm_exact_send_success_declaration :
      llvmExactSendRuntimeDeclarationExact model = true;

    llvm_exact_send_success_no_copy : llvmExactSendPayloadCopyCount model = 0;
    llvm_exact_send_success_no_failure_edge :
      llvmExactSendRecoverableFailureEdgeIntroduced model = false;
    llvm_exact_send_success_no_generic_exact_send :
      llvmExactSendGenericExactSendCallPresent model = false;
    llvm_exact_send_success_no_ambient_transport :
      llvmExactSendAmbientTransportStatePresent model = false;
    llvm_exact_send_success_no_ambient_payload :
      llvmExactSendAmbientPayloadStatePresent model = false;

    llvm_exact_send_success_no_outbound_physical_claim :
      llvmExactSendOutboundRecordPhysicalLoweringClaimed model = false;
    llvm_exact_send_success_outbound_generic_preserved :
      llvmExactSendOutboundGenericSemanticsPreserved model = true;

    llvm_exact_send_success_provider_semantics_external :
      llvmExactSendProviderWholeSendSemanticsProved model = false;
    llvm_exact_send_success_buffer_external :
      llvmExactSendOpaqueBufferImplementationProved model = false;
    llvm_exact_send_success_io_external : llvmExactSendPhysicalIOProved model = false;
    llvm_exact_send_success_llvm_external :
      llvmExactSendLLVMImplementationCorrectnessProved model = false;
    llvm_exact_send_success_link_external : llvmExactSendLinkingProved model = false;
    llvm_exact_send_success_native_external :
      llvmExactSendNativeExecutionProved model = false;
    llvm_exact_send_success_outer_framing_undefined :
      llvmExactSendOuterFramingDefined model = false
  }.

Theorem verified_llvm_exact_send_reuses_systems_and_hello_policy_authority :
  forall model,
    LLVMExactSendVerificationSuccess model ->
    SystemsExactSendVerificationSuccess (llvmExactSendSystems model) /\
    LLVMHelloPolicyValidationVerificationSuccess
      (llvmExactSendHelloPolicyPredecessor model).
Proof.
  intros model H; split.
  - exact (llvm_exact_send_success_systems model H).
  - exact (llvm_exact_send_success_hello_policy_predecessor model H).
Qed.

Theorem verified_llvm_exact_send_preserves_source_target_payload_identity :
  forall model,
    LLVMExactSendVerificationSuccess model ->
    llvmExactSendClientTransportParameterExact model = true /\
    llvmExactSendClientPayloadParameterCount model = 1 /\
    llvmExactSendPayloadSourceTargetRelationExact model = true /\
    llvmExactSendPayloadTargetOwnerNameExact model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_exact_send_success_transport_parameter model H).
  - exact (llvm_exact_send_success_payload_parameter_count model H).
  - exact (llvm_exact_send_success_payload_relation model H).
  - exact (llvm_exact_send_success_payload_owner_name model H).
Qed.

Theorem verified_llvm_exact_send_preserves_one_exact_runtime_operation :
  forall model,
    LLVMExactSendVerificationSuccess model ->
    llvmExactSendTargetExact model = true /\
    llvmExactSendDataLayoutExact model = true /\
    llvmExactSendABIProfileExact model = true /\
    llvmExactSendOperationCount model = 1 /\
    llvmExactSendRuntimeSiteExact model = true /\
    llvmExactSendRuntimeSiteKindExact model = true /\
    llvmExactSendTransportOperandExact model = true /\
    llvmExactSendPayloadOperandExact model = true /\
    llvmExactSendRuntimeDeclarationExact model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_exact_send_success_target model H).
  - exact (llvm_exact_send_success_layout model H).
  - exact (llvm_exact_send_success_abi model H).
  - exact (llvm_exact_send_success_operation_count model H).
  - exact (llvm_exact_send_success_site model H).
  - exact (llvm_exact_send_success_site_kind model H).
  - exact (llvm_exact_send_success_transport_operand model H).
  - exact (llvm_exact_send_success_payload_operand model H).
  - exact (llvm_exact_send_success_declaration model H).
Qed.

Theorem verified_llvm_exact_send_introduces_no_copy_failure_edge_or_ambient_state :
  forall model,
    LLVMExactSendVerificationSuccess model ->
    llvmExactSendPayloadCopyCount model = 0 /\
    llvmExactSendRecoverableFailureEdgeIntroduced model = false /\
    llvmExactSendGenericExactSendCallPresent model = false /\
    llvmExactSendAmbientTransportStatePresent model = false /\
    llvmExactSendAmbientPayloadStatePresent model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_exact_send_success_no_copy model H).
  - exact (llvm_exact_send_success_no_failure_edge model H).
  - exact (llvm_exact_send_success_no_generic_exact_send model H).
  - exact (llvm_exact_send_success_no_ambient_transport model H).
  - exact (llvm_exact_send_success_no_ambient_payload model H).
Qed.

Theorem verified_llvm_exact_send_scopes_out_client_outbound_physical_lowering :
  forall model,
    LLVMExactSendVerificationSuccess model ->
    llvmExactSendOutboundRecordPhysicalLoweringClaimed model = false /\
    llvmExactSendOutboundGenericSemanticsPreserved model = true.
Proof.
  intros model H; split.
  - exact (llvm_exact_send_success_no_outbound_physical_claim model H).
  - exact (llvm_exact_send_success_outbound_generic_preserved model H).
Qed.

Theorem verified_llvm_exact_send_keeps_runtime_and_execution_gates_external :
  forall model,
    LLVMExactSendVerificationSuccess model ->
    llvmExactSendProviderWholeSendSemanticsProved model = false /\
    llvmExactSendOpaqueBufferImplementationProved model = false /\
    llvmExactSendPhysicalIOProved model = false /\
    llvmExactSendLLVMImplementationCorrectnessProved model = false /\
    llvmExactSendLinkingProved model = false /\
    llvmExactSendNativeExecutionProved model = false /\
    llvmExactSendOuterFramingDefined model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_exact_send_success_provider_semantics_external model H).
  - exact (llvm_exact_send_success_buffer_external model H).
  - exact (llvm_exact_send_success_io_external model H).
  - exact (llvm_exact_send_success_llvm_external model H).
  - exact (llvm_exact_send_success_link_external model H).
  - exact (llvm_exact_send_success_native_external model H).
  - exact (llvm_exact_send_success_outer_framing_undefined model H).
Qed.

Theorem llvm_exact_send_mapping_or_operation_drift_is_rejected :
  forall model,
    llvmExactSendClientPayloadParameterCount model <> 1 \/
    llvmExactSendPayloadSourceTargetRelationExact model = false \/
    llvmExactSendPayloadTargetOwnerNameExact model = false \/
    llvmExactSendOperationCount model <> 1 \/
    llvmExactSendRuntimeSiteExact model = false \/
    llvmExactSendRuntimeSiteKindExact model = false \/
    llvmExactSendTransportOperandExact model = false \/
    llvmExactSendPayloadOperandExact model = false ->
    ~ LLVMExactSendVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hparam | [Hrelation | [Hname | [Hcount | [Hsite | [Hkind | [Htransport | Hpayload]]]]]]].
  - apply Hparam. exact (llvm_exact_send_success_payload_parameter_count model H).
  - rewrite (llvm_exact_send_success_payload_relation model H) in Hrelation. discriminate.
  - rewrite (llvm_exact_send_success_payload_owner_name model H) in Hname. discriminate.
  - apply Hcount. exact (llvm_exact_send_success_operation_count model H).
  - rewrite (llvm_exact_send_success_site model H) in Hsite. discriminate.
  - rewrite (llvm_exact_send_success_site_kind model H) in Hkind. discriminate.
  - rewrite (llvm_exact_send_success_transport_operand model H) in Htransport. discriminate.
  - rewrite (llvm_exact_send_success_payload_operand model H) in Hpayload. discriminate.
Qed.

Theorem llvm_exact_send_copy_failure_or_ambient_drift_is_rejected :
  forall model,
    llvmExactSendPayloadCopyCount model <> 0 \/
    llvmExactSendRecoverableFailureEdgeIntroduced model = true \/
    llvmExactSendGenericExactSendCallPresent model = true \/
    llvmExactSendAmbientTransportStatePresent model = true \/
    llvmExactSendAmbientPayloadStatePresent model = true ->
    ~ LLVMExactSendVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hcopy | [Hfailure | [Hgeneric | [Htransport | Hpayload]]]].
  - apply Hcopy. exact (llvm_exact_send_success_no_copy model H).
  - rewrite (llvm_exact_send_success_no_failure_edge model H) in Hfailure. discriminate.
  - rewrite (llvm_exact_send_success_no_generic_exact_send model H) in Hgeneric. discriminate.
  - rewrite (llvm_exact_send_success_no_ambient_transport model H) in Htransport. discriminate.
  - rewrite (llvm_exact_send_success_no_ambient_payload model H) in Hpayload. discriminate.
Qed.
