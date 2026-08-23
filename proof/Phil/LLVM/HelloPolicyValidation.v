From Phil.Systems Require Import HelloPolicyValidation.
From Phil.LLVM Require Import BeginPolicyChoice.

(*
  PHIL-LLVM-HELLO-POLICY-001 — normalized proof model for the concrete
  phil-runtime/phase0/hello-policy-validation-v1 lowering introduced by #88.

  The target keeps the rejection reason as an opaque provider pointer and
  preserves pointer identity from validator output to the fatal-effect call.
  Provider semantics/lifetime, LLVM implementation correctness, linking, and
  native execution remain explicit external gates.
*)

Record LLVMHelloPolicyValidationModel : Type :=
  mkLLVMHelloPolicyValidationModel {
    llvmHelloPolicySystems : SystemsHelloPolicyValidationModel;
    llvmHelloPolicyBeginPredecessor : LLVMBeginPolicyChoiceModel;

    llvmHelloPolicyTargetExact : bool;
    llvmHelloPolicyDataLayoutExact : bool;
    llvmHelloPolicyABIProfileExact : bool;
    llvmHelloPolicyPolicyContextParameterExact : bool;

    llvmHelloPolicyValidatorCount : nat;
    llvmHelloPolicyValidatorPolicyContextExact : bool;
    llvmHelloPolicyValidatorHelloRecordExact : bool;
    llvmHelloPolicyValidatorReasonSlotExact : bool;
    llvmHelloPolicyValidatorTargetsExact : bool;

    llvmHelloPolicyReasonBindingCount : nat;
    llvmHelloPolicyReasonOpaquePointer : bool;
    llvmHelloPolicyFailureCallCount : nat;
    llvmHelloPolicyFailureTransportExact : bool;
    llvmHelloPolicyFailureReasonIdentityExact : bool;
    llvmHelloPolicyFailureTerminalReturnExact : bool;

    llvmHelloPolicyReasonWireEncodingPresent : bool;
    llvmHelloPolicyPeerProtocolEffectDefined : bool;
    llvmHelloPolicyGenericCallPresent : bool;
    llvmHelloPolicyUnloweredControlPresent : bool;
    llvmHelloPolicyAmbientPolicyStatePresent : bool;
    llvmHelloPolicyAmbientHelloStatePresent : bool;
    llvmHelloPolicyAmbientReasonStatePresent : bool;

    llvmHelloPolicyValidatorSemanticsProved : bool;
    llvmHelloPolicyReasonContentsProved : bool;
    llvmHelloPolicyReasonLifetimeProved : bool;
    llvmHelloPolicyFailureRuntimeSemanticsProved : bool;
    llvmHelloPolicyLLVMImplementationCorrectnessProved : bool;
    llvmHelloPolicyLinkingProved : bool;
    llvmHelloPolicyNativeExecutionProved : bool
  }.

Record LLVMHelloPolicyValidationVerificationSuccess
  (model : LLVMHelloPolicyValidationModel) : Prop :=
  mkLLVMHelloPolicyValidationVerificationSuccess {
    llvm_hello_policy_success_systems :
      SystemsHelloPolicyValidationVerificationSuccess
        (llvmHelloPolicySystems model);
    llvm_hello_policy_success_begin_predecessor :
      LLVMBeginPolicyChoiceVerificationSuccess
        (llvmHelloPolicyBeginPredecessor model);

    llvm_hello_policy_success_target :
      llvmHelloPolicyTargetExact model = true;
    llvm_hello_policy_success_layout :
      llvmHelloPolicyDataLayoutExact model = true;
    llvm_hello_policy_success_abi :
      llvmHelloPolicyABIProfileExact model = true;
    llvm_hello_policy_success_policy_parameter :
      llvmHelloPolicyPolicyContextParameterExact model = true;

    llvm_hello_policy_success_validator_count :
      llvmHelloPolicyValidatorCount model = 1;
    llvm_hello_policy_success_validator_policy :
      llvmHelloPolicyValidatorPolicyContextExact model = true;
    llvm_hello_policy_success_validator_hello :
      llvmHelloPolicyValidatorHelloRecordExact model = true;
    llvm_hello_policy_success_validator_reason_slot :
      llvmHelloPolicyValidatorReasonSlotExact model = true;
    llvm_hello_policy_success_validator_targets :
      llvmHelloPolicyValidatorTargetsExact model = true;

    llvm_hello_policy_success_reason_binding :
      llvmHelloPolicyReasonBindingCount model = 1;
    llvm_hello_policy_success_reason_pointer :
      llvmHelloPolicyReasonOpaquePointer model = true;
    llvm_hello_policy_success_failure_count :
      llvmHelloPolicyFailureCallCount model = 1;
    llvm_hello_policy_success_failure_transport :
      llvmHelloPolicyFailureTransportExact model = true;
    llvm_hello_policy_success_failure_reason_identity :
      llvmHelloPolicyFailureReasonIdentityExact model = true;
    llvm_hello_policy_success_terminal_return :
      llvmHelloPolicyFailureTerminalReturnExact model = true;

    llvm_hello_policy_success_no_reason_wire :
      llvmHelloPolicyReasonWireEncodingPresent model = false;
    llvm_hello_policy_success_no_peer_effect :
      llvmHelloPolicyPeerProtocolEffectDefined model = false;
    llvm_hello_policy_success_no_generic :
      llvmHelloPolicyGenericCallPresent model = false;
    llvm_hello_policy_success_no_unlowered :
      llvmHelloPolicyUnloweredControlPresent model = false;
    llvm_hello_policy_success_no_ambient_policy :
      llvmHelloPolicyAmbientPolicyStatePresent model = false;
    llvm_hello_policy_success_no_ambient_hello :
      llvmHelloPolicyAmbientHelloStatePresent model = false;
    llvm_hello_policy_success_no_ambient_reason :
      llvmHelloPolicyAmbientReasonStatePresent model = false;

    llvm_hello_policy_success_validator_semantics_external :
      llvmHelloPolicyValidatorSemanticsProved model = false;
    llvm_hello_policy_success_reason_contents_external :
      llvmHelloPolicyReasonContentsProved model = false;
    llvm_hello_policy_success_reason_lifetime_external :
      llvmHelloPolicyReasonLifetimeProved model = false;
    llvm_hello_policy_success_failure_semantics_external :
      llvmHelloPolicyFailureRuntimeSemanticsProved model = false;
    llvm_hello_policy_success_llvm_external :
      llvmHelloPolicyLLVMImplementationCorrectnessProved model = false;
    llvm_hello_policy_success_link_external :
      llvmHelloPolicyLinkingProved model = false;
    llvm_hello_policy_success_native_external :
      llvmHelloPolicyNativeExecutionProved model = false
  }.

Theorem verified_llvm_hello_policy_reuses_systems_and_begin_policy_authority :
  forall model,
    LLVMHelloPolicyValidationVerificationSuccess model ->
    SystemsHelloPolicyValidationVerificationSuccess
      (llvmHelloPolicySystems model) /\
    LLVMBeginPolicyChoiceVerificationSuccess
      (llvmHelloPolicyBeginPredecessor model).
Proof.
  intros model H; split.
  - exact (llvm_hello_policy_success_systems model H).
  - exact (llvm_hello_policy_success_begin_predecessor model H).
Qed.

Theorem verified_llvm_hello_policy_preserves_target_parameter_and_validator :
  forall model,
    LLVMHelloPolicyValidationVerificationSuccess model ->
    llvmHelloPolicyTargetExact model = true /\
    llvmHelloPolicyDataLayoutExact model = true /\
    llvmHelloPolicyABIProfileExact model = true /\
    llvmHelloPolicyPolicyContextParameterExact model = true /\
    llvmHelloPolicyValidatorCount model = 1 /\
    llvmHelloPolicyValidatorPolicyContextExact model = true /\
    llvmHelloPolicyValidatorHelloRecordExact model = true /\
    llvmHelloPolicyValidatorReasonSlotExact model = true /\
    llvmHelloPolicyValidatorTargetsExact model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_hello_policy_success_target model H).
  - exact (llvm_hello_policy_success_layout model H).
  - exact (llvm_hello_policy_success_abi model H).
  - exact (llvm_hello_policy_success_policy_parameter model H).
  - exact (llvm_hello_policy_success_validator_count model H).
  - exact (llvm_hello_policy_success_validator_policy model H).
  - exact (llvm_hello_policy_success_validator_hello model H).
  - exact (llvm_hello_policy_success_validator_reason_slot model H).
  - exact (llvm_hello_policy_success_validator_targets model H).
Qed.

Theorem verified_llvm_hello_policy_preserves_opaque_reason_identity_to_failure :
  forall model,
    LLVMHelloPolicyValidationVerificationSuccess model ->
    llvmHelloPolicyReasonBindingCount model = 1 /\
    llvmHelloPolicyReasonOpaquePointer model = true /\
    llvmHelloPolicyFailureCallCount model = 1 /\
    llvmHelloPolicyFailureTransportExact model = true /\
    llvmHelloPolicyFailureReasonIdentityExact model = true /\
    llvmHelloPolicyFailureTerminalReturnExact model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_hello_policy_success_reason_binding model H).
  - exact (llvm_hello_policy_success_reason_pointer model H).
  - exact (llvm_hello_policy_success_failure_count model H).
  - exact (llvm_hello_policy_success_failure_transport model H).
  - exact (llvm_hello_policy_success_failure_reason_identity model H).
  - exact (llvm_hello_policy_success_terminal_return model H).
Qed.

Theorem verified_llvm_hello_policy_eliminates_wire_generic_and_ambient_state :
  forall model,
    LLVMHelloPolicyValidationVerificationSuccess model ->
    llvmHelloPolicyReasonWireEncodingPresent model = false /\
    llvmHelloPolicyPeerProtocolEffectDefined model = false /\
    llvmHelloPolicyGenericCallPresent model = false /\
    llvmHelloPolicyUnloweredControlPresent model = false /\
    llvmHelloPolicyAmbientPolicyStatePresent model = false /\
    llvmHelloPolicyAmbientHelloStatePresent model = false /\
    llvmHelloPolicyAmbientReasonStatePresent model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_hello_policy_success_no_reason_wire model H).
  - exact (llvm_hello_policy_success_no_peer_effect model H).
  - exact (llvm_hello_policy_success_no_generic model H).
  - exact (llvm_hello_policy_success_no_unlowered model H).
  - exact (llvm_hello_policy_success_no_ambient_policy model H).
  - exact (llvm_hello_policy_success_no_ambient_hello model H).
  - exact (llvm_hello_policy_success_no_ambient_reason model H).
Qed.

Theorem verified_llvm_hello_policy_keeps_provider_and_execution_gates_external :
  forall model,
    LLVMHelloPolicyValidationVerificationSuccess model ->
    llvmHelloPolicyValidatorSemanticsProved model = false /\
    llvmHelloPolicyReasonContentsProved model = false /\
    llvmHelloPolicyReasonLifetimeProved model = false /\
    llvmHelloPolicyFailureRuntimeSemanticsProved model = false /\
    llvmHelloPolicyLLVMImplementationCorrectnessProved model = false /\
    llvmHelloPolicyLinkingProved model = false /\
    llvmHelloPolicyNativeExecutionProved model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_hello_policy_success_validator_semantics_external model H).
  - exact (llvm_hello_policy_success_reason_contents_external model H).
  - exact (llvm_hello_policy_success_reason_lifetime_external model H).
  - exact (llvm_hello_policy_success_failure_semantics_external model H).
  - exact (llvm_hello_policy_success_llvm_external model H).
  - exact (llvm_hello_policy_success_link_external model H).
  - exact (llvm_hello_policy_success_native_external model H).
Qed.

Theorem llvm_hello_policy_validator_or_reason_identity_drift_is_rejected :
  forall model,
    llvmHelloPolicyValidatorCount model <> 1 \/
    llvmHelloPolicyValidatorPolicyContextExact model = false \/
    llvmHelloPolicyValidatorHelloRecordExact model = false \/
    llvmHelloPolicyValidatorReasonSlotExact model = false \/
    llvmHelloPolicyValidatorTargetsExact model = false \/
    llvmHelloPolicyReasonBindingCount model <> 1 \/
    llvmHelloPolicyReasonOpaquePointer model = false \/
    llvmHelloPolicyFailureReasonIdentityExact model = false ->
    ~ LLVMHelloPolicyValidationVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hcount | [Hpolicy | [Hhello | [Hslot | [Htargets | [Hbind | [Hptr | Hidentity]]]]]]].
  - apply Hcount. exact (llvm_hello_policy_success_validator_count model H).
  - rewrite (llvm_hello_policy_success_validator_policy model H) in Hpolicy. discriminate.
  - rewrite (llvm_hello_policy_success_validator_hello model H) in Hhello. discriminate.
  - rewrite (llvm_hello_policy_success_validator_reason_slot model H) in Hslot. discriminate.
  - rewrite (llvm_hello_policy_success_validator_targets model H) in Htargets. discriminate.
  - apply Hbind. exact (llvm_hello_policy_success_reason_binding model H).
  - rewrite (llvm_hello_policy_success_reason_pointer model H) in Hptr. discriminate.
  - rewrite (llvm_hello_policy_success_failure_reason_identity model H) in Hidentity. discriminate.
Qed.

Theorem llvm_hello_policy_failure_or_ambient_drift_is_rejected :
  forall model,
    llvmHelloPolicyFailureCallCount model <> 1 \/
    llvmHelloPolicyFailureTransportExact model = false \/
    llvmHelloPolicyFailureTerminalReturnExact model = false \/
    llvmHelloPolicyReasonWireEncodingPresent model = true \/
    llvmHelloPolicyPeerProtocolEffectDefined model = true \/
    llvmHelloPolicyGenericCallPresent model = true \/
    llvmHelloPolicyUnloweredControlPresent model = true \/
    llvmHelloPolicyAmbientPolicyStatePresent model = true \/
    llvmHelloPolicyAmbientHelloStatePresent model = true \/
    llvmHelloPolicyAmbientReasonStatePresent model = true ->
    ~ LLVMHelloPolicyValidationVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hcount | [Htransport | [Hterminal | [Hwire | [Hpeer | [Hgeneric | [Hunlowered | [Hpolicy | [Hhello | Hreason]]]]]]]]].
  - apply Hcount. exact (llvm_hello_policy_success_failure_count model H).
  - rewrite (llvm_hello_policy_success_failure_transport model H) in Htransport. discriminate.
  - rewrite (llvm_hello_policy_success_terminal_return model H) in Hterminal. discriminate.
  - rewrite (llvm_hello_policy_success_no_reason_wire model H) in Hwire. discriminate.
  - rewrite (llvm_hello_policy_success_no_peer_effect model H) in Hpeer. discriminate.
  - rewrite (llvm_hello_policy_success_no_generic model H) in Hgeneric. discriminate.
  - rewrite (llvm_hello_policy_success_no_unlowered model H) in Hunlowered. discriminate.
  - rewrite (llvm_hello_policy_success_no_ambient_policy model H) in Hpolicy. discriminate.
  - rewrite (llvm_hello_policy_success_no_ambient_hello model H) in Hhello. discriminate.
  - rewrite (llvm_hello_policy_success_no_ambient_reason model H) in Hreason. discriminate.
Qed.
