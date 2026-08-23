From Phil.Systems Require Import BeginPolicySessionChoice.
From Phil.LLVM Require Import VersionSessionChoiceLowering.

(*
  PHIL-LLVM-BEGIN-POLICY-001 — normalized proof model for the concrete
  phil-runtime/phase0/begin-policy-choice-v1 lowering introduced by PR #76.

  This theorem proves target shape and exact semantic-operand correspondence.
  Validator semantic correctness, the exact-program adequacy of the observable
  reason quotient, concrete byte I/O, malformed-input non-return, physical
  write success, LLVM implementation correctness, linking, and native execution
  remain explicit external gates.
*)

Record LLVMBeginPolicyChoiceModel : Type :=
  mkLLVMBeginPolicyChoiceModel {
    llvmBeginPolicySystems : SystemsBeginPolicyChoiceModel;
    llvmBeginPolicyVersionPredecessor : LLVMVersionSessionChoiceModel;

    llvmBeginPolicyTargetExact : bool;
    llvmBeginPolicyDataLayoutExact : bool;
    llvmBeginPolicyABIProfileExact : bool;
    llvmBeginPolicyPolicyContextParameterExact : bool;

    llvmBeginPolicyValidatorCount : nat;
    llvmBeginPolicyValidatorPolicyContextExact : bool;
    llvmBeginPolicyValidatorBeginRecordExact : bool;
    llvmBeginPolicyValidatorReasonSlotExact : bool;
    llvmBeginPolicyValidatorTargetsExact : bool;

    llvmBeginPolicyServerReasonBindingCount : nat;
    llvmBeginPolicyRejectSelectorCount : nat;
    llvmBeginPolicyRejectTransportExact : bool;
    llvmBeginPolicyRejectReasonExact : bool;
    llvmBeginPolicyProceedSelectorCount : nat;
    llvmBeginPolicyProceedTransportExact : bool;

    llvmBeginPolicyClientReceiverCount : nat;
    llvmBeginPolicyClientReceiverTransportExact : bool;
    llvmBeginPolicyClientReceiverReasonSlotExact : bool;
    llvmBeginPolicyClientReceiverTargetsExact : bool;
    llvmBeginPolicyClientReasonBindingCount : nat;

    llvmBeginPolicyServerReasonSemanticUseCount : nat;
    llvmBeginPolicyClientReasonSemanticUseCount : nat;

    llvmBeginPolicyWireProceed01 : bool;
    llvmBeginPolicyWireReject0001 : bool;
    llvmBeginPolicyReservedReasonNonreturnClaimed : bool;
    llvmBeginPolicyOuterFramingDefined : bool;

    llvmBeginPolicyUnloweredPoisonPresent : bool;
    llvmBeginPolicyGenericBeginPolicyCallPresent : bool;
    llvmBeginPolicyAmbientPolicyStatePresent : bool;
    llvmBeginPolicyAmbientChoiceStatePresent : bool;
    llvmBeginPolicyAmbientReasonStatePresent : bool;

    llvmBeginPolicyValidatorSemanticsProved : bool;
    llvmBeginPolicyReasonQuotientAdequacyProved : bool;
    llvmBeginPolicyConcreteIOProved : bool;
    llvmBeginPolicyMalformedTerminationProved : bool;
    llvmBeginPolicyWriteSuccessProved : bool;
    llvmBeginPolicyLLVMImplementationCorrectnessProved : bool;
    llvmBeginPolicyNativeExecutionProved : bool
  }.

Record LLVMBeginPolicyChoiceVerificationSuccess
  (model : LLVMBeginPolicyChoiceModel) : Prop :=
  mkLLVMBeginPolicyChoiceVerificationSuccess {
    llvm_begin_policy_success_systems :
      SystemsBeginPolicyChoiceVerificationSuccess
        (llvmBeginPolicySystems model);
    llvm_begin_policy_success_version_predecessor :
      LLVMVersionSessionChoiceVerificationSuccess
        (llvmBeginPolicyVersionPredecessor model);

    llvm_begin_policy_success_target : llvmBeginPolicyTargetExact model = true;
    llvm_begin_policy_success_layout : llvmBeginPolicyDataLayoutExact model = true;
    llvm_begin_policy_success_abi : llvmBeginPolicyABIProfileExact model = true;
    llvm_begin_policy_success_policy_parameter :
      llvmBeginPolicyPolicyContextParameterExact model = true;

    llvm_begin_policy_success_validator_count : llvmBeginPolicyValidatorCount model = 1;
    llvm_begin_policy_success_validator_policy :
      llvmBeginPolicyValidatorPolicyContextExact model = true;
    llvm_begin_policy_success_validator_begin :
      llvmBeginPolicyValidatorBeginRecordExact model = true;
    llvm_begin_policy_success_validator_reason_slot :
      llvmBeginPolicyValidatorReasonSlotExact model = true;
    llvm_begin_policy_success_validator_targets :
      llvmBeginPolicyValidatorTargetsExact model = true;

    llvm_begin_policy_success_server_reason_binding :
      llvmBeginPolicyServerReasonBindingCount model = 1;
    llvm_begin_policy_success_reject_selector_count :
      llvmBeginPolicyRejectSelectorCount model = 1;
    llvm_begin_policy_success_reject_transport :
      llvmBeginPolicyRejectTransportExact model = true;
    llvm_begin_policy_success_reject_reason :
      llvmBeginPolicyRejectReasonExact model = true;
    llvm_begin_policy_success_proceed_selector_count :
      llvmBeginPolicyProceedSelectorCount model = 1;
    llvm_begin_policy_success_proceed_transport :
      llvmBeginPolicyProceedTransportExact model = true;

    llvm_begin_policy_success_client_receiver_count :
      llvmBeginPolicyClientReceiverCount model = 1;
    llvm_begin_policy_success_client_receiver_transport :
      llvmBeginPolicyClientReceiverTransportExact model = true;
    llvm_begin_policy_success_client_receiver_reason :
      llvmBeginPolicyClientReceiverReasonSlotExact model = true;
    llvm_begin_policy_success_client_receiver_targets :
      llvmBeginPolicyClientReceiverTargetsExact model = true;
    llvm_begin_policy_success_client_reason_binding :
      llvmBeginPolicyClientReasonBindingCount model = 1;

    llvm_begin_policy_success_server_reason_use_count :
      llvmBeginPolicyServerReasonSemanticUseCount model = 1;
    llvm_begin_policy_success_client_reason_use_count :
      llvmBeginPolicyClientReasonSemanticUseCount model = 0;

    llvm_begin_policy_success_wire_proceed : llvmBeginPolicyWireProceed01 model = true;
    llvm_begin_policy_success_wire_reject : llvmBeginPolicyWireReject0001 model = true;
    llvm_begin_policy_success_reserved_reason_external :
      llvmBeginPolicyReservedReasonNonreturnClaimed model = false;
    llvm_begin_policy_success_outer_framing_undefined :
      llvmBeginPolicyOuterFramingDefined model = false;

    llvm_begin_policy_success_no_poison :
      llvmBeginPolicyUnloweredPoisonPresent model = false;
    llvm_begin_policy_success_no_generic_call :
      llvmBeginPolicyGenericBeginPolicyCallPresent model = false;
    llvm_begin_policy_success_no_ambient_policy :
      llvmBeginPolicyAmbientPolicyStatePresent model = false;
    llvm_begin_policy_success_no_ambient_choice :
      llvmBeginPolicyAmbientChoiceStatePresent model = false;
    llvm_begin_policy_success_no_ambient_reason :
      llvmBeginPolicyAmbientReasonStatePresent model = false;

    llvm_begin_policy_success_validator_semantics_external :
      llvmBeginPolicyValidatorSemanticsProved model = false;
    llvm_begin_policy_success_reason_quotient_external :
      llvmBeginPolicyReasonQuotientAdequacyProved model = false;
    llvm_begin_policy_success_io_external :
      llvmBeginPolicyConcreteIOProved model = false;
    llvm_begin_policy_success_malformed_external :
      llvmBeginPolicyMalformedTerminationProved model = false;
    llvm_begin_policy_success_write_external :
      llvmBeginPolicyWriteSuccessProved model = false;
    llvm_begin_policy_success_llvm_external :
      llvmBeginPolicyLLVMImplementationCorrectnessProved model = false;
    llvm_begin_policy_success_native_external :
      llvmBeginPolicyNativeExecutionProved model = false
  }.

Theorem verified_llvm_begin_policy_reuses_systems_and_version_authority :
  forall model,
    LLVMBeginPolicyChoiceVerificationSuccess model ->
    SystemsBeginPolicyChoiceVerificationSuccess (llvmBeginPolicySystems model) /\
    LLVMVersionSessionChoiceVerificationSuccess
      (llvmBeginPolicyVersionPredecessor model).
Proof.
  intros model H; split.
  - exact (llvm_begin_policy_success_systems model H).
  - exact (llvm_begin_policy_success_version_predecessor model H).
Qed.

Theorem verified_llvm_begin_policy_preserves_target_parameter_and_validator :
  forall model,
    LLVMBeginPolicyChoiceVerificationSuccess model ->
    llvmBeginPolicyTargetExact model = true /\
    llvmBeginPolicyDataLayoutExact model = true /\
    llvmBeginPolicyABIProfileExact model = true /\
    llvmBeginPolicyPolicyContextParameterExact model = true /\
    llvmBeginPolicyValidatorCount model = 1 /\
    llvmBeginPolicyValidatorPolicyContextExact model = true /\
    llvmBeginPolicyValidatorBeginRecordExact model = true /\
    llvmBeginPolicyValidatorReasonSlotExact model = true /\
    llvmBeginPolicyValidatorTargetsExact model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_begin_policy_success_target model H).
  - exact (llvm_begin_policy_success_layout model H).
  - exact (llvm_begin_policy_success_abi model H).
  - exact (llvm_begin_policy_success_policy_parameter model H).
  - exact (llvm_begin_policy_success_validator_count model H).
  - exact (llvm_begin_policy_success_validator_policy model H).
  - exact (llvm_begin_policy_success_validator_begin model H).
  - exact (llvm_begin_policy_success_validator_reason_slot model H).
  - exact (llvm_begin_policy_success_validator_targets model H).
Qed.

Theorem verified_llvm_begin_policy_preserves_server_selectors :
  forall model,
    LLVMBeginPolicyChoiceVerificationSuccess model ->
    llvmBeginPolicyServerReasonBindingCount model = 1 /\
    llvmBeginPolicyRejectSelectorCount model = 1 /\
    llvmBeginPolicyRejectTransportExact model = true /\
    llvmBeginPolicyRejectReasonExact model = true /\
    llvmBeginPolicyProceedSelectorCount model = 1 /\
    llvmBeginPolicyProceedTransportExact model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_begin_policy_success_server_reason_binding model H).
  - exact (llvm_begin_policy_success_reject_selector_count model H).
  - exact (llvm_begin_policy_success_reject_transport model H).
  - exact (llvm_begin_policy_success_reject_reason model H).
  - exact (llvm_begin_policy_success_proceed_selector_count model H).
  - exact (llvm_begin_policy_success_proceed_transport model H).
Qed.

Theorem verified_llvm_begin_policy_preserves_client_receiver_and_reason_binding :
  forall model,
    LLVMBeginPolicyChoiceVerificationSuccess model ->
    llvmBeginPolicyClientReceiverCount model = 1 /\
    llvmBeginPolicyClientReceiverTransportExact model = true /\
    llvmBeginPolicyClientReceiverReasonSlotExact model = true /\
    llvmBeginPolicyClientReceiverTargetsExact model = true /\
    llvmBeginPolicyClientReasonBindingCount model = 1.
Proof.
  intros model H; repeat split.
  - exact (llvm_begin_policy_success_client_receiver_count model H).
  - exact (llvm_begin_policy_success_client_receiver_transport model H).
  - exact (llvm_begin_policy_success_client_receiver_reason model H).
  - exact (llvm_begin_policy_success_client_receiver_targets model H).
  - exact (llvm_begin_policy_success_client_reason_binding model H).
Qed.

Theorem verified_llvm_begin_policy_binds_exact_program_reason_use_quotient :
  forall model,
    LLVMBeginPolicyChoiceVerificationSuccess model ->
    llvmBeginPolicyServerReasonSemanticUseCount model = 1 /\
    llvmBeginPolicyClientReasonSemanticUseCount model = 0 /\
    llvmBeginPolicyWireProceed01 model = true /\
    llvmBeginPolicyWireReject0001 model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_begin_policy_success_server_reason_use_count model H).
  - exact (llvm_begin_policy_success_client_reason_use_count model H).
  - exact (llvm_begin_policy_success_wire_proceed model H).
  - exact (llvm_begin_policy_success_wire_reject model H).
Qed.

Theorem verified_llvm_begin_policy_eliminates_unlowered_and_ambient_state :
  forall model,
    LLVMBeginPolicyChoiceVerificationSuccess model ->
    llvmBeginPolicyUnloweredPoisonPresent model = false /\
    llvmBeginPolicyGenericBeginPolicyCallPresent model = false /\
    llvmBeginPolicyAmbientPolicyStatePresent model = false /\
    llvmBeginPolicyAmbientChoiceStatePresent model = false /\
    llvmBeginPolicyAmbientReasonStatePresent model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_begin_policy_success_no_poison model H).
  - exact (llvm_begin_policy_success_no_generic_call model H).
  - exact (llvm_begin_policy_success_no_ambient_policy model H).
  - exact (llvm_begin_policy_success_no_ambient_choice model H).
  - exact (llvm_begin_policy_success_no_ambient_reason model H).
Qed.

Theorem verified_llvm_begin_policy_keeps_external_runtime_gates_explicit :
  forall model,
    LLVMBeginPolicyChoiceVerificationSuccess model ->
    llvmBeginPolicyValidatorSemanticsProved model = false /\
    llvmBeginPolicyReasonQuotientAdequacyProved model = false /\
    llvmBeginPolicyConcreteIOProved model = false /\
    llvmBeginPolicyMalformedTerminationProved model = false /\
    llvmBeginPolicyWriteSuccessProved model = false /\
    llvmBeginPolicyLLVMImplementationCorrectnessProved model = false /\
    llvmBeginPolicyNativeExecutionProved model = false /\
    llvmBeginPolicyReservedReasonNonreturnClaimed model = false /\
    llvmBeginPolicyOuterFramingDefined model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_begin_policy_success_validator_semantics_external model H).
  - exact (llvm_begin_policy_success_reason_quotient_external model H).
  - exact (llvm_begin_policy_success_io_external model H).
  - exact (llvm_begin_policy_success_malformed_external model H).
  - exact (llvm_begin_policy_success_write_external model H).
  - exact (llvm_begin_policy_success_llvm_external model H).
  - exact (llvm_begin_policy_success_native_external model H).
  - exact (llvm_begin_policy_success_reserved_reason_external model H).
  - exact (llvm_begin_policy_success_outer_framing_undefined model H).
Qed.

Theorem llvm_begin_policy_validator_or_selector_drift_is_rejected :
  forall model,
    llvmBeginPolicyValidatorCount model <> 1 \/
    llvmBeginPolicyValidatorPolicyContextExact model = false \/
    llvmBeginPolicyValidatorBeginRecordExact model = false \/
    llvmBeginPolicyValidatorReasonSlotExact model = false \/
    llvmBeginPolicyValidatorTargetsExact model = false \/
    llvmBeginPolicyRejectSelectorCount model <> 1 \/
    llvmBeginPolicyRejectTransportExact model = false \/
    llvmBeginPolicyRejectReasonExact model = false \/
    llvmBeginPolicyProceedSelectorCount model <> 1 \/
    llvmBeginPolicyProceedTransportExact model = false ->
    ~ LLVMBeginPolicyChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hvc | [Hvp | [Hvb | [Hvr | [Hvt | [Hrc | [Hrt | [Hrr | [Hpc | Hpt]]]]]]]]].
  - apply Hvc. exact (llvm_begin_policy_success_validator_count model H).
  - rewrite (llvm_begin_policy_success_validator_policy model H) in Hvp. discriminate.
  - rewrite (llvm_begin_policy_success_validator_begin model H) in Hvb. discriminate.
  - rewrite (llvm_begin_policy_success_validator_reason_slot model H) in Hvr. discriminate.
  - rewrite (llvm_begin_policy_success_validator_targets model H) in Hvt. discriminate.
  - apply Hrc. exact (llvm_begin_policy_success_reject_selector_count model H).
  - rewrite (llvm_begin_policy_success_reject_transport model H) in Hrt. discriminate.
  - rewrite (llvm_begin_policy_success_reject_reason model H) in Hrr. discriminate.
  - apply Hpc. exact (llvm_begin_policy_success_proceed_selector_count model H).
  - rewrite (llvm_begin_policy_success_proceed_transport model H) in Hpt. discriminate.
Qed.

Theorem llvm_begin_policy_receiver_reason_or_ambient_drift_is_rejected :
  forall model,
    llvmBeginPolicyClientReceiverCount model <> 1 \/
    llvmBeginPolicyClientReceiverTransportExact model = false \/
    llvmBeginPolicyClientReceiverReasonSlotExact model = false \/
    llvmBeginPolicyClientReceiverTargetsExact model = false \/
    llvmBeginPolicyClientReasonBindingCount model <> 1 \/
    llvmBeginPolicyServerReasonSemanticUseCount model <> 1 \/
    llvmBeginPolicyClientReasonSemanticUseCount model <> 0 \/
    llvmBeginPolicyUnloweredPoisonPresent model = true \/
    llvmBeginPolicyGenericBeginPolicyCallPresent model = true \/
    llvmBeginPolicyAmbientPolicyStatePresent model = true \/
    llvmBeginPolicyAmbientChoiceStatePresent model = true \/
    llvmBeginPolicyAmbientReasonStatePresent model = true ->
    ~ LLVMBeginPolicyChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hcc | [Hct | [Hcr | [Hcg | [Hbc | [Hsu | [Hcu | [Hp | [Hg | [Hap | [Hac | Har]]]]]]]]]]].
  - apply Hcc. exact (llvm_begin_policy_success_client_receiver_count model H).
  - rewrite (llvm_begin_policy_success_client_receiver_transport model H) in Hct. discriminate.
  - rewrite (llvm_begin_policy_success_client_receiver_reason model H) in Hcr. discriminate.
  - rewrite (llvm_begin_policy_success_client_receiver_targets model H) in Hcg. discriminate.
  - apply Hbc. exact (llvm_begin_policy_success_client_reason_binding model H).
  - apply Hsu. exact (llvm_begin_policy_success_server_reason_use_count model H).
  - apply Hcu. exact (llvm_begin_policy_success_client_reason_use_count model H).
  - rewrite (llvm_begin_policy_success_no_poison model H) in Hp. discriminate.
  - rewrite (llvm_begin_policy_success_no_generic_call model H) in Hg. discriminate.
  - rewrite (llvm_begin_policy_success_no_ambient_policy model H) in Hap. discriminate.
  - rewrite (llvm_begin_policy_success_no_ambient_choice model H) in Hac. discriminate.
  - rewrite (llvm_begin_policy_success_no_ambient_reason model H) in Har. discriminate.
Qed.
