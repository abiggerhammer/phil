From Phil.Systems Require Import BeginPolicySessionChoice.

(*
  PHIL-SYS-HELLO-POLICY-001 — normalized proof model for the final Systems
  HelloPolicy validation and rejected-reason flow.

  The theorem keeps the exact predecessor BeginPolicy authority, explicit
  policyContext and recognized Hello operands, the retained HelloPolicy runtime
  site, accepted/rejected(reason) control, branch-local rejection reason, and
  the exact single fatal validation effect that consumes that reason. Physical
  validator/reason ABI and runtime behavior are intentionally outside Systems.
*)

Definition HelloPolicyDecisionId := nat.

Record SystemsHelloPolicyValidationModel : Type :=
  mkSystemsHelloPolicyValidationModel {
    systemsHelloPolicyPredecessor : SystemsBeginPolicyChoiceModel;

    systemsHelloPolicyPolicyContextExact : bool;
    systemsHelloPolicyPolicyContextRuntimeInput : bool;
    systemsHelloPolicyPolicyContextHasProducer : bool;
    systemsHelloPolicyHelloRecordExact : bool;
    systemsHelloPolicyHelloRecordRuntimeRecord : bool;
    systemsHelloPolicyRuntimeSiteRetained : bool;

    systemsHelloPolicyValidatorInputCount : nat;
    systemsHelloPolicyValidatorInput0PolicyContext : bool;
    systemsHelloPolicyValidatorInput1HelloRecord : bool;
    systemsHelloPolicyAcceptedPayloadPresent : bool;
    systemsHelloPolicyAcceptedTargetExact : bool;
    systemsHelloPolicyRejectedPayloadPresent : bool;
    systemsHelloPolicyRejectedPayloadExact : bool;
    systemsHelloPolicyRejectedTargetExact : bool;

    systemsHelloPolicyFailureCallCount : nat;
    systemsHelloPolicyFailureTransportExact : bool;
    systemsHelloPolicyFailureReasonExact : bool;
    systemsHelloPolicyFailureTerminalExact : bool;
    systemsHelloPolicyReasonSemanticUseCount : nat;

    systemsHelloPolicyWitnessDecision : HelloPolicyDecisionId;
    systemsHelloPolicyActualDecision : HelloPolicyDecisionId;
    systemsHelloPolicyDecisionExact : bool;

    systemsHelloPolicyPhysicalReasonRepresentationClaimed : bool;
    systemsHelloPolicyRuntimeABIClaimed : bool;
    systemsHelloPolicyWireEncodingClaimed : bool;
    systemsHelloPolicyOuterFramingClaimed : bool
  }.

Record SystemsHelloPolicyValidationVerificationSuccess
  (model : SystemsHelloPolicyValidationModel) : Prop :=
  mkSystemsHelloPolicyValidationVerificationSuccess {
    systems_hello_policy_success_predecessor :
      SystemsBeginPolicyChoiceVerificationSuccess
        (systemsHelloPolicyPredecessor model);

    systems_hello_policy_success_policy_context_exact :
      systemsHelloPolicyPolicyContextExact model = true;
    systems_hello_policy_success_policy_context_role :
      systemsHelloPolicyPolicyContextRuntimeInput model = true;
    systems_hello_policy_success_policy_context_no_producer :
      systemsHelloPolicyPolicyContextHasProducer model = false;
    systems_hello_policy_success_hello_record_exact :
      systemsHelloPolicyHelloRecordExact model = true;
    systems_hello_policy_success_hello_record_role :
      systemsHelloPolicyHelloRecordRuntimeRecord model = true;
    systems_hello_policy_success_runtime_site_retained :
      systemsHelloPolicyRuntimeSiteRetained model = true;

    systems_hello_policy_success_validator_input_count :
      systemsHelloPolicyValidatorInputCount model = 2;
    systems_hello_policy_success_validator_input0 :
      systemsHelloPolicyValidatorInput0PolicyContext model = true;
    systems_hello_policy_success_validator_input1 :
      systemsHelloPolicyValidatorInput1HelloRecord model = true;
    systems_hello_policy_success_accepted_no_payload :
      systemsHelloPolicyAcceptedPayloadPresent model = false;
    systems_hello_policy_success_accepted_target :
      systemsHelloPolicyAcceptedTargetExact model = true;
    systems_hello_policy_success_rejected_payload :
      systemsHelloPolicyRejectedPayloadPresent model = true;
    systems_hello_policy_success_rejected_payload_exact :
      systemsHelloPolicyRejectedPayloadExact model = true;
    systems_hello_policy_success_rejected_target :
      systemsHelloPolicyRejectedTargetExact model = true;

    systems_hello_policy_success_failure_count :
      systemsHelloPolicyFailureCallCount model = 1;
    systems_hello_policy_success_failure_transport :
      systemsHelloPolicyFailureTransportExact model = true;
    systems_hello_policy_success_failure_reason :
      systemsHelloPolicyFailureReasonExact model = true;
    systems_hello_policy_success_failure_terminal :
      systemsHelloPolicyFailureTerminalExact model = true;
    systems_hello_policy_success_reason_use_count :
      systemsHelloPolicyReasonSemanticUseCount model = 1;

    systems_hello_policy_success_decision_identity :
      systemsHelloPolicyActualDecision model =
        systemsHelloPolicyWitnessDecision model;
    systems_hello_policy_success_decision_exact :
      systemsHelloPolicyDecisionExact model = true;

    systems_hello_policy_success_no_physical_reason_claim :
      systemsHelloPolicyPhysicalReasonRepresentationClaimed model = false;
    systems_hello_policy_success_no_runtime_abi_claim :
      systemsHelloPolicyRuntimeABIClaimed model = false;
    systems_hello_policy_success_no_wire_claim :
      systemsHelloPolicyWireEncodingClaimed model = false;
    systems_hello_policy_success_no_outer_framing_claim :
      systemsHelloPolicyOuterFramingClaimed model = false
  }.

Theorem verified_systems_hello_policy_reuses_begin_policy_authority :
  forall model,
    SystemsHelloPolicyValidationVerificationSuccess model ->
    SystemsBeginPolicyChoiceVerificationSuccess
      (systemsHelloPolicyPredecessor model).
Proof.
  intros model H.
  exact (systems_hello_policy_success_predecessor model H).
Qed.

Theorem verified_systems_hello_policy_preserves_exact_validator_subjects_and_site :
  forall model,
    SystemsHelloPolicyValidationVerificationSuccess model ->
    systemsHelloPolicyPolicyContextExact model = true /\
    systemsHelloPolicyPolicyContextRuntimeInput model = true /\
    systemsHelloPolicyPolicyContextHasProducer model = false /\
    systemsHelloPolicyHelloRecordExact model = true /\
    systemsHelloPolicyHelloRecordRuntimeRecord model = true /\
    systemsHelloPolicyRuntimeSiteRetained model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_hello_policy_success_policy_context_exact model H).
  - exact (systems_hello_policy_success_policy_context_role model H).
  - exact (systems_hello_policy_success_policy_context_no_producer model H).
  - exact (systems_hello_policy_success_hello_record_exact model H).
  - exact (systems_hello_policy_success_hello_record_role model H).
  - exact (systems_hello_policy_success_runtime_site_retained model H).
Qed.

Theorem verified_systems_hello_policy_preserves_accepted_rejected_reason_choice :
  forall model,
    SystemsHelloPolicyValidationVerificationSuccess model ->
    systemsHelloPolicyValidatorInputCount model = 2 /\
    systemsHelloPolicyValidatorInput0PolicyContext model = true /\
    systemsHelloPolicyValidatorInput1HelloRecord model = true /\
    systemsHelloPolicyAcceptedPayloadPresent model = false /\
    systemsHelloPolicyAcceptedTargetExact model = true /\
    systemsHelloPolicyRejectedPayloadPresent model = true /\
    systemsHelloPolicyRejectedPayloadExact model = true /\
    systemsHelloPolicyRejectedTargetExact model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_hello_policy_success_validator_input_count model H).
  - exact (systems_hello_policy_success_validator_input0 model H).
  - exact (systems_hello_policy_success_validator_input1 model H).
  - exact (systems_hello_policy_success_accepted_no_payload model H).
  - exact (systems_hello_policy_success_accepted_target model H).
  - exact (systems_hello_policy_success_rejected_payload model H).
  - exact (systems_hello_policy_success_rejected_payload_exact model H).
  - exact (systems_hello_policy_success_rejected_target model H).
Qed.

Theorem verified_systems_hello_policy_preserves_exact_fatal_reason_flow :
  forall model,
    SystemsHelloPolicyValidationVerificationSuccess model ->
    systemsHelloPolicyFailureCallCount model = 1 /\
    systemsHelloPolicyFailureTransportExact model = true /\
    systemsHelloPolicyFailureReasonExact model = true /\
    systemsHelloPolicyFailureTerminalExact model = true /\
    systemsHelloPolicyReasonSemanticUseCount model = 1.
Proof.
  intros model H; repeat split.
  - exact (systems_hello_policy_success_failure_count model H).
  - exact (systems_hello_policy_success_failure_transport model H).
  - exact (systems_hello_policy_success_failure_reason model H).
  - exact (systems_hello_policy_success_failure_terminal model H).
  - exact (systems_hello_policy_success_reason_use_count model H).
Qed.

Theorem verified_systems_hello_policy_binds_exact_lowering_decision :
  forall model,
    SystemsHelloPolicyValidationVerificationSuccess model ->
    systemsHelloPolicyActualDecision model =
      systemsHelloPolicyWitnessDecision model /\
    systemsHelloPolicyDecisionExact model = true.
Proof.
  intros model H; split.
  - exact (systems_hello_policy_success_decision_identity model H).
  - exact (systems_hello_policy_success_decision_exact model H).
Qed.

Theorem verified_systems_hello_policy_claims_no_physical_representation :
  forall model,
    SystemsHelloPolicyValidationVerificationSuccess model ->
    systemsHelloPolicyPhysicalReasonRepresentationClaimed model = false /\
    systemsHelloPolicyRuntimeABIClaimed model = false /\
    systemsHelloPolicyWireEncodingClaimed model = false /\
    systemsHelloPolicyOuterFramingClaimed model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_hello_policy_success_no_physical_reason_claim model H).
  - exact (systems_hello_policy_success_no_runtime_abi_claim model H).
  - exact (systems_hello_policy_success_no_wire_claim model H).
  - exact (systems_hello_policy_success_no_outer_framing_claim model H).
Qed.

Theorem systems_hello_policy_validator_or_reason_drift_is_rejected :
  forall model,
    systemsHelloPolicyPolicyContextHasProducer model = true \/
    systemsHelloPolicyValidatorInputCount model <> 2 \/
    systemsHelloPolicyValidatorInput0PolicyContext model = false \/
    systemsHelloPolicyValidatorInput1HelloRecord model = false \/
    systemsHelloPolicyRuntimeSiteRetained model = false \/
    systemsHelloPolicyRejectedPayloadPresent model = false \/
    systemsHelloPolicyRejectedPayloadExact model = false ->
    ~ SystemsHelloPolicyValidationVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hprod | [Hcount | [H0 | [H1 | [Hsite | [Hpresent | Hexact]]]]]].
  - rewrite (systems_hello_policy_success_policy_context_no_producer model H) in Hprod. discriminate.
  - apply Hcount. exact (systems_hello_policy_success_validator_input_count model H).
  - rewrite (systems_hello_policy_success_validator_input0 model H) in H0. discriminate.
  - rewrite (systems_hello_policy_success_validator_input1 model H) in H1. discriminate.
  - rewrite (systems_hello_policy_success_runtime_site_retained model H) in Hsite. discriminate.
  - rewrite (systems_hello_policy_success_rejected_payload model H) in Hpresent. discriminate.
  - rewrite (systems_hello_policy_success_rejected_payload_exact model H) in Hexact. discriminate.
Qed.

Theorem systems_hello_policy_failure_flow_drift_is_rejected :
  forall model,
    systemsHelloPolicyFailureCallCount model <> 1 \/
    systemsHelloPolicyFailureTransportExact model = false \/
    systemsHelloPolicyFailureReasonExact model = false \/
    systemsHelloPolicyFailureTerminalExact model = false \/
    systemsHelloPolicyReasonSemanticUseCount model <> 1 ->
    ~ SystemsHelloPolicyValidationVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hcount | [Htransport | [Hreason | [Hterminal | Huses]]]].
  - apply Hcount. exact (systems_hello_policy_success_failure_count model H).
  - rewrite (systems_hello_policy_success_failure_transport model H) in Htransport. discriminate.
  - rewrite (systems_hello_policy_success_failure_reason model H) in Hreason. discriminate.
  - rewrite (systems_hello_policy_success_failure_terminal model H) in Hterminal. discriminate.
  - apply Huses. exact (systems_hello_policy_success_reason_use_count model H).
Qed.
