From Phil.Systems Require Import VersionChoiceOperands.

(*
  PHIL-SYS-BEGIN-POLICY-001 — normalized proof model for the final Systems
  BeginPolicy validation and peer-visible reject(reason)/proceed session choice.

  The model preserves the exact predecessor version-choice authority, explicit
  validator subjects, the retained runtime site, branch-local rejection reason,
  exact server selectors, exact client offer, endpoint separation, and removal
  of the historical Bool/generic-receive representation.  Physical reason
  representation and wire/runtime ABI are intentionally outside this Systems
  theorem and are proved separately at the LLVM target.
*)

Definition BeginPolicyDecisionId := nat.

Record SystemsBeginPolicyChoiceModel : Type :=
  mkSystemsBeginPolicyChoiceModel {
    systemsBeginPolicyPredecessor : SystemsVersionChoiceOperandsModel;

    systemsBeginPolicyPolicyContextExact : bool;
    systemsBeginPolicyPolicyContextRuntimeInput : bool;
    systemsBeginPolicyPolicyContextHasProducer : bool;
    systemsBeginPolicyBeginRecordExact : bool;
    systemsBeginPolicyBeginRecordRuntimeRecord : bool;
    systemsBeginPolicyRuntimeSiteRetained : bool;

    systemsBeginPolicyValidatorInputCount : nat;
    systemsBeginPolicyValidatorInput0PolicyContext : bool;
    systemsBeginPolicyValidatorInput1BeginRecord : bool;
    systemsBeginPolicyAcceptedPayloadPresent : bool;
    systemsBeginPolicyAcceptedTargetExact : bool;
    systemsBeginPolicyRejectedPayloadPresent : bool;
    systemsBeginPolicyRejectedPayloadExact : bool;
    systemsBeginPolicyRejectedTargetExact : bool;

    systemsBeginPolicyRejectSelectCount : nat;
    systemsBeginPolicyRejectTransportExact : bool;
    systemsBeginPolicyRejectPayloadExact : bool;
    systemsBeginPolicyProceedSelectCount : nat;
    systemsBeginPolicyProceedTransportExact : bool;
    systemsBeginPolicyProceedPayloadPresent : bool;

    systemsBeginPolicyClientOfferExact : bool;
    systemsBeginPolicyClientRejectPayloadPresent : bool;
    systemsBeginPolicyClientRejectPayloadExact : bool;
    systemsBeginPolicyClientRejectTargetExact : bool;
    systemsBeginPolicyClientProceedPayloadPresent : bool;
    systemsBeginPolicyClientProceedTargetExact : bool;
    systemsBeginPolicyEndpointReasonIdentitiesDistinct : bool;

    systemsBeginPolicyLegacyClientDiscriminatorPresent : bool;
    systemsBeginPolicyLegacyClientReceivePresent : bool;

    systemsBeginPolicyWitnessDecision : BeginPolicyDecisionId;
    systemsBeginPolicyActualDecision : BeginPolicyDecisionId;
    systemsBeginPolicyDecisionExact : bool;

    systemsBeginPolicyPhysicalReasonRepresentationClaimed : bool;
    systemsBeginPolicyWireEncodingClaimed : bool;
    systemsBeginPolicyRuntimeABIClaimed : bool;
    systemsBeginPolicyOuterFramingClaimed : bool
  }.

Record SystemsBeginPolicyChoiceVerificationSuccess
  (model : SystemsBeginPolicyChoiceModel) : Prop :=
  mkSystemsBeginPolicyChoiceVerificationSuccess {
    systems_begin_policy_success_predecessor :
      SystemsVersionChoiceOperandsVerificationSuccess
        (systemsBeginPolicyPredecessor model);

    systems_begin_policy_success_policy_context_exact :
      systemsBeginPolicyPolicyContextExact model = true;
    systems_begin_policy_success_policy_context_role :
      systemsBeginPolicyPolicyContextRuntimeInput model = true;
    systems_begin_policy_success_policy_context_no_producer :
      systemsBeginPolicyPolicyContextHasProducer model = false;
    systems_begin_policy_success_begin_record_exact :
      systemsBeginPolicyBeginRecordExact model = true;
    systems_begin_policy_success_begin_record_role :
      systemsBeginPolicyBeginRecordRuntimeRecord model = true;
    systems_begin_policy_success_runtime_site_retained :
      systemsBeginPolicyRuntimeSiteRetained model = true;

    systems_begin_policy_success_validator_input_count :
      systemsBeginPolicyValidatorInputCount model = 2;
    systems_begin_policy_success_validator_input0 :
      systemsBeginPolicyValidatorInput0PolicyContext model = true;
    systems_begin_policy_success_validator_input1 :
      systemsBeginPolicyValidatorInput1BeginRecord model = true;
    systems_begin_policy_success_accepted_no_payload :
      systemsBeginPolicyAcceptedPayloadPresent model = false;
    systems_begin_policy_success_accepted_target :
      systemsBeginPolicyAcceptedTargetExact model = true;
    systems_begin_policy_success_rejected_payload :
      systemsBeginPolicyRejectedPayloadPresent model = true;
    systems_begin_policy_success_rejected_payload_exact :
      systemsBeginPolicyRejectedPayloadExact model = true;
    systems_begin_policy_success_rejected_target :
      systemsBeginPolicyRejectedTargetExact model = true;

    systems_begin_policy_success_reject_select_count :
      systemsBeginPolicyRejectSelectCount model = 1;
    systems_begin_policy_success_reject_transport :
      systemsBeginPolicyRejectTransportExact model = true;
    systems_begin_policy_success_reject_payload :
      systemsBeginPolicyRejectPayloadExact model = true;
    systems_begin_policy_success_proceed_select_count :
      systemsBeginPolicyProceedSelectCount model = 1;
    systems_begin_policy_success_proceed_transport :
      systemsBeginPolicyProceedTransportExact model = true;
    systems_begin_policy_success_proceed_no_payload :
      systemsBeginPolicyProceedPayloadPresent model = false;

    systems_begin_policy_success_client_offer :
      systemsBeginPolicyClientOfferExact model = true;
    systems_begin_policy_success_client_reject_payload :
      systemsBeginPolicyClientRejectPayloadPresent model = true;
    systems_begin_policy_success_client_reject_payload_exact :
      systemsBeginPolicyClientRejectPayloadExact model = true;
    systems_begin_policy_success_client_reject_target :
      systemsBeginPolicyClientRejectTargetExact model = true;
    systems_begin_policy_success_client_proceed_no_payload :
      systemsBeginPolicyClientProceedPayloadPresent model = false;
    systems_begin_policy_success_client_proceed_target :
      systemsBeginPolicyClientProceedTargetExact model = true;
    systems_begin_policy_success_endpoint_reason_distinct :
      systemsBeginPolicyEndpointReasonIdentitiesDistinct model = true;

    systems_begin_policy_success_no_legacy_discriminator :
      systemsBeginPolicyLegacyClientDiscriminatorPresent model = false;
    systems_begin_policy_success_no_legacy_receive :
      systemsBeginPolicyLegacyClientReceivePresent model = false;

    systems_begin_policy_success_decision_identity :
      systemsBeginPolicyActualDecision model =
        systemsBeginPolicyWitnessDecision model;
    systems_begin_policy_success_decision_exact :
      systemsBeginPolicyDecisionExact model = true;

    systems_begin_policy_success_no_physical_reason_claim :
      systemsBeginPolicyPhysicalReasonRepresentationClaimed model = false;
    systems_begin_policy_success_no_wire_claim :
      systemsBeginPolicyWireEncodingClaimed model = false;
    systems_begin_policy_success_no_runtime_abi_claim :
      systemsBeginPolicyRuntimeABIClaimed model = false;
    systems_begin_policy_success_no_outer_framing_claim :
      systemsBeginPolicyOuterFramingClaimed model = false
  }.

Theorem verified_systems_begin_policy_reuses_version_operand_authority :
  forall model,
    SystemsBeginPolicyChoiceVerificationSuccess model ->
    SystemsVersionChoiceOperandsVerificationSuccess
      (systemsBeginPolicyPredecessor model).
Proof.
  intros model H.
  exact (systems_begin_policy_success_predecessor model H).
Qed.

Theorem verified_systems_begin_policy_preserves_exact_validator_subjects_and_site :
  forall model,
    SystemsBeginPolicyChoiceVerificationSuccess model ->
    systemsBeginPolicyPolicyContextExact model = true /\
    systemsBeginPolicyPolicyContextRuntimeInput model = true /\
    systemsBeginPolicyPolicyContextHasProducer model = false /\
    systemsBeginPolicyBeginRecordExact model = true /\
    systemsBeginPolicyBeginRecordRuntimeRecord model = true /\
    systemsBeginPolicyRuntimeSiteRetained model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_begin_policy_success_policy_context_exact model H).
  - exact (systems_begin_policy_success_policy_context_role model H).
  - exact (systems_begin_policy_success_policy_context_no_producer model H).
  - exact (systems_begin_policy_success_begin_record_exact model H).
  - exact (systems_begin_policy_success_begin_record_role model H).
  - exact (systems_begin_policy_success_runtime_site_retained model H).
Qed.

Theorem verified_systems_begin_policy_preserves_local_accepted_rejected_choice :
  forall model,
    SystemsBeginPolicyChoiceVerificationSuccess model ->
    systemsBeginPolicyValidatorInputCount model = 2 /\
    systemsBeginPolicyValidatorInput0PolicyContext model = true /\
    systemsBeginPolicyValidatorInput1BeginRecord model = true /\
    systemsBeginPolicyAcceptedPayloadPresent model = false /\
    systemsBeginPolicyAcceptedTargetExact model = true /\
    systemsBeginPolicyRejectedPayloadPresent model = true /\
    systemsBeginPolicyRejectedPayloadExact model = true /\
    systemsBeginPolicyRejectedTargetExact model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_begin_policy_success_validator_input_count model H).
  - exact (systems_begin_policy_success_validator_input0 model H).
  - exact (systems_begin_policy_success_validator_input1 model H).
  - exact (systems_begin_policy_success_accepted_no_payload model H).
  - exact (systems_begin_policy_success_accepted_target model H).
  - exact (systems_begin_policy_success_rejected_payload model H).
  - exact (systems_begin_policy_success_rejected_payload_exact model H).
  - exact (systems_begin_policy_success_rejected_target model H).
Qed.

Theorem verified_systems_begin_policy_preserves_exact_server_selects :
  forall model,
    SystemsBeginPolicyChoiceVerificationSuccess model ->
    systemsBeginPolicyRejectSelectCount model = 1 /\
    systemsBeginPolicyRejectTransportExact model = true /\
    systemsBeginPolicyRejectPayloadExact model = true /\
    systemsBeginPolicyProceedSelectCount model = 1 /\
    systemsBeginPolicyProceedTransportExact model = true /\
    systemsBeginPolicyProceedPayloadPresent model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_begin_policy_success_reject_select_count model H).
  - exact (systems_begin_policy_success_reject_transport model H).
  - exact (systems_begin_policy_success_reject_payload model H).
  - exact (systems_begin_policy_success_proceed_select_count model H).
  - exact (systems_begin_policy_success_proceed_transport model H).
  - exact (systems_begin_policy_success_proceed_no_payload model H).
Qed.

Theorem verified_systems_begin_policy_preserves_client_offer_and_endpoint_separation :
  forall model,
    SystemsBeginPolicyChoiceVerificationSuccess model ->
    systemsBeginPolicyClientOfferExact model = true /\
    systemsBeginPolicyClientRejectPayloadPresent model = true /\
    systemsBeginPolicyClientRejectPayloadExact model = true /\
    systemsBeginPolicyClientRejectTargetExact model = true /\
    systemsBeginPolicyClientProceedPayloadPresent model = false /\
    systemsBeginPolicyClientProceedTargetExact model = true /\
    systemsBeginPolicyEndpointReasonIdentitiesDistinct model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_begin_policy_success_client_offer model H).
  - exact (systems_begin_policy_success_client_reject_payload model H).
  - exact (systems_begin_policy_success_client_reject_payload_exact model H).
  - exact (systems_begin_policy_success_client_reject_target model H).
  - exact (systems_begin_policy_success_client_proceed_no_payload model H).
  - exact (systems_begin_policy_success_client_proceed_target model H).
  - exact (systems_begin_policy_success_endpoint_reason_distinct model H).
Qed.

Theorem verified_systems_begin_policy_eliminates_legacy_state_and_binds_decision :
  forall model,
    SystemsBeginPolicyChoiceVerificationSuccess model ->
    systemsBeginPolicyLegacyClientDiscriminatorPresent model = false /\
    systemsBeginPolicyLegacyClientReceivePresent model = false /\
    systemsBeginPolicyActualDecision model =
      systemsBeginPolicyWitnessDecision model /\
    systemsBeginPolicyDecisionExact model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_begin_policy_success_no_legacy_discriminator model H).
  - exact (systems_begin_policy_success_no_legacy_receive model H).
  - exact (systems_begin_policy_success_decision_identity model H).
  - exact (systems_begin_policy_success_decision_exact model H).
Qed.

Theorem verified_systems_begin_policy_claims_no_physical_representation :
  forall model,
    SystemsBeginPolicyChoiceVerificationSuccess model ->
    systemsBeginPolicyPhysicalReasonRepresentationClaimed model = false /\
    systemsBeginPolicyWireEncodingClaimed model = false /\
    systemsBeginPolicyRuntimeABIClaimed model = false /\
    systemsBeginPolicyOuterFramingClaimed model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_begin_policy_success_no_physical_reason_claim model H).
  - exact (systems_begin_policy_success_no_wire_claim model H).
  - exact (systems_begin_policy_success_no_runtime_abi_claim model H).
  - exact (systems_begin_policy_success_no_outer_framing_claim model H).
Qed.

Theorem systems_begin_policy_validator_or_reason_drift_is_rejected :
  forall model,
    systemsBeginPolicyPolicyContextHasProducer model = true \/
    systemsBeginPolicyValidatorInputCount model <> 2 \/
    systemsBeginPolicyValidatorInput0PolicyContext model = false \/
    systemsBeginPolicyValidatorInput1BeginRecord model = false \/
    systemsBeginPolicyRuntimeSiteRetained model = false \/
    systemsBeginPolicyRejectedPayloadPresent model = false \/
    systemsBeginPolicyRejectedPayloadExact model = false ->
    ~ SystemsBeginPolicyChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hprod | [Hcount | [H0 | [H1 | [Hsite | [Hpresent | Hexact]]]]]].
  - rewrite (systems_begin_policy_success_policy_context_no_producer model H) in Hprod. discriminate.
  - apply Hcount. exact (systems_begin_policy_success_validator_input_count model H).
  - rewrite (systems_begin_policy_success_validator_input0 model H) in H0. discriminate.
  - rewrite (systems_begin_policy_success_validator_input1 model H) in H1. discriminate.
  - rewrite (systems_begin_policy_success_runtime_site_retained model H) in Hsite. discriminate.
  - rewrite (systems_begin_policy_success_rejected_payload model H) in Hpresent. discriminate.
  - rewrite (systems_begin_policy_success_rejected_payload_exact model H) in Hexact. discriminate.
Qed.

Theorem systems_begin_policy_protocol_or_legacy_drift_is_rejected :
  forall model,
    systemsBeginPolicyRejectSelectCount model <> 1 \/
    systemsBeginPolicyRejectTransportExact model = false \/
    systemsBeginPolicyRejectPayloadExact model = false \/
    systemsBeginPolicyProceedSelectCount model <> 1 \/
    systemsBeginPolicyProceedTransportExact model = false \/
    systemsBeginPolicyProceedPayloadPresent model = true \/
    systemsBeginPolicyClientOfferExact model = false \/
    systemsBeginPolicyEndpointReasonIdentitiesDistinct model = false \/
    systemsBeginPolicyLegacyClientDiscriminatorPresent model = true \/
    systemsBeginPolicyLegacyClientReceivePresent model = true ->
    ~ SystemsBeginPolicyChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hrc | [Hrt | [Hrp | [Hpc | [Hpt | [Hpp | [Hoffer | [Hdistinct | [Hdisc | Hrecv]]]]]]]]].
  - apply Hrc. exact (systems_begin_policy_success_reject_select_count model H).
  - rewrite (systems_begin_policy_success_reject_transport model H) in Hrt. discriminate.
  - rewrite (systems_begin_policy_success_reject_payload model H) in Hrp. discriminate.
  - apply Hpc. exact (systems_begin_policy_success_proceed_select_count model H).
  - rewrite (systems_begin_policy_success_proceed_transport model H) in Hpt. discriminate.
  - rewrite (systems_begin_policy_success_proceed_no_payload model H) in Hpp. discriminate.
  - rewrite (systems_begin_policy_success_client_offer model H) in Hoffer. discriminate.
  - rewrite (systems_begin_policy_success_endpoint_reason_distinct model H) in Hdistinct. discriminate.
  - rewrite (systems_begin_policy_success_no_legacy_discriminator model H) in Hdisc. discriminate.
  - rewrite (systems_begin_policy_success_no_legacy_receive model H) in Hrecv. discriminate.
Qed.
