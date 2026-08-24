From Phil.Systems Require Import HelloPolicyValidation.

(*
  PHIL-SYS-EXACT-SEND-001 — normalized proof model for the current Phase 0
  client exact-send semantic slice after client-outbound normalization.

  PR #94 made the payload's pre-send borrow/projection/digest uses explicit.
  This theorem therefore records the source fact we now actually need: those
  uses remain non-owning/no-copy, while the exact original client.payload owner
  is passed once to the retained ExactSendBoundary operation with no source
  recoverable-failure continuation.  Physical transport ABI is not selected at
  Systems level.
*)

Definition ExactSendDecisionId := nat.

Record SystemsExactSendModel : Type :=
  mkSystemsExactSendModel {
    systemsExactSendHelloPolicyPredecessor : SystemsHelloPolicyValidationModel;

    systemsExactSendClientOutboundSuccessorVerified : bool;
    systemsExactSendTransportExact : bool;
    systemsExactSendTransportRoleExact : bool;
    systemsExactSendPayloadExact : bool;
    systemsExactSendPayloadOwnedBuffer : bool;

    systemsExactSendPayloadBorrowCount : nat;
    systemsExactSendPayloadBorrowNonowning : bool;
    systemsExactSendPayloadCopyCount : nat;
    systemsExactSendPayloadOwnerIdentityPreserved : bool;

    systemsExactSendCallCount : nat;
    systemsExactSendCallTransportExact : bool;
    systemsExactSendCallPayloadExact : bool;
    systemsExactSendCallOutputCount : nat;
    systemsExactSendRuntimeSiteRetained : bool;
    systemsExactSendRuntimeSiteKindExact : bool;
    systemsExactSendRecoverableFailureEdgePresent : bool;

    systemsExactSendWitnessDecision : ExactSendDecisionId;
    systemsExactSendActualDecision : ExactSendDecisionId;
    systemsExactSendDecisionExact : bool;

    systemsExactSendPhysicalABIClaimed : bool;
    systemsExactSendPhysicalIOClaimed : bool;
    systemsExactSendOuterFramingClaimed : bool
  }.

Record SystemsExactSendVerificationSuccess
  (model : SystemsExactSendModel) : Prop :=
  mkSystemsExactSendVerificationSuccess {
    systems_exact_send_success_predecessor :
      SystemsHelloPolicyValidationVerificationSuccess
        (systemsExactSendHelloPolicyPredecessor model);

    systems_exact_send_success_client_outbound :
      systemsExactSendClientOutboundSuccessorVerified model = true;
    systems_exact_send_success_transport_exact :
      systemsExactSendTransportExact model = true;
    systems_exact_send_success_transport_role :
      systemsExactSendTransportRoleExact model = true;
    systems_exact_send_success_payload_exact :
      systemsExactSendPayloadExact model = true;
    systems_exact_send_success_payload_role :
      systemsExactSendPayloadOwnedBuffer model = true;

    systems_exact_send_success_borrow_count :
      systemsExactSendPayloadBorrowCount model = 1;
    systems_exact_send_success_borrow_nonowning :
      systemsExactSendPayloadBorrowNonowning model = true;
    systems_exact_send_success_copy_count :
      systemsExactSendPayloadCopyCount model = 0;
    systems_exact_send_success_owner_identity :
      systemsExactSendPayloadOwnerIdentityPreserved model = true;

    systems_exact_send_success_call_count :
      systemsExactSendCallCount model = 1;
    systems_exact_send_success_call_transport :
      systemsExactSendCallTransportExact model = true;
    systems_exact_send_success_call_payload :
      systemsExactSendCallPayloadExact model = true;
    systems_exact_send_success_call_outputs :
      systemsExactSendCallOutputCount model = 0;
    systems_exact_send_success_site_retained :
      systemsExactSendRuntimeSiteRetained model = true;
    systems_exact_send_success_site_kind :
      systemsExactSendRuntimeSiteKindExact model = true;
    systems_exact_send_success_no_failure_edge :
      systemsExactSendRecoverableFailureEdgePresent model = false;

    systems_exact_send_success_decision_identity :
      systemsExactSendActualDecision model = systemsExactSendWitnessDecision model;
    systems_exact_send_success_decision_exact :
      systemsExactSendDecisionExact model = true;

    systems_exact_send_success_no_physical_abi_claim :
      systemsExactSendPhysicalABIClaimed model = false;
    systems_exact_send_success_no_physical_io_claim :
      systemsExactSendPhysicalIOClaimed model = false;
    systems_exact_send_success_no_outer_framing_claim :
      systemsExactSendOuterFramingClaimed model = false
  }.

Theorem verified_systems_exact_send_reuses_hello_policy_authority :
  forall model,
    SystemsExactSendVerificationSuccess model ->
    SystemsHelloPolicyValidationVerificationSuccess
      (systemsExactSendHelloPolicyPredecessor model).
Proof.
  intros model H.
  exact (systems_exact_send_success_predecessor model H).
Qed.

Theorem verified_systems_exact_send_preserves_exact_transport_and_payload_owner :
  forall model,
    SystemsExactSendVerificationSuccess model ->
    systemsExactSendClientOutboundSuccessorVerified model = true /\
    systemsExactSendTransportExact model = true /\
    systemsExactSendTransportRoleExact model = true /\
    systemsExactSendPayloadExact model = true /\
    systemsExactSendPayloadOwnedBuffer model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_exact_send_success_client_outbound model H).
  - exact (systems_exact_send_success_transport_exact model H).
  - exact (systems_exact_send_success_transport_role model H).
  - exact (systems_exact_send_success_payload_exact model H).
  - exact (systems_exact_send_success_payload_role model H).
Qed.

Theorem verified_systems_exact_send_preserves_nonowning_borrow_and_no_copy :
  forall model,
    SystemsExactSendVerificationSuccess model ->
    systemsExactSendPayloadBorrowCount model = 1 /\
    systemsExactSendPayloadBorrowNonowning model = true /\
    systemsExactSendPayloadCopyCount model = 0 /\
    systemsExactSendPayloadOwnerIdentityPreserved model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_exact_send_success_borrow_count model H).
  - exact (systems_exact_send_success_borrow_nonowning model H).
  - exact (systems_exact_send_success_copy_count model H).
  - exact (systems_exact_send_success_owner_identity model H).
Qed.

Theorem verified_systems_exact_send_preserves_one_exact_site_without_failure_edge :
  forall model,
    SystemsExactSendVerificationSuccess model ->
    systemsExactSendCallCount model = 1 /\
    systemsExactSendCallTransportExact model = true /\
    systemsExactSendCallPayloadExact model = true /\
    systemsExactSendCallOutputCount model = 0 /\
    systemsExactSendRuntimeSiteRetained model = true /\
    systemsExactSendRuntimeSiteKindExact model = true /\
    systemsExactSendRecoverableFailureEdgePresent model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_exact_send_success_call_count model H).
  - exact (systems_exact_send_success_call_transport model H).
  - exact (systems_exact_send_success_call_payload model H).
  - exact (systems_exact_send_success_call_outputs model H).
  - exact (systems_exact_send_success_site_retained model H).
  - exact (systems_exact_send_success_site_kind model H).
  - exact (systems_exact_send_success_no_failure_edge model H).
Qed.

Theorem verified_systems_exact_send_binds_decision_and_claims_no_physical_transport :
  forall model,
    SystemsExactSendVerificationSuccess model ->
    systemsExactSendActualDecision model = systemsExactSendWitnessDecision model /\
    systemsExactSendDecisionExact model = true /\
    systemsExactSendPhysicalABIClaimed model = false /\
    systemsExactSendPhysicalIOClaimed model = false /\
    systemsExactSendOuterFramingClaimed model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_exact_send_success_decision_identity model H).
  - exact (systems_exact_send_success_decision_exact model H).
  - exact (systems_exact_send_success_no_physical_abi_claim model H).
  - exact (systems_exact_send_success_no_physical_io_claim model H).
  - exact (systems_exact_send_success_no_outer_framing_claim model H).
Qed.

Theorem systems_exact_send_owner_or_copy_drift_is_rejected :
  forall model,
    systemsExactSendPayloadOwnedBuffer model = false \/
    systemsExactSendPayloadBorrowCount model <> 1 \/
    systemsExactSendPayloadBorrowNonowning model = false \/
    systemsExactSendPayloadCopyCount model <> 0 \/
    systemsExactSendPayloadOwnerIdentityPreserved model = false ->
    ~ SystemsExactSendVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hrole | [Hborrow | [Hnonown | [Hcopy | Hidentity]]]].
  - rewrite (systems_exact_send_success_payload_role model H) in Hrole. discriminate.
  - apply Hborrow. exact (systems_exact_send_success_borrow_count model H).
  - rewrite (systems_exact_send_success_borrow_nonowning model H) in Hnonown. discriminate.
  - apply Hcopy. exact (systems_exact_send_success_copy_count model H).
  - rewrite (systems_exact_send_success_owner_identity model H) in Hidentity. discriminate.
Qed.

Theorem systems_exact_send_call_or_site_drift_is_rejected :
  forall model,
    systemsExactSendCallCount model <> 1 \/
    systemsExactSendCallTransportExact model = false \/
    systemsExactSendCallPayloadExact model = false \/
    systemsExactSendCallOutputCount model <> 0 \/
    systemsExactSendRuntimeSiteRetained model = false \/
    systemsExactSendRuntimeSiteKindExact model = false \/
    systemsExactSendRecoverableFailureEdgePresent model = true ->
    ~ SystemsExactSendVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hcount | [Htransport | [Hpayload | [Houtputs | [Hsite | [Hkind | Hfailure]]]]]].
  - apply Hcount. exact (systems_exact_send_success_call_count model H).
  - rewrite (systems_exact_send_success_call_transport model H) in Htransport. discriminate.
  - rewrite (systems_exact_send_success_call_payload model H) in Hpayload. discriminate.
  - apply Houtputs. exact (systems_exact_send_success_call_outputs model H).
  - rewrite (systems_exact_send_success_site_retained model H) in Hsite. discriminate.
  - rewrite (systems_exact_send_success_site_kind model H) in Hkind. discriminate.
  - rewrite (systems_exact_send_success_no_failure_edge model H) in Hfailure. discriminate.
Qed.
