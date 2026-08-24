(*
  PHIL-LLVM-CLIENT-CONTROL-SEND-001 — normalized proof model for the
  client-control-send-v1 physical lowering introduced by #100.

  The theorem is deliberately scoped to the client-outbound-semantics-v1
  Systems source. Concrete Hello/Begin byte encoding, provider semantics,
  physical I/O, and the later server-side recognition/storage failure details
  remain outside this target's authority.
*)

Record LLVMClientControlSendModel : Type :=
  mkLLVMClientControlSendModel {
    ccsSourceClientOutboundAuthority : bool;
    ccsPredecessorExactSendAuthority : bool;
    ccsTranslationVerifies : bool;

    ccsSupportedVersionsCallCount : nat;
    ccsSupportedVersionsIdentityExact : bool;
    ccsHelloSendCount : nat;
    ccsHelloTransportExact : bool;
    ccsHelloVersionsExact : bool;
    ccsHelloRecordResidueCount : nat;

    ccsPayloadOwnerMappingExact : bool;
    ccsBorrowErasesToOwner : bool;
    ccsPayloadCopyCount : nat;
    ccsSha256CallCount : nat;
    ccsSha256PayloadExact : bool;
    ccsPayloadLengthCallCount : nat;
    ccsPayloadLengthOwnerExact : bool;
    ccsPayloadKindCallCount : nat;
    ccsPayloadKindOwnerExact : bool;

    ccsBeginSendCount : nat;
    ccsBeginTransportExact : bool;
    ccsBeginLengthExact : bool;
    ccsBeginKindExact : bool;
    ccsBeginDigestExact : bool;
    ccsBeginDigestAlgSha256 : bool;
    ccsBeginRecordResidueCount : nat;

    ccsRefinementWithSetCount : nat;
    ccsRefinementTransportExact : bool;
    ccsRefinementVersionsSameAsHello : bool;
    ccsRefinementSelectedExact : bool;
    ccsRefinementBranchesExact : bool;
    ccsAmbientOfferedVersionsCount : nat;

    ccsExactSendCount : nat;
    ccsExactSendTransportExact : bool;
    ccsExactSendPayloadOwnerExact : bool;

    ccsGenericOutboundCallCount : nat;
    ccsAmbientStateCount : nat;
    ccsPoisonCount : nat;
    ccsUnresolvedControlCount : nat;

    ccsClaimsConcreteHelloBeginBytes : bool;
    ccsClaimsProviderCodecSemantics : bool;
    ccsClaimsServerFailureDetailLowering : bool
  }.

Definition verified_llvm_client_control_send (m : LLVMClientControlSendModel) : Prop :=
  ccsSourceClientOutboundAuthority m = true /\
  ccsPredecessorExactSendAuthority m = true /\
  ccsTranslationVerifies m = true /\
  ccsSupportedVersionsCallCount m = 1 /\
  ccsSupportedVersionsIdentityExact m = true /\
  ccsHelloSendCount m = 1 /\
  ccsHelloTransportExact m = true /\
  ccsHelloVersionsExact m = true /\
  ccsHelloRecordResidueCount m = 0 /\
  ccsPayloadOwnerMappingExact m = true /\
  ccsBorrowErasesToOwner m = true /\
  ccsPayloadCopyCount m = 0 /\
  ccsSha256CallCount m = 1 /\
  ccsSha256PayloadExact m = true /\
  ccsPayloadLengthCallCount m = 1 /\
  ccsPayloadLengthOwnerExact m = true /\
  ccsPayloadKindCallCount m = 1 /\
  ccsPayloadKindOwnerExact m = true /\
  ccsBeginSendCount m = 1 /\
  ccsBeginTransportExact m = true /\
  ccsBeginLengthExact m = true /\
  ccsBeginKindExact m = true /\
  ccsBeginDigestExact m = true /\
  ccsBeginDigestAlgSha256 m = true /\
  ccsBeginRecordResidueCount m = 0 /\
  ccsRefinementWithSetCount m = 1 /\
  ccsRefinementTransportExact m = true /\
  ccsRefinementVersionsSameAsHello m = true /\
  ccsRefinementSelectedExact m = true /\
  ccsRefinementBranchesExact m = true /\
  ccsAmbientOfferedVersionsCount m = 0 /\
  ccsExactSendCount m = 1 /\
  ccsExactSendTransportExact m = true /\
  ccsExactSendPayloadOwnerExact m = true /\
  ccsGenericOutboundCallCount m = 0 /\
  ccsAmbientStateCount m = 0 /\
  ccsPoisonCount m = 0 /\
  ccsUnresolvedControlCount m = 0 /\
  ccsClaimsConcreteHelloBeginBytes m = false /\
  ccsClaimsProviderCodecSemantics m = false /\
  ccsClaimsServerFailureDetailLowering m = false.

Theorem verified_llvm_client_control_send_reuses_source_and_exact_send_authority :
  forall m, verified_llvm_client_control_send m ->
    ccsSourceClientOutboundAuthority m = true /\
    ccsPredecessorExactSendAuthority m = true.
Proof.
  intros m H.
  unfold verified_llvm_client_control_send in H.
  tauto.
Qed.

Theorem verified_llvm_client_control_send_preserves_one_hello_with_explicit_versions :
  forall m, verified_llvm_client_control_send m ->
    ccsSupportedVersionsCallCount m = 1 /\
    ccsHelloSendCount m = 1 /\
    ccsHelloVersionsExact m = true /\
    ccsRefinementVersionsSameAsHello m = true.
Proof.
  intros m H.
  unfold verified_llvm_client_control_send in H.
  tauto.
Qed.

Theorem verified_llvm_client_control_send_preserves_payload_derivations_without_copy :
  forall m, verified_llvm_client_control_send m ->
    ccsPayloadOwnerMappingExact m = true /\
    ccsBorrowErasesToOwner m = true /\
    ccsPayloadCopyCount m = 0 /\
    ccsSha256CallCount m = 1 /\
    ccsPayloadLengthCallCount m = 1 /\
    ccsPayloadKindCallCount m = 1.
Proof.
  intros m H.
  unfold verified_llvm_client_control_send in H.
  tauto.
Qed.

Theorem verified_llvm_client_control_send_preserves_exact_begin_operands :
  forall m, verified_llvm_client_control_send m ->
    ccsBeginSendCount m = 1 /\
    ccsBeginTransportExact m = true /\
    ccsBeginLengthExact m = true /\
    ccsBeginKindExact m = true /\
    ccsBeginDigestExact m = true /\
    ccsBeginDigestAlgSha256 m = true.
Proof.
  intros m H.
  unfold verified_llvm_client_control_send in H.
  tauto.
Qed.

Theorem verified_llvm_client_control_send_eliminates_ambient_version_state :
  forall m, verified_llvm_client_control_send m ->
    ccsRefinementWithSetCount m = 1 /\
    ccsRefinementVersionsSameAsHello m = true /\
    ccsAmbientOfferedVersionsCount m = 0 /\
    ccsAmbientStateCount m = 0.
Proof.
  intros m H.
  unfold verified_llvm_client_control_send in H.
  tauto.
Qed.

Theorem verified_llvm_client_control_send_preserves_exact_payload_send :
  forall m, verified_llvm_client_control_send m ->
    ccsExactSendCount m = 1 /\
    ccsExactSendTransportExact m = true /\
    ccsExactSendPayloadOwnerExact m = true.
Proof.
  intros m H.
  unfold verified_llvm_client_control_send in H.
  tauto.
Qed.

Theorem verified_llvm_client_control_send_claims_no_codec_or_server_failure_detail :
  forall m, verified_llvm_client_control_send m ->
    ccsClaimsConcreteHelloBeginBytes m = false /\
    ccsClaimsProviderCodecSemantics m = false /\
    ccsClaimsServerFailureDetailLowering m = false.
Proof.
  intros m H.
  unfold verified_llvm_client_control_send in H.
  tauto.
Qed.

Theorem llvm_client_control_send_versions_or_begin_drift_is_rejected :
  forall m,
    ccsRefinementVersionsSameAsHello m <> true \/
    ccsBeginDigestExact m <> true \/
    ccsBeginDigestAlgSha256 m <> true ->
    ~ verified_llvm_client_control_send m.
Proof. intros m Hbad Hgood; unfold verified_llvm_client_control_send in Hgood; tauto. Qed.

Theorem llvm_client_control_send_copy_ambient_or_exact_send_drift_is_rejected :
  forall m,
    ccsPayloadCopyCount m <> 0 \/
    ccsAmbientStateCount m <> 0 \/
    ccsExactSendCount m <> 1 ->
    ~ verified_llvm_client_control_send m.
Proof. intros m Hbad Hgood; unfold verified_llvm_client_control_send in Hgood; tauto. Qed.
