From Phil.LLVM Require Import RecognizedRecordABI RuntimeSymbolIdentity.

(*
  PHIL-LLVM-EXACT-RECV-001 — normalized proof model for the concrete
  transport-exact-receive-v1 lowering.

  This theorem family is deliberately target-bound. It assumes the already
  verified recognized-record ABI and runtime-symbol discipline, then adds the
  new authority introduced by PR #48: explicit transport identity, exact U64
  length identity, exact payload-owner identity, exact status == 1 success,
  owner-preserving failure/ordinary cleanup, and absence of ambient transport
  or payload recovery. It does not prove LLVM, the runtime implementation, or
  production transport semantics.
*)

Definition ExactTransportSSAId := nat.
Definition ExactPayloadSSAId := nat.
Definition ExactBlockId := nat.

Record ExactReceiveModel : Type := mkExactReceiveModel {
  exactRecognizedRecordABI : RecognizedRecordABIModel;
  exactRuntimeSymbols : RuntimeSymbolModel;
  exactExpectedTransport : ExactTransportSSAId;
  exactActualTransport : ExactTransportSSAId;
  exactExpectedLength : ABIScalarSSAId;
  exactActualLength : ABIScalarSSAId;
  exactExpectedPayload : ExactPayloadSSAId;
  exactActualPayload : ExactPayloadSSAId;
  exactPayloadExtractedFromReceiveResult : bool;
  exactStatusConstant : nat;
  exactExpectedSuccessBlock : ExactBlockId;
  exactActualSuccessBlock : ExactBlockId;
  exactExpectedFailureBlock : ExactBlockId;
  exactActualFailureBlock : ExactBlockId;
  exactFailureReleasedPayload : ExactPayloadSSAId;
  exactOrdinaryReleasedPayload : ExactPayloadSSAId;
  exactAmbientTransportPresent : bool;
  exactAmbientPayloadPresent : bool;
  exactObsoleteLengthOnlySignaturePresent : bool;
  exactPayloadLayoutAccessPresent : bool;
  exactUnauthorizedPayloadPointerStrengtheningPresent : bool
}.

Record ExactReceiveVerificationSuccess (model : ExactReceiveModel) : Prop :=
  mkExactReceiveVerificationSuccess {
    exact_success_recognized_record_abi :
      RecognizedRecordABIVerificationSuccess (exactRecognizedRecordABI model);
    exact_success_runtime_symbols :
      RuntimeSymbolVerificationSuccess (exactRuntimeSymbols model);
    exact_success_transport_identity :
      exactActualTransport model = exactExpectedTransport model;
    exact_success_expected_length_is_projection :
      exactExpectedLength model =
        abiProjectedScalar (exactRecognizedRecordABI model);
    exact_success_length_identity :
      exactActualLength model = exactExpectedLength model;
    exact_success_payload_identity :
      exactActualPayload model = exactExpectedPayload model;
    exact_success_payload_from_result :
      exactPayloadExtractedFromReceiveResult model = true;
    exact_success_fail_closed_status :
      exactStatusConstant model = 1;
    exact_success_success_edge :
      exactActualSuccessBlock model = exactExpectedSuccessBlock model;
    exact_success_failure_edge :
      exactActualFailureBlock model = exactExpectedFailureBlock model;
    exact_success_failure_release_identity :
      exactFailureReleasedPayload model = exactActualPayload model;
    exact_success_ordinary_release_identity :
      exactOrdinaryReleasedPayload model = exactActualPayload model;
    exact_success_no_ambient_transport :
      exactAmbientTransportPresent model = false;
    exact_success_no_ambient_payload :
      exactAmbientPayloadPresent model = false;
    exact_success_no_obsolete_signature :
      exactObsoleteLengthOnlySignaturePresent model = false;
    exact_success_no_payload_layout_access :
      exactPayloadLayoutAccessPresent model = false;
    exact_success_no_unauthorized_payload_strengthening :
      exactUnauthorizedPayloadPointerStrengtheningPresent model = false
  }.

Theorem verified_exact_receive_reuses_recognized_record_authority :
  forall model,
    ExactReceiveVerificationSuccess model ->
    RecognizedRecordABIVerificationSuccess (exactRecognizedRecordABI model).
Proof.
  intros model H.
  exact (exact_success_recognized_record_abi model H).
Qed.

Theorem verified_exact_receive_reuses_runtime_symbol_authority :
  forall model,
    ExactReceiveVerificationSuccess model ->
    RuntimeSymbolVerificationSuccess (exactRuntimeSymbols model).
Proof.
  intros model H.
  exact (exact_success_runtime_symbols model H).
Qed.

Theorem verified_exact_receive_preserves_explicit_transport :
  forall model,
    ExactReceiveVerificationSuccess model ->
    exactActualTransport model = exactExpectedTransport model.
Proof.
  intros model H.
  exact (exact_success_transport_identity model H).
Qed.

Theorem verified_exact_receive_preserves_begin_length_u64 :
  forall model,
    ExactReceiveVerificationSuccess model ->
    exactActualLength model =
      abiProjectedScalar (exactRecognizedRecordABI model) /\
    abiActualWidth (exactRecognizedRecordABI model) = 64.
Proof.
  intros model H.
  split.
  - rewrite (exact_success_length_identity model H).
    exact (exact_success_expected_length_is_projection model H).
  - pose proof
      (verified_recognized_record_abi_preserves_typed_accessor
        (exactRecognizedRecordABI model)
        (exact_success_recognized_record_abi model H)) as Htyped.
    destruct Htyped as [_ [_ [_ Hwidth]]].
    exact Hwidth.
Qed.

Theorem verified_exact_receive_materializes_exact_payload_owner :
  forall model,
    ExactReceiveVerificationSuccess model ->
    exactActualPayload model = exactExpectedPayload model /\
    exactPayloadExtractedFromReceiveResult model = true.
Proof.
  intros model H.
  split.
  - exact (exact_success_payload_identity model H).
  - exact (exact_success_payload_from_result model H).
Qed.

Theorem verified_exact_receive_uses_fail_closed_status_and_exact_edges :
  forall model,
    ExactReceiveVerificationSuccess model ->
    exactStatusConstant model = 1 /\
    exactActualSuccessBlock model = exactExpectedSuccessBlock model /\
    exactActualFailureBlock model = exactExpectedFailureBlock model.
Proof.
  intros model H.
  repeat split.
  - exact (exact_success_fail_closed_status model H).
  - exact (exact_success_success_edge model H).
  - exact (exact_success_failure_edge model H).
Qed.

Theorem verified_exact_receive_releases_exact_owner_on_failure_and_later_release :
  forall model,
    ExactReceiveVerificationSuccess model ->
    exactFailureReleasedPayload model = exactExpectedPayload model /\
    exactOrdinaryReleasedPayload model = exactExpectedPayload model.
Proof.
  intros model H.
  split.
  - rewrite (exact_success_failure_release_identity model H).
    exact (exact_success_payload_identity model H).
  - rewrite (exact_success_ordinary_release_identity model H).
    exact (exact_success_payload_identity model H).
Qed.

Theorem verified_exact_receive_forbids_ambient_state_layout_access_and_unauthorized_strengthening :
  forall model,
    ExactReceiveVerificationSuccess model ->
    exactAmbientTransportPresent model = false /\
    exactAmbientPayloadPresent model = false /\
    exactObsoleteLengthOnlySignaturePresent model = false /\
    exactPayloadLayoutAccessPresent model = false /\
    exactUnauthorizedPayloadPointerStrengtheningPresent model = false.
Proof.
  intros model H.
  repeat split.
  - exact (exact_success_no_ambient_transport model H).
  - exact (exact_success_no_ambient_payload model H).
  - exact (exact_success_no_obsolete_signature model H).
  - exact (exact_success_no_payload_layout_access model H).
  - exact (exact_success_no_unauthorized_payload_strengthening model H).
Qed.

Theorem exact_receive_transport_drift_is_rejected :
  forall model,
    exactActualTransport model <> exactExpectedTransport model ->
    ~ ExactReceiveVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (exact_success_transport_identity model H).
Qed.

Theorem exact_receive_length_drift_is_rejected :
  forall model,
    exactActualLength model <> exactExpectedLength model ->
    ~ ExactReceiveVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (exact_success_length_identity model H).
Qed.

Theorem exact_receive_payload_identity_drift_is_rejected :
  forall model,
    exactActualPayload model <> exactExpectedPayload model ->
    ~ ExactReceiveVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (exact_success_payload_identity model H).
Qed.

Theorem exact_receive_status_drift_is_rejected :
  forall model,
    exactStatusConstant model <> 1 ->
    ~ ExactReceiveVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (exact_success_fail_closed_status model H).
Qed.

Theorem exact_receive_failure_cleanup_drift_is_rejected :
  forall model,
    exactFailureReleasedPayload model <> exactActualPayload model ->
    ~ ExactReceiveVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (exact_success_failure_release_identity model H).
Qed.

Theorem exact_receive_ordinary_release_drift_is_rejected :
  forall model,
    exactOrdinaryReleasedPayload model <> exactActualPayload model ->
    ~ ExactReceiveVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (exact_success_ordinary_release_identity model H).
Qed.

Theorem exact_receive_ambient_state_is_rejected :
  forall model,
    exactAmbientTransportPresent model = true \/
    exactAmbientPayloadPresent model = true \/
    exactObsoleteLengthOnlySignaturePresent model = true ->
    ~ ExactReceiveVerificationSuccess model.
Proof.
  intros model Hambient H.
  destruct Hambient as [Htransport | [Hpayload | Hold]].
  - rewrite (exact_success_no_ambient_transport model H) in Htransport.
    discriminate.
  - rewrite (exact_success_no_ambient_payload model H) in Hpayload.
    discriminate.
  - rewrite (exact_success_no_obsolete_signature model H) in Hold.
    discriminate.
Qed.

Theorem exact_receive_payload_layout_or_strengthening_is_rejected :
  forall model,
    exactPayloadLayoutAccessPresent model = true \/
    exactUnauthorizedPayloadPointerStrengtheningPresent model = true ->
    ~ ExactReceiveVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hlayout | Hstrengthening].
  - rewrite (exact_success_no_payload_layout_access model H) in Hlayout.
    discriminate.
  - rewrite (exact_success_no_unauthorized_payload_strengthening model H) in Hstrengthening.
    discriminate.
Qed.
