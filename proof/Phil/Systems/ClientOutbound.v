(*
  PHIL-SYS-CLIENT-OUTBOUND-001 — normalized proof model for the current
  Phase 0 client outbound Hello/Begin semantic successor.

  This theorem certifies semantic construction/dataflow only.  Physical record
  representation, serialization, supported-version encoding, payload-kind
  encoding, SHA-256 provider ABI, transport framing, and physical send lowering
  remain later target/runtime work.
*)

Definition ClientOutboundDecisionId := nat.

Record SystemsClientOutboundModel : Type :=
  mkSystemsClientOutboundModel {
    clientOutboundCurrentSuccessorVerifies : bool;
    clientOutboundRecognitionFailureSuccessorPreservesWitness : bool;

    clientOutboundTransportExact : bool;
    clientOutboundPayloadOwnerExact : bool;

    clientOutboundSupportedVersionsCallCount : nat;
    clientOutboundSupportedVersionsExact : bool;
    clientOutboundHelloConstructCount : nat;
    clientOutboundHelloInputExact : bool;
    clientOutboundHelloRecordExact : bool;
    clientOutboundHelloSendCount : nat;
    clientOutboundHelloSendTransportExact : bool;
    clientOutboundHelloSendRecordExact : bool;
    clientOutboundHelloRecordUseCount : nat;

    clientOutboundBorrowCount : nat;
    clientOutboundBorrowOwnerExact : bool;
    clientOutboundBorrowNonOwning : bool;
    clientOutboundPayloadCopyCount : nat;
    clientOutboundDigestCallCount : nat;
    clientOutboundDigestInputViewExact : bool;
    clientOutboundDigestResultExact : bool;
    clientOutboundLengthProjectionCount : nat;
    clientOutboundLengthProjectionOwnerExact : bool;
    clientOutboundKindProjectionCount : nat;
    clientOutboundKindProjectionOwnerExact : bool;
    clientOutboundBeginConstructCount : nat;
    clientOutboundBeginLengthExact : bool;
    clientOutboundBeginKindExact : bool;
    clientOutboundBeginDigestExact : bool;
    clientOutboundBeginDigestAlgSha256 : bool;
    clientOutboundBeginRecordExact : bool;
    clientOutboundBeginSendCount : nat;
    clientOutboundBeginSendTransportExact : bool;
    clientOutboundBeginSendRecordExact : bool;
    clientOutboundBeginRecordUseCount : nat;

    clientOutboundRecordDecisionWitness : ClientOutboundDecisionId;
    clientOutboundRecordDecisionActual : ClientOutboundDecisionId;
    clientOutboundBorrowDecisionWitness : ClientOutboundDecisionId;
    clientOutboundBorrowDecisionActual : ClientOutboundDecisionId;
    clientOutboundDigestDecisionWitness : ClientOutboundDecisionId;
    clientOutboundDigestDecisionActual : ClientOutboundDecisionId;
    clientOutboundDecisionsBoundToCurrentTarget : bool;
    clientOutboundBorrowInvariantExact : bool;

    clientOutboundPhysicalHelloRepresentationClaimed : bool;
    clientOutboundPhysicalBeginRepresentationClaimed : bool;
    clientOutboundSupportedVersionsRepresentationClaimed : bool;
    clientOutboundPayloadKindRepresentationClaimed : bool;
    clientOutboundSHA256ProviderABIClaimed : bool;
    clientOutboundOuterFramingClaimed : bool
  }.

Record SystemsClientOutboundVerificationSuccess
  (model : SystemsClientOutboundModel) : Prop :=
  mkSystemsClientOutboundVerificationSuccess {
    client_outbound_success_current_successor :
      clientOutboundCurrentSuccessorVerifies model = true;
    client_outbound_success_recognition_successor_preserves :
      clientOutboundRecognitionFailureSuccessorPreservesWitness model = true;

    client_outbound_success_transport :
      clientOutboundTransportExact model = true;
    client_outbound_success_payload_owner :
      clientOutboundPayloadOwnerExact model = true;

    client_outbound_success_supported_versions_count :
      clientOutboundSupportedVersionsCallCount model = 1;
    client_outbound_success_supported_versions_exact :
      clientOutboundSupportedVersionsExact model = true;
    client_outbound_success_hello_construct_count :
      clientOutboundHelloConstructCount model = 1;
    client_outbound_success_hello_input :
      clientOutboundHelloInputExact model = true;
    client_outbound_success_hello_record :
      clientOutboundHelloRecordExact model = true;
    client_outbound_success_hello_send_count :
      clientOutboundHelloSendCount model = 1;
    client_outbound_success_hello_send_transport :
      clientOutboundHelloSendTransportExact model = true;
    client_outbound_success_hello_send_record :
      clientOutboundHelloSendRecordExact model = true;
    client_outbound_success_hello_use_count :
      clientOutboundHelloRecordUseCount model = 1;

    client_outbound_success_borrow_count :
      clientOutboundBorrowCount model = 1;
    client_outbound_success_borrow_owner :
      clientOutboundBorrowOwnerExact model = true;
    client_outbound_success_borrow_nonowning :
      clientOutboundBorrowNonOwning model = true;
    client_outbound_success_no_copy :
      clientOutboundPayloadCopyCount model = 0;
    client_outbound_success_digest_count :
      clientOutboundDigestCallCount model = 1;
    client_outbound_success_digest_input :
      clientOutboundDigestInputViewExact model = true;
    client_outbound_success_digest_result :
      clientOutboundDigestResultExact model = true;
    client_outbound_success_length_count :
      clientOutboundLengthProjectionCount model = 1;
    client_outbound_success_length_owner :
      clientOutboundLengthProjectionOwnerExact model = true;
    client_outbound_success_kind_count :
      clientOutboundKindProjectionCount model = 1;
    client_outbound_success_kind_owner :
      clientOutboundKindProjectionOwnerExact model = true;
    client_outbound_success_begin_construct_count :
      clientOutboundBeginConstructCount model = 1;
    client_outbound_success_begin_length :
      clientOutboundBeginLengthExact model = true;
    client_outbound_success_begin_kind :
      clientOutboundBeginKindExact model = true;
    client_outbound_success_begin_digest :
      clientOutboundBeginDigestExact model = true;
    client_outbound_success_begin_sha256 :
      clientOutboundBeginDigestAlgSha256 model = true;
    client_outbound_success_begin_record :
      clientOutboundBeginRecordExact model = true;
    client_outbound_success_begin_send_count :
      clientOutboundBeginSendCount model = 1;
    client_outbound_success_begin_send_transport :
      clientOutboundBeginSendTransportExact model = true;
    client_outbound_success_begin_send_record :
      clientOutboundBeginSendRecordExact model = true;
    client_outbound_success_begin_use_count :
      clientOutboundBeginRecordUseCount model = 1;

    client_outbound_success_record_decision :
      clientOutboundRecordDecisionActual model =
        clientOutboundRecordDecisionWitness model;
    client_outbound_success_borrow_decision :
      clientOutboundBorrowDecisionActual model =
        clientOutboundBorrowDecisionWitness model;
    client_outbound_success_digest_decision :
      clientOutboundDigestDecisionActual model =
        clientOutboundDigestDecisionWitness model;
    client_outbound_success_decisions_current_target :
      clientOutboundDecisionsBoundToCurrentTarget model = true;
    client_outbound_success_borrow_invariant :
      clientOutboundBorrowInvariantExact model = true;

    client_outbound_success_no_hello_physical_claim :
      clientOutboundPhysicalHelloRepresentationClaimed model = false;
    client_outbound_success_no_begin_physical_claim :
      clientOutboundPhysicalBeginRepresentationClaimed model = false;
    client_outbound_success_no_version_set_physical_claim :
      clientOutboundSupportedVersionsRepresentationClaimed model = false;
    client_outbound_success_no_kind_physical_claim :
      clientOutboundPayloadKindRepresentationClaimed model = false;
    client_outbound_success_no_sha256_provider_abi_claim :
      clientOutboundSHA256ProviderABIClaimed model = false;
    client_outbound_success_no_outer_framing_claim :
      clientOutboundOuterFramingClaimed model = false
  }.

Theorem verified_systems_client_outbound_is_preserved_by_current_successor :
  forall model,
    SystemsClientOutboundVerificationSuccess model ->
    clientOutboundCurrentSuccessorVerifies model = true /\
    clientOutboundRecognitionFailureSuccessorPreservesWitness model = true.
Proof.
  intros model H; split.
  - exact (client_outbound_success_current_successor model H).
  - exact (client_outbound_success_recognition_successor_preserves model H).
Qed.

Theorem verified_systems_client_outbound_preserves_exact_hello_dataflow :
  forall model,
    SystemsClientOutboundVerificationSuccess model ->
    clientOutboundSupportedVersionsCallCount model = 1 /\
    clientOutboundSupportedVersionsExact model = true /\
    clientOutboundHelloConstructCount model = 1 /\
    clientOutboundHelloInputExact model = true /\
    clientOutboundHelloRecordExact model = true /\
    clientOutboundHelloSendCount model = 1 /\
    clientOutboundHelloSendTransportExact model = true /\
    clientOutboundHelloSendRecordExact model = true /\
    clientOutboundHelloRecordUseCount model = 1.
Proof.
  intros model H; repeat split.
  - exact (client_outbound_success_supported_versions_count model H).
  - exact (client_outbound_success_supported_versions_exact model H).
  - exact (client_outbound_success_hello_construct_count model H).
  - exact (client_outbound_success_hello_input model H).
  - exact (client_outbound_success_hello_record model H).
  - exact (client_outbound_success_hello_send_count model H).
  - exact (client_outbound_success_hello_send_transport model H).
  - exact (client_outbound_success_hello_send_record model H).
  - exact (client_outbound_success_hello_use_count model H).
Qed.

Theorem verified_systems_client_outbound_preserves_exact_begin_dataflow :
  forall model,
    SystemsClientOutboundVerificationSuccess model ->
    clientOutboundBorrowCount model = 1 /\
    clientOutboundBorrowOwnerExact model = true /\
    clientOutboundBorrowNonOwning model = true /\
    clientOutboundPayloadCopyCount model = 0 /\
    clientOutboundDigestCallCount model = 1 /\
    clientOutboundDigestInputViewExact model = true /\
    clientOutboundDigestResultExact model = true /\
    clientOutboundLengthProjectionCount model = 1 /\
    clientOutboundLengthProjectionOwnerExact model = true /\
    clientOutboundKindProjectionCount model = 1 /\
    clientOutboundKindProjectionOwnerExact model = true /\
    clientOutboundBeginConstructCount model = 1 /\
    clientOutboundBeginLengthExact model = true /\
    clientOutboundBeginKindExact model = true /\
    clientOutboundBeginDigestExact model = true /\
    clientOutboundBeginDigestAlgSha256 model = true /\
    clientOutboundBeginRecordExact model = true /\
    clientOutboundBeginSendCount model = 1 /\
    clientOutboundBeginSendTransportExact model = true /\
    clientOutboundBeginSendRecordExact model = true /\
    clientOutboundBeginRecordUseCount model = 1.
Proof.
  intros model H; repeat split.
  - exact (client_outbound_success_borrow_count model H).
  - exact (client_outbound_success_borrow_owner model H).
  - exact (client_outbound_success_borrow_nonowning model H).
  - exact (client_outbound_success_no_copy model H).
  - exact (client_outbound_success_digest_count model H).
  - exact (client_outbound_success_digest_input model H).
  - exact (client_outbound_success_digest_result model H).
  - exact (client_outbound_success_length_count model H).
  - exact (client_outbound_success_length_owner model H).
  - exact (client_outbound_success_kind_count model H).
  - exact (client_outbound_success_kind_owner model H).
  - exact (client_outbound_success_begin_construct_count model H).
  - exact (client_outbound_success_begin_length model H).
  - exact (client_outbound_success_begin_kind model H).
  - exact (client_outbound_success_begin_digest model H).
  - exact (client_outbound_success_begin_sha256 model H).
  - exact (client_outbound_success_begin_record model H).
  - exact (client_outbound_success_begin_send_count model H).
  - exact (client_outbound_success_begin_send_transport model H).
  - exact (client_outbound_success_begin_send_record model H).
  - exact (client_outbound_success_begin_use_count model H).
Qed.

Theorem verified_systems_client_outbound_binds_decisions_and_borrow_invariant :
  forall model,
    SystemsClientOutboundVerificationSuccess model ->
    clientOutboundRecordDecisionActual model =
      clientOutboundRecordDecisionWitness model /\
    clientOutboundBorrowDecisionActual model =
      clientOutboundBorrowDecisionWitness model /\
    clientOutboundDigestDecisionActual model =
      clientOutboundDigestDecisionWitness model /\
    clientOutboundDecisionsBoundToCurrentTarget model = true /\
    clientOutboundBorrowInvariantExact model = true.
Proof.
  intros model H; repeat split.
  - exact (client_outbound_success_record_decision model H).
  - exact (client_outbound_success_borrow_decision model H).
  - exact (client_outbound_success_digest_decision model H).
  - exact (client_outbound_success_decisions_current_target model H).
  - exact (client_outbound_success_borrow_invariant model H).
Qed.

Theorem verified_systems_client_outbound_claims_no_physical_representation :
  forall model,
    SystemsClientOutboundVerificationSuccess model ->
    clientOutboundPhysicalHelloRepresentationClaimed model = false /\
    clientOutboundPhysicalBeginRepresentationClaimed model = false /\
    clientOutboundSupportedVersionsRepresentationClaimed model = false /\
    clientOutboundPayloadKindRepresentationClaimed model = false /\
    clientOutboundSHA256ProviderABIClaimed model = false /\
    clientOutboundOuterFramingClaimed model = false.
Proof.
  intros model H; repeat split.
  - exact (client_outbound_success_no_hello_physical_claim model H).
  - exact (client_outbound_success_no_begin_physical_claim model H).
  - exact (client_outbound_success_no_version_set_physical_claim model H).
  - exact (client_outbound_success_no_kind_physical_claim model H).
  - exact (client_outbound_success_no_sha256_provider_abi_claim model H).
  - exact (client_outbound_success_no_outer_framing_claim model H).
Qed.

Theorem systems_client_outbound_hello_drift_is_rejected :
  forall model,
    clientOutboundSupportedVersionsCallCount model <> 1 \/
    clientOutboundHelloConstructCount model <> 1 \/
    clientOutboundHelloInputExact model = false \/
    clientOutboundHelloSendCount model <> 1 \/
    clientOutboundHelloSendTransportExact model = false \/
    clientOutboundHelloSendRecordExact model = false \/
    clientOutboundHelloRecordUseCount model <> 1 ->
    ~ SystemsClientOutboundVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hcount | [Hconstruct | [Hinput | [Hsend | [Htransport | [Hrecord | Huse]]]]]].
  - apply Hcount. exact (client_outbound_success_supported_versions_count model H).
  - apply Hconstruct. exact (client_outbound_success_hello_construct_count model H).
  - rewrite (client_outbound_success_hello_input model H) in Hinput. discriminate.
  - apply Hsend. exact (client_outbound_success_hello_send_count model H).
  - rewrite (client_outbound_success_hello_send_transport model H) in Htransport. discriminate.
  - rewrite (client_outbound_success_hello_send_record model H) in Hrecord. discriminate.
  - apply Huse. exact (client_outbound_success_hello_use_count model H).
Qed.

Theorem systems_client_outbound_begin_or_copy_drift_is_rejected :
  forall model,
    clientOutboundBorrowCount model <> 1 \/
    clientOutboundBorrowOwnerExact model = false \/
    clientOutboundPayloadCopyCount model <> 0 \/
    clientOutboundDigestCallCount model <> 1 \/
    clientOutboundLengthProjectionCount model <> 1 \/
    clientOutboundKindProjectionCount model <> 1 \/
    clientOutboundBeginConstructCount model <> 1 \/
    clientOutboundBeginDigestAlgSha256 model = false \/
    clientOutboundBeginSendCount model <> 1 \/
    clientOutboundBeginSendRecordExact model = false ->
    ~ SystemsClientOutboundVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hborrow | [Howner | [Hcopy | [Hdigest | [Hlength | [Hkind | [Hconstruct | [Hsha | [Hsend | Hrecord]]]]]]]]].
  - apply Hborrow. exact (client_outbound_success_borrow_count model H).
  - rewrite (client_outbound_success_borrow_owner model H) in Howner. discriminate.
  - apply Hcopy. exact (client_outbound_success_no_copy model H).
  - apply Hdigest. exact (client_outbound_success_digest_count model H).
  - apply Hlength. exact (client_outbound_success_length_count model H).
  - apply Hkind. exact (client_outbound_success_kind_count model H).
  - apply Hconstruct. exact (client_outbound_success_begin_construct_count model H).
  - rewrite (client_outbound_success_begin_sha256 model H) in Hsha. discriminate.
  - apply Hsend. exact (client_outbound_success_begin_send_count model H).
  - rewrite (client_outbound_success_begin_send_record model H) in Hrecord. discriminate.
Qed.
