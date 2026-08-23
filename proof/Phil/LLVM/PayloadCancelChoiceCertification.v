From Phil.Assurance Require Import Manifest EvidenceUse.
From Phil.Systems Require Import PayloadCancelChoice.
From Phil.LLVM Require Import PayloadCancelChoice.

(*
  Proof-bound PHIL-LLVM-CERT-009 composition model.

  Exact Systems and LLVM payload/cancel authorities must align with exact
  artifact/scope authority and translation validation. LLVM 18 acceptance,
  provider ABI conformance, native selector/receiver execution, and malformed
  input non-return remain explicit external gates. Physical selector write
  failure remains a residual source/runtime mismatch because source select has
  no failure edge.
*)

Record PayloadCancelChoiceCertificationModel : Type :=
  mkPayloadCancelChoiceCertificationModel {
    payloadCancelCertificationSystemsModel : SystemsPayloadCancelChoiceModel;
    payloadCancelCertificationLLVMModel : PayloadCancelChoiceLLVMModel;
    payloadCancelCertificationArtifactAuthority : ArtifactAuthority;
    payloadCancelCertificationScopeModel : ScopeModel;
    payloadCancelCertificationRevision : RevisionId;
    payloadCancelCertificationTranslationAccepted : bool;
    payloadCancelCertificationLLVM18Accepted : bool;
    payloadCancelCertificationRuntimeABIAccepted : bool;
    payloadCancelCertificationSelectorExecutionAccepted : bool;
    payloadCancelCertificationReceiverExecutionAccepted : bool;
    payloadCancelCertificationMalformedNonReturnAccepted : bool
  }.

Record PayloadCancelChoiceCertificationSuccess
  (model : PayloadCancelChoiceCertificationModel) : Prop :=
  mkPayloadCancelChoiceCertificationSuccess {
    payload_cancel_certification_systems_success :
      SystemsPayloadCancelChoiceVerificationSuccess
        (payloadCancelCertificationSystemsModel model);
    payload_cancel_certification_llvm_success :
      PayloadCancelChoiceLLVMVerificationSuccess
        (payloadCancelCertificationLLVMModel model);
    payload_cancel_certification_models_align :
      llvmPayloadCancelSystems (payloadCancelCertificationLLVMModel model) =
        payloadCancelCertificationSystemsModel model;
    payload_cancel_certification_artifact_success :
      verifyArtifactAuthority
        (payloadCancelCertificationArtifactAuthority model) = GateAccepted;
    payload_cancel_certification_scope_closure :
      CertificationClosure (payloadCancelCertificationScopeModel model);
    payload_cancel_certification_revision_in_scope :
      certificationScope (payloadCancelCertificationScopeModel model)
        (payloadCancelCertificationRevision model) = true;
    payload_cancel_certification_translation_success :
      payloadCancelCertificationTranslationAccepted model = true;
    payload_cancel_certification_llvm18_success :
      payloadCancelCertificationLLVM18Accepted model = true;
    payload_cancel_certification_runtime_abi_success :
      payloadCancelCertificationRuntimeABIAccepted model = true;
    payload_cancel_certification_selector_execution_success :
      payloadCancelCertificationSelectorExecutionAccepted model = true;
    payload_cancel_certification_receiver_execution_success :
      payloadCancelCertificationReceiverExecutionAccepted model = true;
    payload_cancel_certification_malformed_non_return_success :
      payloadCancelCertificationMalformedNonReturnAccepted model = true
  }.

Theorem payload_cancel_certification_requires_aligned_semantic_authorities :
  forall model, PayloadCancelChoiceCertificationSuccess model ->
  SystemsPayloadCancelChoiceVerificationSuccess
    (payloadCancelCertificationSystemsModel model) /\
  PayloadCancelChoiceLLVMVerificationSuccess
    (payloadCancelCertificationLLVMModel model) /\
  llvmPayloadCancelSystems (payloadCancelCertificationLLVMModel model) =
    payloadCancelCertificationSystemsModel model.
Proof.
  intros model H.
  split.
  - exact (payload_cancel_certification_systems_success model H).
  - split.
    + exact (payload_cancel_certification_llvm_success model H).
    + exact (payload_cancel_certification_models_align model H).
Qed.

Theorem payload_cancel_certification_requires_exact_artifact_authority :
  forall model, PayloadCancelChoiceCertificationSuccess model ->
  artifactDeclared (payloadCancelCertificationArtifactAuthority model) = true /\
  artifactIdentityMatches
    (payloadCancelCertificationArtifactAuthority model) = true /\
  artifactDigestMatchesTrustedAvailability
    (payloadCancelCertificationArtifactAuthority model) = true.
Proof.
  intros model H.
  exact (successful_artifact_authority_is_exact
    (payloadCancelCertificationArtifactAuthority model)
    (payload_cancel_certification_artifact_success model H)).
Qed.

Theorem payload_cancel_certification_requires_closed_scope :
  forall model, PayloadCancelChoiceCertificationSuccess model ->
  revisionDisposition (payloadCancelCertificationScopeModel model)
    (payloadCancelCertificationRevision model) = LocallyAccepted.
Proof.
  intros model H.
  exact (in_scope_revision_is_locally_accepted
    (payloadCancelCertificationScopeModel model)
    (payloadCancelCertificationRevision model)
    (payload_cancel_certification_scope_closure model H)
    (payload_cancel_certification_revision_in_scope model H)).
Qed.

Theorem payload_cancel_certification_requires_translation_and_external_gates :
  forall model, PayloadCancelChoiceCertificationSuccess model ->
  payloadCancelCertificationTranslationAccepted model = true /\
  payloadCancelCertificationLLVM18Accepted model = true /\
  payloadCancelCertificationRuntimeABIAccepted model = true /\
  payloadCancelCertificationSelectorExecutionAccepted model = true /\
  payloadCancelCertificationReceiverExecutionAccepted model = true /\
  payloadCancelCertificationMalformedNonReturnAccepted model = true.
Proof.
  intros model H; repeat split.
  - exact (payload_cancel_certification_translation_success model H).
  - exact (payload_cancel_certification_llvm18_success model H).
  - exact (payload_cancel_certification_runtime_abi_success model H).
  - exact (payload_cancel_certification_selector_execution_success model H).
  - exact (payload_cancel_certification_receiver_execution_success model H).
  - exact (payload_cancel_certification_malformed_non_return_success model H).
Qed.

Theorem payload_cancel_certification_cannot_succeed_without_systems_proof :
  forall model,
  ~ SystemsPayloadCancelChoiceVerificationSuccess
      (payloadCancelCertificationSystemsModel model) ->
  ~ PayloadCancelChoiceCertificationSuccess model.
Proof.
  intros model Hmissing H; apply Hmissing.
  exact (payload_cancel_certification_systems_success model H).
Qed.

Theorem payload_cancel_certification_cannot_succeed_without_llvm_proof :
  forall model,
  ~ PayloadCancelChoiceLLVMVerificationSuccess
      (payloadCancelCertificationLLVMModel model) ->
  ~ PayloadCancelChoiceCertificationSuccess model.
Proof.
  intros model Hmissing H; apply Hmissing.
  exact (payload_cancel_certification_llvm_success model H).
Qed.

Theorem payload_cancel_certification_cannot_succeed_without_runtime_abi_gate :
  forall model,
  payloadCancelCertificationRuntimeABIAccepted model = false ->
  ~ PayloadCancelChoiceCertificationSuccess model.
Proof.
  intros model Hbad H.
  rewrite (payload_cancel_certification_runtime_abi_success model H) in Hbad.
  discriminate.
Qed.

Theorem payload_cancel_certification_cannot_succeed_without_malformed_non_return_gate :
  forall model,
  payloadCancelCertificationMalformedNonReturnAccepted model = false ->
  ~ PayloadCancelChoiceCertificationSuccess model.
Proof.
  intros model Hbad H.
  rewrite (payload_cancel_certification_malformed_non_return_success model H) in Hbad.
  discriminate.
Qed.
