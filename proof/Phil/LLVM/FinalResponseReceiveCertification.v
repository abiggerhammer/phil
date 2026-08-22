From Phil.Assurance Require Import Manifest EvidenceUse.
From Phil.Systems Require Import FinalResponse.
From Phil.LLVM Require Import FinalResponseReceive.

(*
  Proof-bound PHIL-LLVM-CERT-008 composition model.

  Exact Systems and LLVM final-response authorities must align with exact
  artifact/scope authority and translation validation. LLVM 18 acceptance,
  provider ABI conformance, accepted/rejected native execution, and malformed
  input non-return remain explicit external gates rather than Rocq claims.
*)

Record FinalResponseReceiveCertificationModel : Type :=
  mkFinalResponseReceiveCertificationModel {
    finalCertificationSystemsModel : SystemsFinalResponseModel;
    finalCertificationLLVMModel : FinalResponseReceiveLLVMModel;
    finalCertificationArtifactAuthority : ArtifactAuthority;
    finalCertificationScopeModel : ScopeModel;
    finalCertificationRevision : RevisionId;
    finalCertificationTranslationAccepted : bool;
    finalCertificationLLVM18Accepted : bool;
    finalCertificationRuntimeABIAccepted : bool;
    finalCertificationAcceptedExecutionAccepted : bool;
    finalCertificationRejectedExecutionAccepted : bool;
    finalCertificationMalformedNonReturnAccepted : bool
  }.

Record FinalResponseReceiveCertificationSuccess
  (model : FinalResponseReceiveCertificationModel) : Prop :=
  mkFinalResponseReceiveCertificationSuccess {
    final_certification_systems_success :
      SystemsFinalResponseVerificationSuccess
        (finalCertificationSystemsModel model);
    final_certification_llvm_success :
      FinalResponseReceiveLLVMVerificationSuccess
        (finalCertificationLLVMModel model);
    final_certification_models_align :
      llvmFinalSystems (finalCertificationLLVMModel model) =
        finalCertificationSystemsModel model;
    final_certification_artifact_success :
      verifyArtifactAuthority (finalCertificationArtifactAuthority model) = GateAccepted;
    final_certification_scope_closure :
      CertificationClosure (finalCertificationScopeModel model);
    final_certification_revision_in_scope :
      certificationScope (finalCertificationScopeModel model)
        (finalCertificationRevision model) = true;
    final_certification_translation_success :
      finalCertificationTranslationAccepted model = true;
    final_certification_llvm18_success :
      finalCertificationLLVM18Accepted model = true;
    final_certification_runtime_abi_success :
      finalCertificationRuntimeABIAccepted model = true;
    final_certification_accepted_execution_success :
      finalCertificationAcceptedExecutionAccepted model = true;
    final_certification_rejected_execution_success :
      finalCertificationRejectedExecutionAccepted model = true;
    final_certification_malformed_non_return_success :
      finalCertificationMalformedNonReturnAccepted model = true
  }.

Theorem final_response_certification_requires_aligned_semantic_authorities :
  forall model, FinalResponseReceiveCertificationSuccess model ->
  SystemsFinalResponseVerificationSuccess (finalCertificationSystemsModel model) /\
  FinalResponseReceiveLLVMVerificationSuccess (finalCertificationLLVMModel model) /\
  llvmFinalSystems (finalCertificationLLVMModel model) = finalCertificationSystemsModel model.
Proof.
  intros model H.
  split.
  - exact (final_certification_systems_success model H).
  - split.
    + exact (final_certification_llvm_success model H).
    + exact (final_certification_models_align model H).
Qed.

Theorem final_response_certification_requires_exact_artifact_authority :
  forall model, FinalResponseReceiveCertificationSuccess model ->
  artifactDeclared (finalCertificationArtifactAuthority model) = true /\
  artifactIdentityMatches (finalCertificationArtifactAuthority model) = true /\
  artifactDigestMatchesTrustedAvailability
    (finalCertificationArtifactAuthority model) = true.
Proof.
  intros model H.
  exact (successful_artifact_authority_is_exact
    (finalCertificationArtifactAuthority model)
    (final_certification_artifact_success model H)).
Qed.

Theorem final_response_certification_requires_closed_scope :
  forall model, FinalResponseReceiveCertificationSuccess model ->
  revisionDisposition (finalCertificationScopeModel model)
    (finalCertificationRevision model) = LocallyAccepted.
Proof.
  intros model H.
  exact (in_scope_revision_is_locally_accepted
    (finalCertificationScopeModel model)
    (finalCertificationRevision model)
    (final_certification_scope_closure model H)
    (final_certification_revision_in_scope model H)).
Qed.

Theorem final_response_certification_requires_translation_and_external_gates :
  forall model, FinalResponseReceiveCertificationSuccess model ->
  finalCertificationTranslationAccepted model = true /\
  finalCertificationLLVM18Accepted model = true /\
  finalCertificationRuntimeABIAccepted model = true /\
  finalCertificationAcceptedExecutionAccepted model = true /\
  finalCertificationRejectedExecutionAccepted model = true /\
  finalCertificationMalformedNonReturnAccepted model = true.
Proof.
  intros model H; repeat split.
  - exact (final_certification_translation_success model H).
  - exact (final_certification_llvm18_success model H).
  - exact (final_certification_runtime_abi_success model H).
  - exact (final_certification_accepted_execution_success model H).
  - exact (final_certification_rejected_execution_success model H).
  - exact (final_certification_malformed_non_return_success model H).
Qed.

Theorem final_response_certification_cannot_succeed_without_systems_proof :
  forall model,
  ~ SystemsFinalResponseVerificationSuccess (finalCertificationSystemsModel model) ->
  ~ FinalResponseReceiveCertificationSuccess model.
Proof.
  intros model Hmissing H; apply Hmissing.
  exact (final_certification_systems_success model H).
Qed.

Theorem final_response_certification_cannot_succeed_without_llvm_proof :
  forall model,
  ~ FinalResponseReceiveLLVMVerificationSuccess (finalCertificationLLVMModel model) ->
  ~ FinalResponseReceiveCertificationSuccess model.
Proof.
  intros model Hmissing H; apply Hmissing.
  exact (final_certification_llvm_success model H).
Qed.

Theorem final_response_certification_cannot_succeed_without_runtime_abi_gate :
  forall model, finalCertificationRuntimeABIAccepted model = false ->
  ~ FinalResponseReceiveCertificationSuccess model.
Proof.
  intros model Hbad H.
  rewrite (final_certification_runtime_abi_success model H) in Hbad; discriminate.
Qed.

Theorem final_response_certification_cannot_succeed_without_malformed_non_return_gate :
  forall model, finalCertificationMalformedNonReturnAccepted model = false ->
  ~ FinalResponseReceiveCertificationSuccess model.
Proof.
  intros model Hbad H.
  rewrite (final_certification_malformed_non_return_success model H) in Hbad; discriminate.
Qed.
