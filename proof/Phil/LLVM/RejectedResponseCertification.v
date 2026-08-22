From Phil.Assurance Require Import Manifest EvidenceUse.
From Phil.Systems Require Import RejectedResponse.
From Phil.LLVM Require Import RejectedResponse.

(*
  PHIL-LLVM-CERT-007 — composition theorem for proof-bound
  rejected-response-v1 certification.

  Certification closes only when exact Systems rejected-response authority and
  exact LLVM rejected-response authority align, exact artifact authority and
  certification scope close, translation validation accepts the pair, and the
  external LLVM 18, runtime ABI, and rejected-response wire execution gates
  pass.

  Rocq proves the semantic/representation relation through the explicit reason
  code.  It does not prove the provider's concrete two-octet write 00 01,
  physical write success, outer framing, or native runtime implementation.
*)

Record RejectedResponseCertificationModel : Type :=
  mkRejectedResponseCertificationModel {
    rejectedCertificationSystemsModel : SystemsRejectedResponseModel;
    rejectedCertificationLLVMModel : RejectedResponseLLVMModel;
    rejectedCertificationArtifactAuthority : ArtifactAuthority;
    rejectedCertificationScopeModel : ScopeModel;
    rejectedCertificationRevision : RevisionId;
    rejectedCertificationTranslationAccepted : bool;
    rejectedCertificationLLVM18Accepted : bool;
    rejectedCertificationRuntimeABIAccepted : bool;
    rejectedCertificationWireExecutionAccepted : bool
  }.

Record RejectedResponseCertificationSuccess
  (model : RejectedResponseCertificationModel) : Prop :=
  mkRejectedResponseCertificationSuccess {
    rejected_certification_systems_success :
      SystemsRejectedResponseVerificationSuccess
        (rejectedCertificationSystemsModel model);
    rejected_certification_llvm_success :
      RejectedResponseLLVMVerificationSuccess
        (rejectedCertificationLLVMModel model);
    rejected_certification_models_align :
      llvmRejectedSystems (rejectedCertificationLLVMModel model) =
        rejectedCertificationSystemsModel model;
    rejected_certification_artifact_success :
      verifyArtifactAuthority
        (rejectedCertificationArtifactAuthority model) = GateAccepted;
    rejected_certification_scope_closure :
      CertificationClosure (rejectedCertificationScopeModel model);
    rejected_certification_revision_in_scope :
      certificationScope
        (rejectedCertificationScopeModel model)
        (rejectedCertificationRevision model) = true;
    rejected_certification_translation_success :
      rejectedCertificationTranslationAccepted model = true;
    rejected_certification_llvm18_success :
      rejectedCertificationLLVM18Accepted model = true;
    rejected_certification_runtime_abi_success :
      rejectedCertificationRuntimeABIAccepted model = true;
    rejected_certification_wire_execution_success :
      rejectedCertificationWireExecutionAccepted model = true
  }.

Theorem rejected_response_certification_requires_aligned_semantic_authorities :
  forall model,
    RejectedResponseCertificationSuccess model ->
    SystemsRejectedResponseVerificationSuccess
      (rejectedCertificationSystemsModel model) /\
    RejectedResponseLLVMVerificationSuccess
      (rejectedCertificationLLVMModel model) /\
    llvmRejectedSystems (rejectedCertificationLLVMModel model) =
      rejectedCertificationSystemsModel model.
Proof.
  intros model H.
  split.
  - exact (rejected_certification_systems_success model H).
  - split.
    + exact (rejected_certification_llvm_success model H).
    + exact (rejected_certification_models_align model H).
Qed.

Theorem rejected_response_certification_requires_exact_artifact_authority :
  forall model,
    RejectedResponseCertificationSuccess model ->
    artifactDeclared (rejectedCertificationArtifactAuthority model) = true /\
    artifactIdentityMatches (rejectedCertificationArtifactAuthority model) = true /\
    artifactDigestMatchesTrustedAvailability
      (rejectedCertificationArtifactAuthority model) = true.
Proof.
  intros model H.
  exact
    (successful_artifact_authority_is_exact
      (rejectedCertificationArtifactAuthority model)
      (rejected_certification_artifact_success model H)).
Qed.

Theorem rejected_response_certification_requires_closed_scope :
  forall model,
    RejectedResponseCertificationSuccess model ->
    revisionDisposition
      (rejectedCertificationScopeModel model)
      (rejectedCertificationRevision model) = LocallyAccepted.
Proof.
  intros model H.
  exact
    (in_scope_revision_is_locally_accepted
      (rejectedCertificationScopeModel model)
      (rejectedCertificationRevision model)
      (rejected_certification_scope_closure model H)
      (rejected_certification_revision_in_scope model H)).
Qed.

Theorem rejected_response_certification_requires_translation_and_external_gates :
  forall model,
    RejectedResponseCertificationSuccess model ->
    rejectedCertificationTranslationAccepted model = true /\
    rejectedCertificationLLVM18Accepted model = true /\
    rejectedCertificationRuntimeABIAccepted model = true /\
    rejectedCertificationWireExecutionAccepted model = true.
Proof.
  intros model H.
  repeat split.
  - exact (rejected_certification_translation_success model H).
  - exact (rejected_certification_llvm18_success model H).
  - exact (rejected_certification_runtime_abi_success model H).
  - exact (rejected_certification_wire_execution_success model H).
Qed.

Theorem rejected_response_certification_cannot_succeed_without_systems_proof :
  forall model,
    ~ SystemsRejectedResponseVerificationSuccess
      (rejectedCertificationSystemsModel model) ->
    ~ RejectedResponseCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (rejected_certification_systems_success model H).
Qed.

Theorem rejected_response_certification_cannot_succeed_without_llvm_proof :
  forall model,
    ~ RejectedResponseLLVMVerificationSuccess
      (rejectedCertificationLLVMModel model) ->
    ~ RejectedResponseCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (rejected_certification_llvm_success model H).
Qed.

Theorem rejected_response_certification_cannot_succeed_without_runtime_abi_gate :
  forall model,
    rejectedCertificationRuntimeABIAccepted model = false ->
    ~ RejectedResponseCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (rejected_certification_runtime_abi_success model H) in Hrejected.
  discriminate.
Qed.

Theorem rejected_response_certification_cannot_succeed_without_wire_execution_gate :
  forall model,
    rejectedCertificationWireExecutionAccepted model = false ->
    ~ RejectedResponseCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (rejected_certification_wire_execution_success model H) in Hrejected.
  discriminate.
Qed.

Theorem rejected_response_certification_cannot_succeed_without_llvm18_gate :
  forall model,
    rejectedCertificationLLVM18Accepted model = false ->
    ~ RejectedResponseCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (rejected_certification_llvm18_success model H) in Hrejected.
  discriminate.
Qed.
