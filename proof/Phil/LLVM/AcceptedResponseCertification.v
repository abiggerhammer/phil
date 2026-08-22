From Phil.Assurance Require Import Manifest EvidenceUse.
From Phil.Systems Require Import AcceptedResponse.
From Phil.LLVM Require Import AcceptedResponse.

(*
  PHIL-LLVM-CERT-006 — composition theorem for proof-bound
  accepted-response-v1 certification.

  The theorem closes only when exact Systems accepted-response authority and
  exact LLVM accepted-response authority align, artifact identity and scope are
  exact, translation validation accepts the pair, and the external LLVM 18,
  runtime ABI, and exact accepted-response wire execution gates pass.

  The 17-octet encoding itself is not proved in Rocq; it remains an explicit
  external runtime gate.  Outer framing, physical write failure, and UploadId
  freshness/uniqueness remain residual boundaries.
*)

Record AcceptedResponseCertificationModel : Type :=
  mkAcceptedResponseCertificationModel {
    acceptedCertificationSystemsModel : SystemsAcceptedResponseModel;
    acceptedCertificationLLVMModel : AcceptedResponseLLVMModel;
    acceptedCertificationArtifactAuthority : ArtifactAuthority;
    acceptedCertificationScopeModel : ScopeModel;
    acceptedCertificationRevision : RevisionId;
    acceptedCertificationTranslationAccepted : bool;
    acceptedCertificationLLVM18Accepted : bool;
    acceptedCertificationRuntimeABIAccepted : bool;
    acceptedCertificationWireExecutionAccepted : bool
  }.

Record AcceptedResponseCertificationSuccess
  (model : AcceptedResponseCertificationModel) : Prop :=
  mkAcceptedResponseCertificationSuccess {
    accepted_certification_systems_success :
      SystemsAcceptedResponseVerificationSuccess
        (acceptedCertificationSystemsModel model);
    accepted_certification_llvm_success :
      AcceptedResponseLLVMVerificationSuccess
        (acceptedCertificationLLVMModel model);
    accepted_certification_models_align :
      llvmAcceptedSystems (acceptedCertificationLLVMModel model) =
        acceptedCertificationSystemsModel model;
    accepted_certification_artifact_success :
      verifyArtifactAuthority
        (acceptedCertificationArtifactAuthority model) = GateAccepted;
    accepted_certification_scope_closure :
      CertificationClosure (acceptedCertificationScopeModel model);
    accepted_certification_revision_in_scope :
      certificationScope
        (acceptedCertificationScopeModel model)
        (acceptedCertificationRevision model) = true;
    accepted_certification_translation_success :
      acceptedCertificationTranslationAccepted model = true;
    accepted_certification_llvm18_success :
      acceptedCertificationLLVM18Accepted model = true;
    accepted_certification_runtime_abi_success :
      acceptedCertificationRuntimeABIAccepted model = true;
    accepted_certification_wire_execution_success :
      acceptedCertificationWireExecutionAccepted model = true
  }.

Theorem accepted_response_certification_requires_aligned_semantic_authorities :
  forall model,
    AcceptedResponseCertificationSuccess model ->
    SystemsAcceptedResponseVerificationSuccess
      (acceptedCertificationSystemsModel model) /\
    AcceptedResponseLLVMVerificationSuccess
      (acceptedCertificationLLVMModel model) /\
    llvmAcceptedSystems (acceptedCertificationLLVMModel model) =
      acceptedCertificationSystemsModel model.
Proof.
  intros model H.
  split.
  - exact (accepted_certification_systems_success model H).
  - split.
    + exact (accepted_certification_llvm_success model H).
    + exact (accepted_certification_models_align model H).
Qed.

Theorem accepted_response_certification_requires_exact_artifact_authority :
  forall model,
    AcceptedResponseCertificationSuccess model ->
    artifactDeclared (acceptedCertificationArtifactAuthority model) = true /\
    artifactIdentityMatches (acceptedCertificationArtifactAuthority model) = true /\
    artifactDigestMatchesTrustedAvailability
      (acceptedCertificationArtifactAuthority model) = true.
Proof.
  intros model H.
  exact
    (successful_artifact_authority_is_exact
      (acceptedCertificationArtifactAuthority model)
      (accepted_certification_artifact_success model H)).
Qed.

Theorem accepted_response_certification_requires_closed_scope :
  forall model,
    AcceptedResponseCertificationSuccess model ->
    revisionDisposition
      (acceptedCertificationScopeModel model)
      (acceptedCertificationRevision model) = LocallyAccepted.
Proof.
  intros model H.
  exact
    (in_scope_revision_is_locally_accepted
      (acceptedCertificationScopeModel model)
      (acceptedCertificationRevision model)
      (accepted_certification_scope_closure model H)
      (accepted_certification_revision_in_scope model H)).
Qed.

Theorem accepted_response_certification_requires_translation_and_external_gates :
  forall model,
    AcceptedResponseCertificationSuccess model ->
    acceptedCertificationTranslationAccepted model = true /\
    acceptedCertificationLLVM18Accepted model = true /\
    acceptedCertificationRuntimeABIAccepted model = true /\
    acceptedCertificationWireExecutionAccepted model = true.
Proof.
  intros model H.
  repeat split.
  - exact (accepted_certification_translation_success model H).
  - exact (accepted_certification_llvm18_success model H).
  - exact (accepted_certification_runtime_abi_success model H).
  - exact (accepted_certification_wire_execution_success model H).
Qed.

Theorem accepted_response_certification_cannot_succeed_without_systems_proof :
  forall model,
    ~ SystemsAcceptedResponseVerificationSuccess
      (acceptedCertificationSystemsModel model) ->
    ~ AcceptedResponseCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (accepted_certification_systems_success model H).
Qed.

Theorem accepted_response_certification_cannot_succeed_without_llvm_proof :
  forall model,
    ~ AcceptedResponseLLVMVerificationSuccess
      (acceptedCertificationLLVMModel model) ->
    ~ AcceptedResponseCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (accepted_certification_llvm_success model H).
Qed.

Theorem accepted_response_certification_cannot_succeed_without_runtime_abi_gate :
  forall model,
    acceptedCertificationRuntimeABIAccepted model = false ->
    ~ AcceptedResponseCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (accepted_certification_runtime_abi_success model H) in Hrejected.
  discriminate.
Qed.

Theorem accepted_response_certification_cannot_succeed_without_wire_execution_gate :
  forall model,
    acceptedCertificationWireExecutionAccepted model = false ->
    ~ AcceptedResponseCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (accepted_certification_wire_execution_success model H) in Hrejected.
  discriminate.
Qed.

Theorem accepted_response_certification_cannot_succeed_without_llvm18_gate :
  forall model,
    acceptedCertificationLLVM18Accepted model = false ->
    ~ AcceptedResponseCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (accepted_certification_llvm18_success model H) in Hrejected.
  discriminate.
Qed.
