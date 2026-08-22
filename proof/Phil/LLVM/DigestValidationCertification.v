From Phil.Assurance Require Import Manifest EvidenceUse.
From Phil.Systems Require Import DigestValidation.
From Phil.LLVM Require Import DigestValidation.

(*
  PHIL-LLVM-CERT-004 — composition theorem for the proof-bound
  digest-validation-v1 certification tranche.

  This theorem does not model SHA-256 internals or execute LLVM/libcrypto.  It
  states the closure condition used by the Haskell assurance graph: exact
  Systems subject/borrow authority and exact LLVM digest-lowering authority
  must agree, exact artifact authority and certification scope must close, the
  translation validator must accept the exact pair, and the external LLVM 18,
  runtime ABI, and SHA-256 match/mismatch execution gates must succeed.
*)

Record DigestValidationCertificationModel : Type :=
  mkDigestValidationCertificationModel {
    digestCertificationSystemsModel : SystemsDigestValidationModel;
    digestCertificationLLVMModel : DigestValidationLLVMModel;
    digestCertificationArtifactAuthority : ArtifactAuthority;
    digestCertificationScopeModel : ScopeModel;
    digestCertificationRevision : RevisionId;
    digestCertificationTranslationAccepted : bool;
    digestCertificationLLVM18Accepted : bool;
    digestCertificationRuntimeABIAccepted : bool;
    digestCertificationSHA256ExecutionAccepted : bool
  }.

Record DigestValidationCertificationSuccess
  (model : DigestValidationCertificationModel) : Prop :=
  mkDigestValidationCertificationSuccess {
    digest_certification_systems_success :
      SystemsDigestValidationVerificationSuccess
        (digestCertificationSystemsModel model);
    digest_certification_llvm_success :
      DigestValidationLLVMVerificationSuccess
        (digestCertificationLLVMModel model);
    digest_certification_models_align :
      llvmDigestSystems (digestCertificationLLVMModel model) =
        digestCertificationSystemsModel model;
    digest_certification_artifact_success :
      verifyArtifactAuthority
        (digestCertificationArtifactAuthority model) = GateAccepted;
    digest_certification_scope_closure :
      CertificationClosure (digestCertificationScopeModel model);
    digest_certification_revision_in_scope :
      certificationScope
        (digestCertificationScopeModel model)
        (digestCertificationRevision model) = true;
    digest_certification_translation_success :
      digestCertificationTranslationAccepted model = true;
    digest_certification_llvm18_success :
      digestCertificationLLVM18Accepted model = true;
    digest_certification_runtime_abi_success :
      digestCertificationRuntimeABIAccepted model = true;
    digest_certification_sha256_execution_success :
      digestCertificationSHA256ExecutionAccepted model = true
  }.

Theorem digest_validation_certification_requires_aligned_semantic_authorities :
  forall model,
    DigestValidationCertificationSuccess model ->
    SystemsDigestValidationVerificationSuccess
      (digestCertificationSystemsModel model) /\
    DigestValidationLLVMVerificationSuccess
      (digestCertificationLLVMModel model) /\
    llvmDigestSystems (digestCertificationLLVMModel model) =
      digestCertificationSystemsModel model.
Proof.
  intros model H.
  repeat split.
  - exact (digest_certification_systems_success model H).
  - exact (digest_certification_llvm_success model H).
  - exact (digest_certification_models_align model H).
Qed.

Theorem digest_validation_certification_requires_exact_artifact_authority :
  forall model,
    DigestValidationCertificationSuccess model ->
    artifactDeclared (digestCertificationArtifactAuthority model) = true /\
    artifactIdentityMatches (digestCertificationArtifactAuthority model) = true /\
    artifactDigestMatchesTrustedAvailability
      (digestCertificationArtifactAuthority model) = true.
Proof.
  intros model H.
  exact
    (successful_artifact_authority_is_exact
      (digestCertificationArtifactAuthority model)
      (digest_certification_artifact_success model H)).
Qed.

Theorem digest_validation_certification_requires_closed_scope :
  forall model,
    DigestValidationCertificationSuccess model ->
    revisionDisposition
      (digestCertificationScopeModel model)
      (digestCertificationRevision model) = LocallyAccepted.
Proof.
  intros model H.
  exact
    (in_scope_revision_is_locally_accepted
      (digestCertificationScopeModel model)
      (digestCertificationRevision model)
      (digest_certification_scope_closure model H)
      (digest_certification_revision_in_scope model H)).
Qed.

Theorem digest_validation_certification_requires_translation_and_external_gates :
  forall model,
    DigestValidationCertificationSuccess model ->
    digestCertificationTranslationAccepted model = true /\
    digestCertificationLLVM18Accepted model = true /\
    digestCertificationRuntimeABIAccepted model = true /\
    digestCertificationSHA256ExecutionAccepted model = true.
Proof.
  intros model H.
  repeat split.
  - exact (digest_certification_translation_success model H).
  - exact (digest_certification_llvm18_success model H).
  - exact (digest_certification_runtime_abi_success model H).
  - exact (digest_certification_sha256_execution_success model H).
Qed.

Theorem digest_validation_certification_cannot_succeed_without_systems_proof :
  forall model,
    ~ SystemsDigestValidationVerificationSuccess
      (digestCertificationSystemsModel model) ->
    ~ DigestValidationCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (digest_certification_systems_success model H).
Qed.

Theorem digest_validation_certification_cannot_succeed_without_llvm_proof :
  forall model,
    ~ DigestValidationLLVMVerificationSuccess
      (digestCertificationLLVMModel model) ->
    ~ DigestValidationCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (digest_certification_llvm_success model H).
Qed.

Theorem digest_validation_certification_cannot_succeed_without_sha256_execution_gate :
  forall model,
    digestCertificationSHA256ExecutionAccepted model = false ->
    ~ DigestValidationCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (digest_certification_sha256_execution_success model H) in Hrejected.
  discriminate.
Qed.

Theorem digest_validation_certification_cannot_succeed_without_runtime_abi_gate :
  forall model,
    digestCertificationRuntimeABIAccepted model = false ->
    ~ DigestValidationCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (digest_certification_runtime_abi_success model H) in Hrejected.
  discriminate.
Qed.

Theorem digest_validation_certification_cannot_succeed_without_llvm18_gate :
  forall model,
    digestCertificationLLVM18Accepted model = false ->
    ~ DigestValidationCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (digest_certification_llvm18_success model H) in Hrejected.
  discriminate.
Qed.
