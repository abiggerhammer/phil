From Phil.Assurance Require Import Manifest EvidenceUse.
From Phil.Systems Require Import Storage.
From Phil.LLVM Require Import Storage.

(*
  PHIL-LLVM-CERT-005 — composition theorem for the proof-bound storage-v1
  certification tranche.

  The theorem closes only when the exact Systems storage authority and exact
  LLVM storage authority align, artifact identity and certification scope are
  exact, translation validation accepts the pair, and the external LLVM 18,
  runtime ABI, and persistence/ownership execution gates pass.

  Provider-side failure-null UploadId behavior is part of external ABI/runtime
  conformance.  It is deliberately not used to establish the generated
  consumer's fail-closed status discipline.
*)

Record StorageCertificationModel : Type :=
  mkStorageCertificationModel {
    storageCertificationSystemsModel : SystemsStorageModel;
    storageCertificationLLVMModel : StorageLLVMModel;
    storageCertificationArtifactAuthority : ArtifactAuthority;
    storageCertificationScopeModel : ScopeModel;
    storageCertificationRevision : RevisionId;
    storageCertificationTranslationAccepted : bool;
    storageCertificationLLVM18Accepted : bool;
    storageCertificationRuntimeABIAccepted : bool;
    storageCertificationPersistenceExecutionAccepted : bool
  }.

Record StorageCertificationSuccess
  (model : StorageCertificationModel) : Prop :=
  mkStorageCertificationSuccess {
    storage_certification_systems_success :
      SystemsStorageVerificationSuccess
        (storageCertificationSystemsModel model);
    storage_certification_llvm_success :
      StorageLLVMVerificationSuccess
        (storageCertificationLLVMModel model);
    storage_certification_models_align :
      llvmStorageSystems (storageCertificationLLVMModel model) =
        storageCertificationSystemsModel model;
    storage_certification_artifact_success :
      verifyArtifactAuthority
        (storageCertificationArtifactAuthority model) = GateAccepted;
    storage_certification_scope_closure :
      CertificationClosure (storageCertificationScopeModel model);
    storage_certification_revision_in_scope :
      certificationScope
        (storageCertificationScopeModel model)
        (storageCertificationRevision model) = true;
    storage_certification_translation_success :
      storageCertificationTranslationAccepted model = true;
    storage_certification_llvm18_success :
      storageCertificationLLVM18Accepted model = true;
    storage_certification_runtime_abi_success :
      storageCertificationRuntimeABIAccepted model = true;
    storage_certification_persistence_execution_success :
      storageCertificationPersistenceExecutionAccepted model = true
  }.

Theorem storage_certification_requires_aligned_semantic_authorities :
  forall model,
    StorageCertificationSuccess model ->
    SystemsStorageVerificationSuccess
      (storageCertificationSystemsModel model) /\
    StorageLLVMVerificationSuccess
      (storageCertificationLLVMModel model) /\
    llvmStorageSystems (storageCertificationLLVMModel model) =
      storageCertificationSystemsModel model.
Proof.
  intros model H.
  split.
  - exact (storage_certification_systems_success model H).
  - split.
    + exact (storage_certification_llvm_success model H).
    + exact (storage_certification_models_align model H).
Qed.

Theorem storage_certification_requires_exact_artifact_authority :
  forall model,
    StorageCertificationSuccess model ->
    artifactDeclared (storageCertificationArtifactAuthority model) = true /\
    artifactIdentityMatches (storageCertificationArtifactAuthority model) = true /\
    artifactDigestMatchesTrustedAvailability
      (storageCertificationArtifactAuthority model) = true.
Proof.
  intros model H.
  exact
    (successful_artifact_authority_is_exact
      (storageCertificationArtifactAuthority model)
      (storage_certification_artifact_success model H)).
Qed.

Theorem storage_certification_requires_closed_scope :
  forall model,
    StorageCertificationSuccess model ->
    revisionDisposition
      (storageCertificationScopeModel model)
      (storageCertificationRevision model) = LocallyAccepted.
Proof.
  intros model H.
  exact
    (in_scope_revision_is_locally_accepted
      (storageCertificationScopeModel model)
      (storageCertificationRevision model)
      (storage_certification_scope_closure model H)
      (storage_certification_revision_in_scope model H)).
Qed.

Theorem storage_certification_requires_translation_and_external_gates :
  forall model,
    StorageCertificationSuccess model ->
    storageCertificationTranslationAccepted model = true /\
    storageCertificationLLVM18Accepted model = true /\
    storageCertificationRuntimeABIAccepted model = true /\
    storageCertificationPersistenceExecutionAccepted model = true.
Proof.
  intros model H.
  repeat split.
  - exact (storage_certification_translation_success model H).
  - exact (storage_certification_llvm18_success model H).
  - exact (storage_certification_runtime_abi_success model H).
  - exact (storage_certification_persistence_execution_success model H).
Qed.

Theorem storage_certification_cannot_succeed_without_systems_proof :
  forall model,
    ~ SystemsStorageVerificationSuccess
      (storageCertificationSystemsModel model) ->
    ~ StorageCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (storage_certification_systems_success model H).
Qed.

Theorem storage_certification_cannot_succeed_without_llvm_proof :
  forall model,
    ~ StorageLLVMVerificationSuccess
      (storageCertificationLLVMModel model) ->
    ~ StorageCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (storage_certification_llvm_success model H).
Qed.

Theorem storage_certification_cannot_succeed_without_runtime_abi_gate :
  forall model,
    storageCertificationRuntimeABIAccepted model = false ->
    ~ StorageCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (storage_certification_runtime_abi_success model H) in Hrejected.
  discriminate.
Qed.

Theorem storage_certification_cannot_succeed_without_persistence_execution_gate :
  forall model,
    storageCertificationPersistenceExecutionAccepted model = false ->
    ~ StorageCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (storage_certification_persistence_execution_success model H) in Hrejected.
  discriminate.
Qed.

Theorem storage_certification_cannot_succeed_without_llvm18_gate :
  forall model,
    storageCertificationLLVM18Accepted model = false ->
    ~ StorageCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (storage_certification_llvm18_success model H) in Hrejected.
  discriminate.
Qed.
