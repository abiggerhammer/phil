From Phil.Assurance Require Import Manifest EvidenceUse.
From Phil.LLVM Require Import ExactReceive.

(*
  PHIL-LLVM-CERT-003 — composition theorem for the proof-bound
  transport-exact-receive-v1 certification tranche.

  This theorem does not model SHA-256, execute LLVM, or implement the runtime.
  It states the closure condition used by the Haskell assurance graph: exact
  receive semantic authority must hold, the exact translation-validation
  artifact must be accepted, the certification revision must be in scope, and
  both the LLVM 18 acceptance gate and ABI-conforming runtime gate must pass.
*)

Record ExactReceiveCertificationModel : Type := mkExactReceiveCertificationModel {
  exactCertificationSemanticModel : ExactReceiveModel;
  exactCertificationArtifactAuthority : ArtifactAuthority;
  exactCertificationScopeModel : ScopeModel;
  exactCertificationRevision : RevisionId;
  exactCertificationTranslationAccepted : bool;
  exactCertificationLLVM18Accepted : bool;
  exactCertificationRuntimeGateAccepted : bool
}.

Record ExactReceiveCertificationSuccess
  (model : ExactReceiveCertificationModel) : Prop :=
  mkExactReceiveCertificationSuccess {
    exact_certification_semantic_success :
      ExactReceiveVerificationSuccess
        (exactCertificationSemanticModel model);
    exact_certification_artifact_success :
      verifyArtifactAuthority
        (exactCertificationArtifactAuthority model) = GateAccepted;
    exact_certification_scope_closure :
      CertificationClosure (exactCertificationScopeModel model);
    exact_certification_revision_in_scope :
      certificationScope
        (exactCertificationScopeModel model)
        (exactCertificationRevision model) = true;
    exact_certification_translation_success :
      exactCertificationTranslationAccepted model = true;
    exact_certification_llvm18_success :
      exactCertificationLLVM18Accepted model = true;
    exact_certification_runtime_gate_success :
      exactCertificationRuntimeGateAccepted model = true
  }.

Theorem exact_receive_certification_requires_semantic_authority :
  forall model,
    ExactReceiveCertificationSuccess model ->
    ExactReceiveVerificationSuccess
      (exactCertificationSemanticModel model).
Proof.
  intros model H.
  exact (exact_certification_semantic_success model H).
Qed.

Theorem exact_receive_certification_requires_exact_artifact_authority :
  forall model,
    ExactReceiveCertificationSuccess model ->
    artifactDeclared (exactCertificationArtifactAuthority model) = true /\
    artifactIdentityMatches (exactCertificationArtifactAuthority model) = true /\
    artifactDigestMatchesTrustedAvailability
      (exactCertificationArtifactAuthority model) = true.
Proof.
  intros model H.
  exact
    (successful_artifact_authority_is_exact
      (exactCertificationArtifactAuthority model)
      (exact_certification_artifact_success model H)).
Qed.

Theorem exact_receive_certification_requires_closed_scope :
  forall model,
    ExactReceiveCertificationSuccess model ->
    revisionDisposition
      (exactCertificationScopeModel model)
      (exactCertificationRevision model) = LocallyAccepted.
Proof.
  intros model H.
  exact
    (in_scope_revision_is_locally_accepted
      (exactCertificationScopeModel model)
      (exactCertificationRevision model)
      (exact_certification_scope_closure model H)
      (exact_certification_revision_in_scope model H)).
Qed.

Theorem exact_receive_certification_requires_translation_and_external_gates :
  forall model,
    ExactReceiveCertificationSuccess model ->
    exactCertificationTranslationAccepted model = true /\
    exactCertificationLLVM18Accepted model = true /\
    exactCertificationRuntimeGateAccepted model = true.
Proof.
  intros model H.
  repeat split.
  - exact (exact_certification_translation_success model H).
  - exact (exact_certification_llvm18_success model H).
  - exact (exact_certification_runtime_gate_success model H).
Qed.

Theorem exact_receive_certification_cannot_succeed_without_semantic_proof :
  forall model,
    ~ ExactReceiveVerificationSuccess
      (exactCertificationSemanticModel model) ->
    ~ ExactReceiveCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (exact_certification_semantic_success model H).
Qed.

Theorem exact_receive_certification_cannot_succeed_without_llvm18_acceptance :
  forall model,
    exactCertificationLLVM18Accepted model = false ->
    ~ ExactReceiveCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (exact_certification_llvm18_success model H) in Hrejected.
  discriminate.
Qed.

Theorem exact_receive_certification_cannot_succeed_without_runtime_gate :
  forall model,
    exactCertificationRuntimeGateAccepted model = false ->
    ~ ExactReceiveCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (exact_certification_runtime_gate_success model H) in Hrejected.
  discriminate.
Qed.
