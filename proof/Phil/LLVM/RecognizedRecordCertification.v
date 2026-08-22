From Phil.Assurance Require Import Manifest EvidenceUse.
From Phil.Systems Require Import RecognizedRecord.
From Phil.LLVM Require Import RecognizedRecordABI RuntimeSymbolIdentity.

(*
  PHIL-LLVM-CERT-002 — composition theorem for the proof-bound recognized-record
  certification tranche.

  This theorem does not model SHA-256 or execute LLVM.  It states the logical
  closure condition used by the Haskell assurance graph: recognized-record
  Systems provenance, concrete ABI-v1 lowering, and runtime-symbol separation
  must all hold; the exact translation-validation artifact must be accepted;
  the certification revision must be in scope; and the external LLVM 18 gate
  must succeed.
*)

Record RecognizedRecordCertificationModel : Type := mkRecognizedRecordCertificationModel {
  recognizedCertificationSystemsModel : RecognizedRecordModel;
  recognizedCertificationABIModel : RecognizedRecordABIModel;
  recognizedCertificationSymbolModel : RuntimeSymbolModel;
  recognizedCertificationArtifactAuthority : ArtifactAuthority;
  recognizedCertificationScopeModel : ScopeModel;
  recognizedCertificationRevision : RevisionId;
  recognizedCertificationTranslationAccepted : bool;
  recognizedCertificationLLVM18Accepted : bool
}.

Record RecognizedRecordCertificationSuccess
  (model : RecognizedRecordCertificationModel) : Prop :=
  mkRecognizedRecordCertificationSuccess {
    recognized_certification_systems_success :
      RecognizedRecordVerificationSuccess
        (recognizedCertificationSystemsModel model);
    recognized_certification_abi_success :
      RecognizedRecordABIVerificationSuccess
        (recognizedCertificationABIModel model);
    recognized_certification_symbol_success :
      RuntimeSymbolVerificationSuccess
        (recognizedCertificationSymbolModel model);
    recognized_certification_artifact_success :
      verifyArtifactAuthority
        (recognizedCertificationArtifactAuthority model) = GateAccepted;
    recognized_certification_scope_closure :
      CertificationClosure (recognizedCertificationScopeModel model);
    recognized_certification_revision_in_scope :
      certificationScope
        (recognizedCertificationScopeModel model)
        (recognizedCertificationRevision model) = true;
    recognized_certification_translation_success :
      recognizedCertificationTranslationAccepted model = true;
    recognized_certification_llvm18_success :
      recognizedCertificationLLVM18Accepted model = true
  }.

Theorem recognized_record_certification_requires_all_semantic_authorities :
  forall model,
    RecognizedRecordCertificationSuccess model ->
    RecognizedRecordVerificationSuccess
      (recognizedCertificationSystemsModel model) /\
    RecognizedRecordABIVerificationSuccess
      (recognizedCertificationABIModel model) /\
    RuntimeSymbolVerificationSuccess
      (recognizedCertificationSymbolModel model).
Proof.
  intros model H.
  repeat split.
  - exact (recognized_certification_systems_success model H).
  - exact (recognized_certification_abi_success model H).
  - exact (recognized_certification_symbol_success model H).
Qed.

Theorem recognized_record_certification_requires_exact_artifact_authority :
  forall model,
    RecognizedRecordCertificationSuccess model ->
    artifactDeclared (recognizedCertificationArtifactAuthority model) = true /\
    artifactIdentityMatches (recognizedCertificationArtifactAuthority model) = true /\
    artifactDigestMatchesTrustedAvailability
      (recognizedCertificationArtifactAuthority model) = true.
Proof.
  intros model H.
  exact
    (successful_artifact_authority_is_exact
      (recognizedCertificationArtifactAuthority model)
      (recognized_certification_artifact_success model H)).
Qed.

Theorem recognized_record_certification_requires_closed_scope :
  forall model,
    RecognizedRecordCertificationSuccess model ->
    revisionDisposition
      (recognizedCertificationScopeModel model)
      (recognizedCertificationRevision model) = LocallyAccepted.
Proof.
  intros model H.
  exact
    (in_scope_revision_is_locally_accepted
      (recognizedCertificationScopeModel model)
      (recognizedCertificationRevision model)
      (recognized_certification_scope_closure model H)
      (recognized_certification_revision_in_scope model H)).
Qed.

Theorem recognized_record_certification_requires_translation_and_external_llvm_gate :
  forall model,
    RecognizedRecordCertificationSuccess model ->
    recognizedCertificationTranslationAccepted model = true /\
    recognizedCertificationLLVM18Accepted model = true.
Proof.
  intros model H.
  split.
  - exact (recognized_certification_translation_success model H).
  - exact (recognized_certification_llvm18_success model H).
Qed.

Theorem recognized_record_certification_cannot_succeed_without_systems_proof :
  forall model,
    ~ RecognizedRecordVerificationSuccess
      (recognizedCertificationSystemsModel model) ->
    ~ RecognizedRecordCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (recognized_certification_systems_success model H).
Qed.

Theorem recognized_record_certification_cannot_succeed_without_abi_proof :
  forall model,
    ~ RecognizedRecordABIVerificationSuccess
      (recognizedCertificationABIModel model) ->
    ~ RecognizedRecordCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (recognized_certification_abi_success model H).
Qed.

Theorem recognized_record_certification_cannot_succeed_without_symbol_proof :
  forall model,
    ~ RuntimeSymbolVerificationSuccess
      (recognizedCertificationSymbolModel model) ->
    ~ RecognizedRecordCertificationSuccess model.
Proof.
  intros model Hmissing H.
  apply Hmissing.
  exact (recognized_certification_symbol_success model H).
Qed.

Theorem recognized_record_certification_cannot_succeed_without_llvm18_acceptance :
  forall model,
    recognizedCertificationLLVM18Accepted model = false ->
    ~ RecognizedRecordCertificationSuccess model.
Proof.
  intros model Hrejected H.
  rewrite (recognized_certification_llvm18_success model H) in Hrejected.
  discriminate.
Qed.
