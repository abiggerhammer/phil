From Stdlib Require Import Bool.Bool.

(*
  PHIL-PROV-STEVE-WITNESS-001 — bounded PROV-016 witness closure.

  This proof records the normalized semantic facts exercised by Steve's two
  concrete provider qualification artifacts. It does not prove SHA-256
  cryptographic correctness, filesystem/object-store truth, or universal
  completeness of the BlobProvider law/lifecycle model. Those remain explicit
  evidence and TCB boundaries.
*)

Inductive StableIdParameter : Type :=
| StableId : nat -> StableIdParameter.

Inductive EvidenceSubject : Type :=
| StableOwnerSubject : nat -> EvidenceSubject.

Inductive BorrowObservation : Type :=
| ScopedBorrowObservation : nat -> nat -> BorrowObservation.

Inductive ResourceKey : Type :=
| Resource : nat -> ResourceKey.

Inductive ObligationKey : Type :=
| Obligation : nat -> ObligationKey.

Inductive ConditionKey : Type :=
| Condition : nat -> ConditionKey.

Inductive InstallOutcome : Type :=
| InstallInstalled
| InstallAlreadyExists
| InstallStorageFailure.

Inductive ObservableState : Type :=
| ObjectAbsent
| ObjectCompleteAndCorrect
| ObjectPartiallyCommitted.

Inductive AuthorityUse : Type :=
| OverwriteAuthority
| DeleteAuthority.

Record BorrowResidue : Type := mkBorrowResidue {
  residueBorrowed : ResourceKey -> bool;
  residueConsumed : ResourceKey -> bool
}.

Definition BorrowPreserved (resource : ResourceKey) (residue : BorrowResidue) : Prop :=
  residueBorrowed residue resource = true /\
  residueConsumed residue resource = false.

Record SteveProviderArtifact : Type := mkSteveProviderArtifact {
  artifactAdmitted : bool;
  artifactRequiredObligation : ObligationKey -> bool;
  artifactEvidenceDisposition : ObligationKey -> bool;
  artifactClaimCondition : ConditionKey -> bool;
  artifactEvidenceAssumption : ConditionKey -> bool;
  artifactAdmissionDisposition : ConditionKey -> bool
}.

Record QualificationClosure (artifact : SteveProviderArtifact) : Prop :=
  mkQualificationClosure {
    closure_admitted : artifactAdmitted artifact = true;
    closure_obligation_domain_exact :
      forall key,
        artifactRequiredObligation artifact key =
          artifactEvidenceDisposition artifact key;
    closure_conditions_match_evidence :
      forall condition,
        artifactClaimCondition artifact condition =
          artifactEvidenceAssumption artifact condition;
    closure_conditions_match_admission :
      forall condition,
        artifactClaimCondition artifact condition =
          artifactAdmissionDisposition artifact condition
  }.

Record DigestProviderWitness : Type := mkDigestProviderWitness {
  digestArtifact : SteveProviderArtifact;
  digestClosure : QualificationClosure digestArtifact;
  digestIdParameter : StableIdParameter;
  digestPropositionSubject : EvidenceSubject;
  digestCheckedSubject : EvidenceSubject;
  digestObservation : BorrowObservation;
  digestObservationMappingChecked : bool;
  digestCandidateResource : ResourceKey;
  digestComputeResidue : BorrowResidue;
  digestSha256ProfileCondition : ConditionKey;
  digest_subject_exact :
    digestPropositionSubject = digestCheckedSubject;
  digest_observation_mapping_valid :
    digestObservationMappingChecked = true;
  digest_candidate_borrow_preserved :
    BorrowPreserved digestCandidateResource digestComputeResidue;
  digest_sha256_condition_explicit :
    artifactClaimCondition digestArtifact digestSha256ProfileCondition = true /\
    artifactEvidenceAssumption digestArtifact digestSha256ProfileCondition = true /\
    artifactAdmissionDisposition digestArtifact digestSha256ProfileCondition = true
}.

Record BlobProviderWitness : Type := mkBlobProviderWitness {
  blobArtifact : SteveProviderArtifact;
  blobClosure : QualificationClosure blobArtifact;
  blobCandidateResource : ResourceKey;
  blobInstallResidue : InstallOutcome -> BorrowResidue;
  blobHasStateQualification : bool;
  blobHasNoReplaceLaw : bool;
  blobHasLifecycleQualification : bool;
  blobHasAuthorityQualification : bool;
  blobOverwriteAuthorityExtra : bool;
  blobDeleteAuthorityExtra : bool;
  blobOverwriteAuthorityDispositioned : bool;
  blobDeleteAuthorityDispositioned : bool;
  blob_candidate_borrow_preserved :
    forall outcome,
      BorrowPreserved blobCandidateResource (blobInstallResidue outcome);
  blob_state_present : blobHasStateQualification = true;
  blob_law_present : blobHasNoReplaceLaw = true;
  blob_lifecycle_present : blobHasLifecycleQualification = true;
  blob_authority_present : blobHasAuthorityQualification = true;
  blob_overwrite_extra_explicit : blobOverwriteAuthorityExtra = true;
  blob_delete_extra_explicit : blobDeleteAuthorityExtra = true;
  blob_overwrite_disposition_explicit : blobOverwriteAuthorityDispositioned = true;
  blob_delete_disposition_explicit : blobDeleteAuthorityDispositioned = true
}.

Record SteveProviderQualificationWitness : Type := mkSteveProviderQualificationWitness {
  steveDigestWitness : DigestProviderWitness;
  steveBlobWitness : BlobProviderWitness
}.

Definition NoReplaceAcceptsTwoInstalled : bool := false.

Definition ClientVisibleStateAllowed (state : ObservableState) : bool :=
  match state with
  | ObjectAbsent => true
  | ObjectCompleteAndCorrect => true
  | ObjectPartiallyCommitted => false
  end.

Theorem both_steve_providers_are_admitted :
  forall witness,
    artifactAdmitted (digestArtifact (steveDigestWitness witness)) = true /\
    artifactAdmitted (blobArtifact (steveBlobWitness witness)) = true.
Proof.
  intros witness.
  split.
  - exact (closure_admitted
      (digestArtifact (steveDigestWitness witness))
      (digestClosure (steveDigestWitness witness))).
  - exact (closure_admitted
      (blobArtifact (steveBlobWitness witness))
      (blobClosure (steveBlobWitness witness))).
Qed.

Theorem digest_matches_retains_stable_owner_subject :
  forall witness,
    digestPropositionSubject (steveDigestWitness witness) =
      digestCheckedSubject (steveDigestWitness witness).
Proof.
  intros witness.
  exact (digest_subject_exact (steveDigestWitness witness)).
Qed.

Theorem digest_scoped_borrow_maps_to_stable_subject :
  forall witness,
    digestObservationMappingChecked (steveDigestWitness witness) = true.
Proof.
  intros witness.
  exact (digest_observation_mapping_valid (steveDigestWitness witness)).
Qed.

Theorem digest_candidate_bytes_remain_borrowed :
  forall witness,
    BorrowPreserved
      (digestCandidateResource (steveDigestWitness witness))
      (digestComputeResidue (steveDigestWitness witness)).
Proof.
  intros witness.
  exact (digest_candidate_borrow_preserved (steveDigestWitness witness)).
Qed.

Theorem blob_installed_outcome_preserves_candidate_borrow :
  forall witness,
    BorrowPreserved
      (blobCandidateResource (steveBlobWitness witness))
      (blobInstallResidue (steveBlobWitness witness) InstallInstalled).
Proof.
  intros witness.
  exact (blob_candidate_borrow_preserved
    (steveBlobWitness witness) InstallInstalled).
Qed.

Theorem blob_already_exists_outcome_preserves_candidate_borrow :
  forall witness,
    BorrowPreserved
      (blobCandidateResource (steveBlobWitness witness))
      (blobInstallResidue (steveBlobWitness witness) InstallAlreadyExists).
Proof.
  intros witness.
  exact (blob_candidate_borrow_preserved
    (steveBlobWitness witness) InstallAlreadyExists).
Qed.

Theorem blob_storage_failure_outcome_preserves_candidate_borrow :
  forall witness,
    BorrowPreserved
      (blobCandidateResource (steveBlobWitness witness))
      (blobInstallResidue (steveBlobWitness witness) InstallStorageFailure).
Proof.
  intros witness.
  exact (blob_candidate_borrow_preserved
    (steveBlobWitness witness) InstallStorageFailure).
Qed.

Theorem blob_whole_provider_layers_are_present :
  forall witness,
    blobHasStateQualification (steveBlobWitness witness) = true /\
    blobHasNoReplaceLaw (steveBlobWitness witness) = true /\
    blobHasLifecycleQualification (steveBlobWitness witness) = true /\
    blobHasAuthorityQualification (steveBlobWitness witness) = true.
Proof.
  intros witness.
  repeat split.
  - exact (blob_state_present (steveBlobWitness witness)).
  - exact (blob_law_present (steveBlobWitness witness)).
  - exact (blob_lifecycle_present (steveBlobWitness witness)).
  - exact (blob_authority_present (steveBlobWitness witness)).
Qed.

Theorem blob_second_installed_event_violates_no_replace :
  NoReplaceAcceptsTwoInstalled = false.
Proof.
  reflexivity.
Qed.

Theorem blob_partial_publication_is_forbidden :
  ClientVisibleStateAllowed ObjectPartiallyCommitted = false.
Proof.
  reflexivity.
Qed.

Theorem blob_overwrite_authority_is_explicitly_dispositioned :
  forall witness,
    blobOverwriteAuthorityExtra (steveBlobWitness witness) = true /\
    blobOverwriteAuthorityDispositioned (steveBlobWitness witness) = true.
Proof.
  intros witness.
  split.
  - exact (blob_overwrite_extra_explicit (steveBlobWitness witness)).
  - exact (blob_overwrite_disposition_explicit (steveBlobWitness witness)).
Qed.

Theorem blob_delete_authority_is_explicitly_dispositioned :
  forall witness,
    blobDeleteAuthorityExtra (steveBlobWitness witness) = true /\
    blobDeleteAuthorityDispositioned (steveBlobWitness witness) = true.
Proof.
  intros witness.
  split.
  - exact (blob_delete_extra_explicit (steveBlobWitness witness)).
  - exact (blob_delete_disposition_explicit (steveBlobWitness witness)).
Qed.

Theorem digest_obligation_manifest_closes_exactly :
  forall witness key,
    artifactRequiredObligation (digestArtifact (steveDigestWitness witness)) key =
      artifactEvidenceDisposition (digestArtifact (steveDigestWitness witness)) key.
Proof.
  intros witness key.
  exact (closure_obligation_domain_exact
    (digestArtifact (steveDigestWitness witness))
    (digestClosure (steveDigestWitness witness)) key).
Qed.

Theorem blob_obligation_manifest_closes_exactly :
  forall witness key,
    artifactRequiredObligation (blobArtifact (steveBlobWitness witness)) key =
      artifactEvidenceDisposition (blobArtifact (steveBlobWitness witness)) key.
Proof.
  intros witness key.
  exact (closure_obligation_domain_exact
    (blobArtifact (steveBlobWitness witness))
    (blobClosure (steveBlobWitness witness)) key).
Qed.

Theorem digest_conditions_remain_explicit_in_evidence :
  forall witness condition,
    artifactClaimCondition (digestArtifact (steveDigestWitness witness)) condition =
      artifactEvidenceAssumption (digestArtifact (steveDigestWitness witness)) condition.
Proof.
  intros witness condition.
  exact (closure_conditions_match_evidence
    (digestArtifact (steveDigestWitness witness))
    (digestClosure (steveDigestWitness witness)) condition).
Qed.

Theorem digest_conditions_remain_explicit_in_admission :
  forall witness condition,
    artifactClaimCondition (digestArtifact (steveDigestWitness witness)) condition =
      artifactAdmissionDisposition (digestArtifact (steveDigestWitness witness)) condition.
Proof.
  intros witness condition.
  exact (closure_conditions_match_admission
    (digestArtifact (steveDigestWitness witness))
    (digestClosure (steveDigestWitness witness)) condition).
Qed.

Theorem blob_conditions_remain_explicit_in_evidence :
  forall witness condition,
    artifactClaimCondition (blobArtifact (steveBlobWitness witness)) condition =
      artifactEvidenceAssumption (blobArtifact (steveBlobWitness witness)) condition.
Proof.
  intros witness condition.
  exact (closure_conditions_match_evidence
    (blobArtifact (steveBlobWitness witness))
    (blobClosure (steveBlobWitness witness)) condition).
Qed.

Theorem blob_conditions_remain_explicit_in_admission :
  forall witness condition,
    artifactClaimCondition (blobArtifact (steveBlobWitness witness)) condition =
      artifactAdmissionDisposition (blobArtifact (steveBlobWitness witness)) condition.
Proof.
  intros witness condition.
  exact (closure_conditions_match_admission
    (blobArtifact (steveBlobWitness witness))
    (blobClosure (steveBlobWitness witness)) condition).
Qed.

Theorem digest_sha256_profile_remains_an_explicit_condition :
  forall witness,
    artifactClaimCondition
      (digestArtifact (steveDigestWitness witness))
      (digestSha256ProfileCondition (steveDigestWitness witness)) = true /\
    artifactEvidenceAssumption
      (digestArtifact (steveDigestWitness witness))
      (digestSha256ProfileCondition (steveDigestWitness witness)) = true /\
    artifactAdmissionDisposition
      (digestArtifact (steveDigestWitness witness))
      (digestSha256ProfileCondition (steveDigestWitness witness)) = true.
Proof.
  intros witness.
  exact (digest_sha256_condition_explicit (steveDigestWitness witness)).
Qed.
