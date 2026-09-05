From Stdlib Require Import Bool.Bool Setoids.Setoid.

From Phil.Core Require Import SteveProviderQualificationWitness.

(*
  Machine-facing decision surface for PHIL-PROV-STEVE-WITNESS-001.

  This is deliberately a bounded witness-correspondence gate.  It groups the
  nineteen Certified theorem consequences into eleven reflected facts matching
  the existing PROV-016 pressure corpus.  It does not claim SHA-256
  cryptographic correctness, filesystem/object-store truth, completeness of the
  BlobProvider state/law/lifecycle model, or full ArchitectureRealization /
  Systems / StageContract integration.
*)

Definition BothSteveProvidersAdmitted
  (witness : SteveProviderQualificationWitness) : Prop :=
  artifactAdmitted (digestArtifact (steveDigestWitness witness)) = true /\
  artifactAdmitted (blobArtifact (steveBlobWitness witness)) = true.

Definition DigestStableSubjectExact
  (witness : SteveProviderQualificationWitness) : Prop :=
  digestPropositionSubject (steveDigestWitness witness) =
    digestCheckedSubject (steveDigestWitness witness).

Definition DigestObservationMappingValid
  (witness : SteveProviderQualificationWitness) : Prop :=
  digestObservationMappingChecked (steveDigestWitness witness) = true.

Definition DigestCandidateBorrowPreserved
  (witness : SteveProviderQualificationWitness) : Prop :=
  BorrowPreserved
    (digestCandidateResource (steveDigestWitness witness))
    (digestComputeResidue (steveDigestWitness witness)).

Definition BlobCandidateBorrowPreservedAllOutcomes
  (witness : SteveProviderQualificationWitness) : Prop :=
  forall outcome,
    BorrowPreserved
      (blobCandidateResource (steveBlobWitness witness))
      (blobInstallResidue (steveBlobWitness witness) outcome).

Definition BlobWholeProviderLayersPresent
  (witness : SteveProviderQualificationWitness) : Prop :=
  blobHasStateQualification (steveBlobWitness witness) = true /\
  blobHasNoReplaceLaw (steveBlobWitness witness) = true /\
  blobHasLifecycleQualification (steveBlobWitness witness) = true /\
  blobHasAuthorityQualification (steveBlobWitness witness) = true.

Definition BlobNoReplaceEnforced : Prop :=
  NoReplaceAcceptsTwoInstalled = false.

Definition BlobPartialPublicationForbidden : Prop :=
  ClientVisibleStateAllowed ObjectPartiallyCommitted = false.

Definition BlobAuthorityExplicitlyDispositioned
  (witness : SteveProviderQualificationWitness) : Prop :=
  blobOverwriteAuthorityExtra (steveBlobWitness witness) = true /\
  blobOverwriteAuthorityDispositioned (steveBlobWitness witness) = true /\
  blobDeleteAuthorityExtra (steveBlobWitness witness) = true /\
  blobDeleteAuthorityDispositioned (steveBlobWitness witness) = true.

Definition SteveObligationManifestsExact
  (witness : SteveProviderQualificationWitness) : Prop :=
  (forall key,
    artifactRequiredObligation
      (digestArtifact (steveDigestWitness witness)) key =
    artifactEvidenceDisposition
      (digestArtifact (steveDigestWitness witness)) key) /\
  (forall key,
    artifactRequiredObligation
      (blobArtifact (steveBlobWitness witness)) key =
    artifactEvidenceDisposition
      (blobArtifact (steveBlobWitness witness)) key).

Definition SteveConditionsRemainExplicit
  (witness : SteveProviderQualificationWitness) : Prop :=
  (forall condition,
    artifactClaimCondition
      (digestArtifact (steveDigestWitness witness)) condition =
    artifactEvidenceAssumption
      (digestArtifact (steveDigestWitness witness)) condition) /\
  (forall condition,
    artifactClaimCondition
      (digestArtifact (steveDigestWitness witness)) condition =
    artifactAdmissionDisposition
      (digestArtifact (steveDigestWitness witness)) condition) /\
  (forall condition,
    artifactClaimCondition
      (blobArtifact (steveBlobWitness witness)) condition =
    artifactEvidenceAssumption
      (blobArtifact (steveBlobWitness witness)) condition) /\
  (forall condition,
    artifactClaimCondition
      (blobArtifact (steveBlobWitness witness)) condition =
    artifactAdmissionDisposition
      (blobArtifact (steveBlobWitness witness)) condition) /\
  artifactClaimCondition
    (digestArtifact (steveDigestWitness witness))
    (digestSha256ProfileCondition (steveDigestWitness witness)) = true /\
  artifactEvidenceAssumption
    (digestArtifact (steveDigestWitness witness))
    (digestSha256ProfileCondition (steveDigestWitness witness)) = true /\
  artifactAdmissionDisposition
    (digestArtifact (steveDigestWitness witness))
    (digestSha256ProfileCondition (steveDigestWitness witness)) = true.

Definition SteveProviderQualificationWitnessBoundary
  (witness : SteveProviderQualificationWitness) : Prop :=
  BothSteveProvidersAdmitted witness /\
  DigestStableSubjectExact witness /\
  DigestObservationMappingValid witness /\
  DigestCandidateBorrowPreserved witness /\
  BlobCandidateBorrowPreservedAllOutcomes witness /\
  BlobWholeProviderLayersPresent witness /\
  BlobNoReplaceEnforced /\
  BlobPartialPublicationForbidden /\
  BlobAuthorityExplicitlyDispositioned witness /\
  SteveObligationManifestsExact witness /\
  SteveConditionsRemainExplicit witness.

Theorem steve_provider_qualification_witness_boundary_certified :
  forall witness,
    SteveProviderQualificationWitnessBoundary witness.
Proof.
  intros witness.
  unfold SteveProviderQualificationWitnessBoundary.
  split.
  - apply both_steve_providers_are_admitted.
  - split.
    + apply digest_matches_retains_stable_owner_subject.
    + split.
      * apply digest_scoped_borrow_maps_to_stable_subject.
      * split.
        -- apply digest_candidate_bytes_remain_borrowed.
        -- split.
           ++ intros outcome.
              destruct outcome.
              ** apply blob_installed_outcome_preserves_candidate_borrow.
              ** apply blob_already_exists_outcome_preserves_candidate_borrow.
              ** apply blob_storage_failure_outcome_preserves_candidate_borrow.
           ++ split.
              ** apply blob_whole_provider_layers_are_present.
              ** split.
                 --- apply blob_second_installed_event_violates_no_replace.
                 --- split.
                     +++ apply blob_partial_publication_is_forbidden.
                     +++ split.
                         *** unfold BlobAuthorityExplicitlyDispositioned.
                             pose proof
                               (blob_overwrite_authority_is_explicitly_dispositioned witness)
                               as Hoverwrite.
                             pose proof
                               (blob_delete_authority_is_explicitly_dispositioned witness)
                               as Hdelete.
                             destruct Hoverwrite as
                               [HoverwriteExtra HoverwriteDisposition].
                             destruct Hdelete as
                               [HdeleteExtra HdeleteDisposition].
                             repeat split; assumption.
                         *** split.
                             ---- unfold SteveObligationManifestsExact.
                                  split.
                                  ++++ intros key.
                                       apply digest_obligation_manifest_closes_exactly.
                                  ++++ intros key.
                                       apply blob_obligation_manifest_closes_exactly.
                             ---- unfold SteveConditionsRemainExplicit.
                                  repeat split.
                                  ++++ intros condition.
                                       apply digest_conditions_remain_explicit_in_evidence.
                                  ++++ intros condition.
                                       apply digest_conditions_remain_explicit_in_admission.
                                  ++++ intros condition.
                                       apply blob_conditions_remain_explicit_in_evidence.
                                  ++++ intros condition.
                                       apply blob_conditions_remain_explicit_in_admission.
                                  ++++ pose proof
                                       (digest_sha256_profile_remains_an_explicit_condition witness)
                                       as Hsha.
                                       destruct Hsha as
                                         [Hclaim [Hevidence Hadmission]].
                                       exact Hclaim.
                                  ++++ pose proof
                                       (digest_sha256_profile_remains_an_explicit_condition witness)
                                       as Hsha.
                                       destruct Hsha as
                                         [Hclaim [Hevidence Hadmission]].
                                       exact Hevidence.
                                  ++++ pose proof
                                       (digest_sha256_profile_remains_an_explicit_condition witness)
                                       as Hsha.
                                       destruct Hsha as
                                         [Hclaim [Hevidence Hadmission]].
                                       exact Hadmission.
Qed.

Definition decideSteveProviderQualificationWitnessByFacts
  (bothAdmitted
   digestSubjectExact
   digestObservationMapped
   digestBorrowPreserved
   blobBorrowAllOutcomes
   blobWholeLayersPresent
   noReplaceEnforced
   partialPublicationForbidden
   blobAuthorityDispositioned
   obligationManifestsExact
   conditionsExplicit : bool) : bool :=
  andb bothAdmitted
    (andb digestSubjectExact
      (andb digestObservationMapped
        (andb digestBorrowPreserved
          (andb blobBorrowAllOutcomes
            (andb blobWholeLayersPresent
              (andb noReplaceEnforced
                (andb partialPublicationForbidden
                  (andb blobAuthorityDispositioned
                    (andb obligationManifestsExact
                      conditionsExplicit)))))))))).

Theorem decideSteveProviderQualificationWitnessByFacts_classifies :
  forall witness
    bothAdmitted
    digestSubjectExact
    digestObservationMapped
    digestBorrowPreserved
    blobBorrowAllOutcomes
    blobWholeLayersPresent
    noReplaceEnforced
    partialPublicationForbidden
    blobAuthorityDispositioned
    obligationManifestsExact
    conditionsExplicit,
    (bothAdmitted = true <-> BothSteveProvidersAdmitted witness) ->
    (digestSubjectExact = true <-> DigestStableSubjectExact witness) ->
    (digestObservationMapped = true <-> DigestObservationMappingValid witness) ->
    (digestBorrowPreserved = true <-> DigestCandidateBorrowPreserved witness) ->
    (blobBorrowAllOutcomes = true <->
      BlobCandidateBorrowPreservedAllOutcomes witness) ->
    (blobWholeLayersPresent = true <-> BlobWholeProviderLayersPresent witness) ->
    (noReplaceEnforced = true <-> BlobNoReplaceEnforced) ->
    (partialPublicationForbidden = true <-> BlobPartialPublicationForbidden) ->
    (blobAuthorityDispositioned = true <->
      BlobAuthorityExplicitlyDispositioned witness) ->
    (obligationManifestsExact = true <-> SteveObligationManifestsExact witness) ->
    (conditionsExplicit = true <-> SteveConditionsRemainExplicit witness) ->
    decideSteveProviderQualificationWitnessByFacts
      bothAdmitted
      digestSubjectExact
      digestObservationMapped
      digestBorrowPreserved
      blobBorrowAllOutcomes
      blobWholeLayersPresent
      noReplaceEnforced
      partialPublicationForbidden
      blobAuthorityDispositioned
      obligationManifestsExact
      conditionsExplicit = true <->
    SteveProviderQualificationWitnessBoundary witness.
Proof.
  intros witness
    bothAdmitted
    digestSubjectExact
    digestObservationMapped
    digestBorrowPreserved
    blobBorrowAllOutcomes
    blobWholeLayersPresent
    noReplaceEnforced
    partialPublicationForbidden
    blobAuthorityDispositioned
    obligationManifestsExact
    conditionsExplicit
    Hboth
    HdigestSubject
    HdigestObservation
    HdigestBorrow
    HblobBorrow
    HblobLayers
    HnoReplace
    Hpartial
    Hauthority
    Hobligations
    Hconditions.
  unfold decideSteveProviderQualificationWitnessByFacts.
  repeat rewrite andb_true_iff.
  rewrite Hboth,
    HdigestSubject,
    HdigestObservation,
    HdigestBorrow,
    HblobBorrow,
    HblobLayers,
    HnoReplace,
    Hpartial,
    Hauthority,
    Hobligations,
    Hconditions.
  reflexivity.
Qed.
