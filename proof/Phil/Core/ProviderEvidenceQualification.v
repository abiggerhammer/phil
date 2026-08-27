From Stdlib Require Import Lists.List.
Import ListNotations.

From Phil.Core Require Import ProviderQualification.

(*
  PHIL-PROV-EVIDENCE-001 — bounded PROV-010 evidence-producer competence.

  The normalized model keeps temporary observation identity separate from the
  stable semantic subject carried by persistent evidence.  Exact proposition
  family/parameters, exact stable subject, exact validity contract, and an
  admissible observation-to-subject mapping are all required independently.
*)

Definition ProviderPropositionFamilyKey := nat.
Definition ProviderEvidenceSubjectKey := nat.
Definition ProviderObservationKey := nat.
Definition EvidenceSubjectMappingRevision := nat.
Definition EvidenceValidityContractKey := nat.
Definition ProviderEvidenceScopeKey := nat.
Definition ProviderEvidenceParameter := nat.
Definition RuntimeCoincidenceReason := nat.

Inductive ProviderEvidenceObservation : Type :=
| StableEvidenceObservation :
    ProviderEvidenceSubjectKey -> ProviderEvidenceObservation
| ScopedBorrowEvidenceObservation :
    ProviderObservationKey ->
    ProviderEvidenceScopeKey ->
    ProviderEvidenceObservation
| OpaqueEvidenceObservation :
    ProviderObservationKey -> ProviderEvidenceObservation.

Inductive EvidenceSubjectMapping : Type :=
| DirectStableEvidenceSubject :
    ProviderEvidenceSubjectKey -> EvidenceSubjectMapping
| CheckedObservationToStableSubject :
    EvidenceSubjectMappingRevision ->
    ProviderEvidenceObservation ->
    ProviderEvidenceSubjectKey ->
    EvidenceSubjectMapping
| RuntimeCoincidenceSubjectMapping :
    RuntimeCoincidenceReason -> EvidenceSubjectMapping.

Record ProviderEvidenceProducerRequirement : Type :=
  mkProviderEvidenceProducerRequirement {
    requiredEvidenceOperation : ProviderOperationKey;
    requiredEvidenceFamily : ProviderPropositionFamilyKey;
    requiredEvidenceParameters : list ProviderEvidenceParameter;
    requiredEvidenceStableSubject : ProviderEvidenceSubjectKey;
    requiredEvidenceValidity : EvidenceValidityContractKey
  }.

Record ProviderEvidenceProducerCompetenceClaim : Type :=
  mkProviderEvidenceProducerCompetenceClaim {
    claimedEvidenceOperation : ProviderOperationKey;
    claimedEvidenceFamily : ProviderPropositionFamilyKey;
    claimedEvidenceParameters : list ProviderEvidenceParameter;
    claimedEvidenceObservation : ProviderEvidenceObservation;
    claimedEvidencePropositionSubject : ProviderEvidenceSubjectKey;
    claimedEvidenceSubjectMapping : EvidenceSubjectMapping;
    claimedEvidenceValidity : EvidenceValidityContractKey
  }.

Definition EvidenceSubjectMappingAdmissible
  (observation : ProviderEvidenceObservation)
  (subject : ProviderEvidenceSubjectKey)
  (mapping : EvidenceSubjectMapping) : Prop :=
  match mapping with
  | DirectStableEvidenceSubject mappedSubject =>
      observation = StableEvidenceObservation mappedSubject /\
      mappedSubject = subject
  | CheckedObservationToStableSubject _ mappedObservation mappedSubject =>
      mappedObservation = observation /\
      mappedSubject = subject
  | RuntimeCoincidenceSubjectMapping _ => False
  end.

Definition ProviderEvidenceProducerCompetent
  (contract : ProviderContract)
  (implementation : ProviderImplementation)
  (providerClaim : ProviderQualificationClaim)
  (requirement : ProviderEvidenceProducerRequirement)
  (claim : ProviderEvidenceProducerCompetenceClaim) : Prop :=
  ProviderQualifies contract implementation providerClaim /\
  (exists operationContract,
    providerOperations contract (requiredEvidenceOperation requirement) =
      Some operationContract) /\
  claimedEvidenceOperation claim = requiredEvidenceOperation requirement /\
  claimedEvidenceFamily claim = requiredEvidenceFamily requirement /\
  claimedEvidenceParameters claim = requiredEvidenceParameters requirement /\
  claimedEvidencePropositionSubject claim =
    requiredEvidenceStableSubject requirement /\
  claimedEvidenceValidity claim = requiredEvidenceValidity requirement /\
  EvidenceSubjectMappingAdmissible
    (claimedEvidenceObservation claim)
    (claimedEvidencePropositionSubject claim)
    (claimedEvidenceSubjectMapping claim).

Definition ProviderEvidenceProposition : Type :=
  (ProviderPropositionFamilyKey *
    (list ProviderEvidenceParameter * ProviderEvidenceSubjectKey))%type.

Definition instantiateProviderEvidenceProposition
  (family : ProviderPropositionFamilyKey)
  (parameters : list ProviderEvidenceParameter)
  (subject : ProviderEvidenceSubjectKey) : ProviderEvidenceProposition :=
  (family, (parameters, subject)).

Theorem competent_evidence_operation_has_explicit_provider_correspondence :
  forall contract implementation providerClaim requirement claim,
    ProviderEvidenceProducerCompetent
      contract implementation providerClaim requirement claim ->
    exists operationContract correspondence implementationOperation,
      providerOperations contract (requiredEvidenceOperation requirement) =
        Some operationContract /\
      claimCorrespondences providerClaim (requiredEvidenceOperation requirement) =
        Some correspondence /\
      providerEntries implementation (correspondenceEntry correspondence) =
        Some implementationOperation /\
      ProviderOperationQualifies
        operationContract implementationOperation correspondence.
Proof.
  intros contract implementation providerClaim requirement claim Hcompetent.
  destruct Hcompetent as [Hprovider [Hpresent _]].
  destruct Hpresent as [operationContract Hoperation].
  destruct (every_public_operation_has_explicit_correspondence
    contract implementation providerClaim
    (requiredEvidenceOperation requirement) operationContract
    Hprovider Hoperation)
    as [correspondence [implementationOperation
      [Hcorrespondence [Hentry Hqualified]]]].
  exists operationContract, correspondence, implementationOperation.
  repeat split; assumption.
Qed.

Theorem competence_requires_exact_evidence_operation :
  forall contract implementation providerClaim requirement claim,
    ProviderEvidenceProducerCompetent
      contract implementation providerClaim requirement claim ->
    claimedEvidenceOperation claim = requiredEvidenceOperation requirement.
Proof.
  intros contract implementation providerClaim requirement claim Hcompetent.
  destruct Hcompetent as [_ [_ [Hoperation _]]].
  exact Hoperation.
Qed.

Theorem competence_requires_exact_proposition_family :
  forall contract implementation providerClaim requirement claim,
    ProviderEvidenceProducerCompetent
      contract implementation providerClaim requirement claim ->
    claimedEvidenceFamily claim = requiredEvidenceFamily requirement.
Proof.
  intros contract implementation providerClaim requirement claim Hcompetent.
  destruct Hcompetent as [_ [_ [_ [Hfamily _]]]].
  exact Hfamily.
Qed.

Theorem competence_requires_exact_proposition_parameters :
  forall contract implementation providerClaim requirement claim,
    ProviderEvidenceProducerCompetent
      contract implementation providerClaim requirement claim ->
    claimedEvidenceParameters claim = requiredEvidenceParameters requirement.
Proof.
  intros contract implementation providerClaim requirement claim Hcompetent.
  destruct Hcompetent as [_ [_ [_ [_ [Hparameters _]]]]].
  exact Hparameters.
Qed.

Theorem competence_requires_exact_stable_subject :
  forall contract implementation providerClaim requirement claim,
    ProviderEvidenceProducerCompetent
      contract implementation providerClaim requirement claim ->
    claimedEvidencePropositionSubject claim =
      requiredEvidenceStableSubject requirement.
Proof.
  intros contract implementation providerClaim requirement claim Hcompetent.
  destruct Hcompetent as [_ [_ [_ [_ [_ [Hsubject _]]]]]].
  exact Hsubject.
Qed.

Theorem competence_requires_exact_validity_contract :
  forall contract implementation providerClaim requirement claim,
    ProviderEvidenceProducerCompetent
      contract implementation providerClaim requirement claim ->
    claimedEvidenceValidity claim = requiredEvidenceValidity requirement.
Proof.
  intros contract implementation providerClaim requirement claim Hcompetent.
  destruct Hcompetent as [_ [_ [_ [_ [_ [_ [Hvalidity _]]]]]]].
  exact Hvalidity.
Qed.

Theorem direct_mapping_requires_exact_stable_observation :
  forall observation subject mappedSubject,
    EvidenceSubjectMappingAdmissible
      observation subject (DirectStableEvidenceSubject mappedSubject) ->
    observation = StableEvidenceObservation mappedSubject /\
    mappedSubject = subject.
Proof.
  intros observation subject mappedSubject Hadmissible.
  exact Hadmissible.
Qed.

Theorem scoped_borrow_cannot_use_direct_stable_mapping :
  forall observationKey scopeKey subject mappedSubject,
    ~ EvidenceSubjectMappingAdmissible
        (ScopedBorrowEvidenceObservation observationKey scopeKey)
        subject
        (DirectStableEvidenceSubject mappedSubject).
Proof.
  intros observationKey scopeKey subject mappedSubject Hadmissible.
  destruct Hadmissible as [Hobservation _].
  discriminate.
Qed.

Theorem checked_mapping_binds_exact_observation :
  forall observation subject revision mappedObservation mappedSubject,
    EvidenceSubjectMappingAdmissible
      observation subject
      (CheckedObservationToStableSubject
        revision mappedObservation mappedSubject) ->
    mappedObservation = observation.
Proof.
  intros observation subject revision mappedObservation mappedSubject Hadmissible.
  exact (proj1 Hadmissible).
Qed.

Theorem checked_mapping_binds_exact_stable_subject :
  forall observation subject revision mappedObservation mappedSubject,
    EvidenceSubjectMappingAdmissible
      observation subject
      (CheckedObservationToStableSubject
        revision mappedObservation mappedSubject) ->
    mappedSubject = subject.
Proof.
  intros observation subject revision mappedObservation mappedSubject Hadmissible.
  exact (proj2 Hadmissible).
Qed.

Theorem runtime_coincidence_never_establishes_subject_competence :
  forall observation subject reason,
    ~ EvidenceSubjectMappingAdmissible
        observation subject (RuntimeCoincidenceSubjectMapping reason).
Proof.
  intros observation subject reason Hadmissible.
  exact Hadmissible.
Qed.

Theorem mismatched_stable_subject_rejects_competence :
  forall contract implementation providerClaim requirement claim,
    claimedEvidencePropositionSubject claim <>
      requiredEvidenceStableSubject requirement ->
    ~ ProviderEvidenceProducerCompetent
        contract implementation providerClaim requirement claim.
Proof.
  intros contract implementation providerClaim requirement claim Hmismatch Hcompetent.
  apply Hmismatch.
  eapply competence_requires_exact_stable_subject.
  exact Hcompetent.
Qed.

Theorem competent_claim_materializes_exact_required_proposition :
  forall contract implementation providerClaim requirement claim,
    ProviderEvidenceProducerCompetent
      contract implementation providerClaim requirement claim ->
    instantiateProviderEvidenceProposition
      (claimedEvidenceFamily claim)
      (claimedEvidenceParameters claim)
      (claimedEvidencePropositionSubject claim) =
    instantiateProviderEvidenceProposition
      (requiredEvidenceFamily requirement)
      (requiredEvidenceParameters requirement)
      (requiredEvidenceStableSubject requirement).
Proof.
  intros contract implementation providerClaim requirement claim Hcompetent.
  rewrite (competence_requires_exact_proposition_family
    contract implementation providerClaim requirement claim Hcompetent).
  rewrite (competence_requires_exact_proposition_parameters
    contract implementation providerClaim requirement claim Hcompetent).
  rewrite (competence_requires_exact_stable_subject
    contract implementation providerClaim requirement claim Hcompetent).
  reflexivity.
Qed.

Theorem temporary_observation_identity_is_nonsemantic_to_proposition :
  forall family parameters subject firstObservation secondObservation,
    instantiateProviderEvidenceProposition family parameters subject =
    instantiateProviderEvidenceProposition family parameters subject.
Proof.
  intros family parameters subject firstObservation secondObservation.
  reflexivity.
Qed.

Theorem competent_evidence_retains_exact_provider_lineage :
  forall contract implementation providerClaim requirement claim,
    ProviderEvidenceProducerCompetent
      contract implementation providerClaim requirement claim ->
    claimRequiredInterface providerClaim = providerInterfaceRevision contract /\
    claimImplementationRevision providerClaim =
      providerDefinitionRevision implementation.
Proof.
  intros contract implementation providerClaim requirement claim Hcompetent.
  destruct Hcompetent as [Hprovider _].
  split.
  - eapply qualified_provider_has_exact_contract_revision.
    exact Hprovider.
  - eapply qualified_provider_has_exact_implementation_revision.
    exact Hprovider.
Qed.
