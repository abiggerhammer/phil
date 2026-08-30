From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ProviderQualification ProviderEvidenceQualification.

(*
  PHIL-PROV-EVIDENCE-001 — representation-neutral evidence competence decisions.

  Production already receives a CheckedProviderSemanticQualification from the
  Implementation Refined PROV-001–005 checker. It reflects concrete operation
  membership plus exact Text/RefTerm equality into Boolean facts. This layer
  owns the ordered evidence-specific decision over those facts and the three
  Certified EvidenceSubjectMapping cases. Concrete representations and the
  truth of reflected facts remain the native bridge boundary.
*)

Inductive ProviderEvidenceCompetenceDecision : Type :=
| ProviderEvidenceCompetenceAccepted
| ProviderEvidenceOperationNotQualified
| ProviderEvidenceOperationMismatch
| ProviderEvidenceFamilyMismatch
| ProviderEvidenceParametersMismatch
| ProviderEvidenceStableSubjectMismatch
| ProviderEvidenceValidityMismatch.

Definition decideProviderEvidenceCompetenceByFacts
  (operationQualified operationMatches familyMatches parametersMatch
   stableSubjectMatches validityMatches : bool)
  : ProviderEvidenceCompetenceDecision :=
  if operationQualified then
    if operationMatches then
      if familyMatches then
        if parametersMatch then
          if stableSubjectMatches then
            if validityMatches then
              ProviderEvidenceCompetenceAccepted
            else ProviderEvidenceValidityMismatch
          else ProviderEvidenceStableSubjectMismatch
        else ProviderEvidenceParametersMismatch
      else ProviderEvidenceFamilyMismatch
    else ProviderEvidenceOperationMismatch
  else ProviderEvidenceOperationNotQualified.

Inductive ProviderEvidenceMappingDecision : Type :=
| ProviderEvidenceMappingAccepted
| ProviderEvidenceDirectMappingRejected
| ProviderEvidenceCheckedObservationMismatch
| ProviderEvidenceCheckedSubjectMismatch
| ProviderEvidenceRuntimeCoincidenceRejected.

Definition decideDirectEvidenceSubjectMappingByFacts
  (observationIsExactStable mappedSubjectMatches : bool)
  : ProviderEvidenceMappingDecision :=
  if observationIsExactStable then
    if mappedSubjectMatches then
      ProviderEvidenceMappingAccepted
    else ProviderEvidenceDirectMappingRejected
  else ProviderEvidenceDirectMappingRejected.

Definition decideCheckedEvidenceSubjectMappingByFacts
  (observationMatches mappedSubjectMatches : bool)
  : ProviderEvidenceMappingDecision :=
  if observationMatches then
    if mappedSubjectMatches then
      ProviderEvidenceMappingAccepted
    else ProviderEvidenceCheckedSubjectMismatch
  else ProviderEvidenceCheckedObservationMismatch.

Definition decideRuntimeCoincidenceSubjectMapping
  : ProviderEvidenceMappingDecision :=
  ProviderEvidenceRuntimeCoincidenceRejected.

Definition ProviderEvidenceSpecificCompetence
  (contract : ProviderContract)
  (requirement : ProviderEvidenceProducerRequirement)
  (claim : ProviderEvidenceProducerCompetenceClaim) : Prop :=
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

Theorem provider_evidence_competence_decomposes :
  forall contract implementation providerClaim requirement claim,
    ProviderEvidenceProducerCompetent
      contract implementation providerClaim requirement claim <->
    ProviderQualifies contract implementation providerClaim /\
    ProviderEvidenceSpecificCompetence contract requirement claim.
Proof.
  intros contract implementation providerClaim requirement claim.
  unfold ProviderEvidenceProducerCompetent, ProviderEvidenceSpecificCompetence.
  reflexivity.
Qed.

Theorem provider_evidence_all_reflected_prefix_facts_accept :
  decideProviderEvidenceCompetenceByFacts
    true true true true true true =
    ProviderEvidenceCompetenceAccepted.
Proof. reflexivity. Qed.

Theorem provider_evidence_prefix_acceptance_requires_all_reflected_facts :
  forall operationQualified operationMatches familyMatches parametersMatch
         stableSubjectMatches validityMatches,
    decideProviderEvidenceCompetenceByFacts
      operationQualified operationMatches familyMatches parametersMatch
      stableSubjectMatches validityMatches =
      ProviderEvidenceCompetenceAccepted ->
    operationQualified = true /\
    operationMatches = true /\
    familyMatches = true /\
    parametersMatch = true /\
    stableSubjectMatches = true /\
    validityMatches = true.
Proof.
  intros operationQualified operationMatches familyMatches parametersMatch
    stableSubjectMatches validityMatches Haccepted.
  destruct operationQualified; simpl in Haccepted; try discriminate.
  destruct operationMatches; simpl in Haccepted; try discriminate.
  destruct familyMatches; simpl in Haccepted; try discriminate.
  destruct parametersMatch; simpl in Haccepted; try discriminate.
  destruct stableSubjectMatches; simpl in Haccepted; try discriminate.
  destruct validityMatches; simpl in Haccepted; try discriminate.
  repeat split; reflexivity.
Qed.

Theorem provider_evidence_unqualified_operation_has_precedence :
  forall operationMatches familyMatches parametersMatch stableSubjectMatches validityMatches,
    decideProviderEvidenceCompetenceByFacts
      false operationMatches familyMatches parametersMatch stableSubjectMatches validityMatches =
      ProviderEvidenceOperationNotQualified.
Proof. reflexivity. Qed.

Theorem provider_evidence_operation_mismatch_has_precedence :
  forall familyMatches parametersMatch stableSubjectMatches validityMatches,
    decideProviderEvidenceCompetenceByFacts
      true false familyMatches parametersMatch stableSubjectMatches validityMatches =
      ProviderEvidenceOperationMismatch.
Proof. reflexivity. Qed.

Theorem provider_evidence_family_mismatch_has_precedence :
  forall parametersMatch stableSubjectMatches validityMatches,
    decideProviderEvidenceCompetenceByFacts
      true true false parametersMatch stableSubjectMatches validityMatches =
      ProviderEvidenceFamilyMismatch.
Proof. reflexivity. Qed.

Theorem provider_evidence_parameters_mismatch_has_precedence :
  forall stableSubjectMatches validityMatches,
    decideProviderEvidenceCompetenceByFacts
      true true true false stableSubjectMatches validityMatches =
      ProviderEvidenceParametersMismatch.
Proof. reflexivity. Qed.

Theorem provider_evidence_stable_subject_mismatch_has_precedence :
  forall validityMatches,
    decideProviderEvidenceCompetenceByFacts
      true true true true false validityMatches =
      ProviderEvidenceStableSubjectMismatch.
Proof. reflexivity. Qed.

Theorem provider_evidence_validity_mismatch_has_precedence :
  decideProviderEvidenceCompetenceByFacts
    true true true true true false =
    ProviderEvidenceValidityMismatch.
Proof. reflexivity. Qed.

Theorem direct_mapping_all_reflected_facts_accept :
  decideDirectEvidenceSubjectMappingByFacts true true =
    ProviderEvidenceMappingAccepted.
Proof. reflexivity. Qed.

Theorem direct_mapping_acceptance_requires_both_reflected_facts :
  forall observationIsExactStable mappedSubjectMatches,
    decideDirectEvidenceSubjectMappingByFacts
      observationIsExactStable mappedSubjectMatches =
      ProviderEvidenceMappingAccepted ->
    observationIsExactStable = true /\
    mappedSubjectMatches = true.
Proof.
  intros observationIsExactStable mappedSubjectMatches Haccepted.
  destruct observationIsExactStable; simpl in Haccepted; try discriminate.
  destruct mappedSubjectMatches; simpl in Haccepted; try discriminate.
  split; reflexivity.
Qed.

Theorem direct_mapping_observation_failure_rejects :
  forall mappedSubjectMatches,
    decideDirectEvidenceSubjectMappingByFacts false mappedSubjectMatches =
      ProviderEvidenceDirectMappingRejected.
Proof. reflexivity. Qed.

Theorem direct_mapping_subject_failure_rejects :
  decideDirectEvidenceSubjectMappingByFacts true false =
    ProviderEvidenceDirectMappingRejected.
Proof. reflexivity. Qed.

Theorem direct_mapping_decision_sound_complete :
  forall observation subject mappedSubject observationIsExactStable mappedSubjectMatches,
    (observationIsExactStable = true <->
      observation = StableEvidenceObservation mappedSubject) ->
    (mappedSubjectMatches = true <-> mappedSubject = subject) ->
    (decideDirectEvidenceSubjectMappingByFacts
      observationIsExactStable mappedSubjectMatches =
      ProviderEvidenceMappingAccepted <->
     EvidenceSubjectMappingAdmissible
       observation subject (DirectStableEvidenceSubject mappedSubject)).
Proof.
  intros observation subject mappedSubject observationIsExactStable
    mappedSubjectMatches Hobservation Hsubject.
  split.
  - intro Haccepted.
    apply direct_mapping_acceptance_requires_both_reflected_facts in Haccepted.
    destruct Haccepted as [HobservationFact HsubjectFact].
    simpl.
    split.
    + apply (proj1 Hobservation). exact HobservationFact.
    + apply (proj1 Hsubject). exact HsubjectFact.
  - intro Hadmissible.
    simpl in Hadmissible.
    destruct Hadmissible as [HobservationEq HsubjectEq].
    assert (HobservationFact : observationIsExactStable = true).
    { apply (proj2 Hobservation). exact HobservationEq. }
    assert (HsubjectFact : mappedSubjectMatches = true).
    { apply (proj2 Hsubject). exact HsubjectEq. }
    rewrite HobservationFact, HsubjectFact.
    reflexivity.
Qed.

Theorem checked_mapping_all_reflected_facts_accept :
  decideCheckedEvidenceSubjectMappingByFacts true true =
    ProviderEvidenceMappingAccepted.
Proof. reflexivity. Qed.

Theorem checked_mapping_acceptance_requires_both_reflected_facts :
  forall observationMatches mappedSubjectMatches,
    decideCheckedEvidenceSubjectMappingByFacts observationMatches mappedSubjectMatches =
      ProviderEvidenceMappingAccepted ->
    observationMatches = true /\
    mappedSubjectMatches = true.
Proof.
  intros observationMatches mappedSubjectMatches Haccepted.
  destruct observationMatches; simpl in Haccepted; try discriminate.
  destruct mappedSubjectMatches; simpl in Haccepted; try discriminate.
  split; reflexivity.
Qed.

Theorem checked_mapping_observation_failure_has_precedence :
  forall mappedSubjectMatches,
    decideCheckedEvidenceSubjectMappingByFacts false mappedSubjectMatches =
      ProviderEvidenceCheckedObservationMismatch.
Proof. reflexivity. Qed.

Theorem checked_mapping_subject_failure_has_precedence :
  decideCheckedEvidenceSubjectMappingByFacts true false =
    ProviderEvidenceCheckedSubjectMismatch.
Proof. reflexivity. Qed.

Theorem checked_mapping_decision_sound_complete :
  forall observation subject revision mappedObservation mappedSubject
         observationMatches mappedSubjectMatches,
    (observationMatches = true <-> mappedObservation = observation) ->
    (mappedSubjectMatches = true <-> mappedSubject = subject) ->
    (decideCheckedEvidenceSubjectMappingByFacts
      observationMatches mappedSubjectMatches =
      ProviderEvidenceMappingAccepted <->
     EvidenceSubjectMappingAdmissible
       observation subject
       (CheckedObservationToStableSubject
         revision mappedObservation mappedSubject)).
Proof.
  intros observation subject revision mappedObservation mappedSubject
    observationMatches mappedSubjectMatches Hobservation Hsubject.
  split.
  - intro Haccepted.
    apply checked_mapping_acceptance_requires_both_reflected_facts in Haccepted.
    destruct Haccepted as [HobservationFact HsubjectFact].
    simpl.
    split.
    + apply (proj1 Hobservation). exact HobservationFact.
    + apply (proj1 Hsubject). exact HsubjectFact.
  - intro Hadmissible.
    simpl in Hadmissible.
    destruct Hadmissible as [HobservationEq HsubjectEq].
    assert (HobservationFact : observationMatches = true).
    { apply (proj2 Hobservation). exact HobservationEq. }
    assert (HsubjectFact : mappedSubjectMatches = true).
    { apply (proj2 Hsubject). exact HsubjectEq. }
    rewrite HobservationFact, HsubjectFact.
    reflexivity.
Qed.

Theorem runtime_coincidence_mapping_always_rejects :
  decideRuntimeCoincidenceSubjectMapping =
    ProviderEvidenceRuntimeCoincidenceRejected.
Proof. reflexivity. Qed.

Theorem runtime_coincidence_mapping_decision_sound_complete :
  forall observation subject reason,
    (decideRuntimeCoincidenceSubjectMapping =
      ProviderEvidenceMappingAccepted <->
     EvidenceSubjectMappingAdmissible
       observation subject (RuntimeCoincidenceSubjectMapping reason)).
Proof.
  intros observation subject reason.
  split.
  - intro Haccepted. discriminate.
  - intro Hadmissible. simpl in Hadmissible. contradiction.
Qed.
