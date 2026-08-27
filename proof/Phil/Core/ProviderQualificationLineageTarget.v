From Stdlib Require Import Bool.Bool.

(*
  PHIL-PROV-LINEAGE-TARGET-001 — bounded PROV-013/014 lineage closure.

  PROV-013 preserves one exact semantic provider claim across distinct target
  profiles while requiring target-specific realization evidence to bind that
  exact claim/interface/implementation and carry fresh translation evidence.

  PROV-014 admits one selected provider realization only when the accepted
  admission, target evidence, provider occurrence, architecture instance and
  realization, provider interface, implementation, target profile, artifact,
  and runtime ABI all match exactly. Exported symbol names are deliberately
  absent from semantic applicability.
*)

Definition QualificationClaimRevision := nat.
Definition QualificationAdmissionRevision := nat.
Definition InterfaceRevision := nat.
Definition DefinitionRevision := nat.
Definition TargetRealizationEvidenceRevision := nat.
Definition TargetProfileRevision := nat.
Definition ArtifactRevision := nat.
Definition RuntimeAbiRevision := nat.
Definition RealizationRelationRevision := nat.
Definition ProviderRequirementOccurrenceKey := nat.
Definition InstanceRevision := nat.
Definition RealizationRevision := nat.
Definition ExportedSymbolMetadata := nat.
Definition TargetAssumptionTag := nat.
Definition OpaqueBoundaryKey := nat.

Inductive ProviderQualificationLayer : Type :=
| SemanticImplementationQualification
| ConcreteRealizationQualification
| CollapsedOpaqueQualification.

Inductive ProviderQualificationSubject : Type :=
| SemanticProviderImplementation : DefinitionRevision -> ProviderQualificationSubject
| ConcreteProviderRealization :
    DefinitionRevision -> ArtifactRevision -> ProviderQualificationSubject
| OpaqueProviderBoundary : OpaqueBoundaryKey -> ProviderQualificationSubject.

Record ProviderQualificationClaim : Type := mkProviderQualificationClaim {
  targetClaimRevision : QualificationClaimRevision;
  targetClaimRequiredInterface : InterfaceRevision;
  targetClaimLayer : ProviderQualificationLayer;
  targetClaimSubject : ProviderQualificationSubject;
  targetClaimSemanticImplementation : DefinitionRevision
}.

Record ProviderTargetRealizationEvidence : Type :=
  mkProviderTargetRealizationEvidence {
    targetEvidenceRevision : TargetRealizationEvidenceRevision;
    targetEvidenceClaimRevision : QualificationClaimRevision;
    targetEvidenceRequiredInterface : InterfaceRevision;
    targetEvidenceSemanticImplementation : DefinitionRevision;
    targetEvidenceTargetProfile : TargetProfileRevision;
    targetEvidenceArtifact : ArtifactRevision;
    targetEvidenceRuntimeAbi : RuntimeAbiRevision;
    targetEvidenceRealizationRelation : RealizationRelationRevision;
    targetEvidenceHasTranslationEvidence : bool;
    targetEvidenceAssumptionTag : TargetAssumptionTag
  }.

Record TargetEvidenceMatches
  (claim : ProviderQualificationClaim)
  (evidence : ProviderTargetRealizationEvidence) : Prop :=
  mkTargetEvidenceMatches {
    target_match_claim_revision :
      targetEvidenceClaimRevision evidence = targetClaimRevision claim;
    target_match_required_interface :
      targetEvidenceRequiredInterface evidence = targetClaimRequiredInterface claim;
    target_match_semantic_implementation :
      targetEvidenceSemanticImplementation evidence =
        targetClaimSemanticImplementation claim;
    target_match_translation_evidence :
      targetEvidenceHasTranslationEvidence evidence = true
  }.

Record CrossTargetSemanticReuse
  (claim : ProviderQualificationClaim)
  (priorEvidence newEvidence : ProviderTargetRealizationEvidence) : Prop :=
  mkCrossTargetSemanticReuse {
    cross_target_semantic_layer :
      targetClaimLayer claim = SemanticImplementationQualification;
    cross_target_semantic_subject :
      targetClaimSubject claim =
        SemanticProviderImplementation (targetClaimSemanticImplementation claim);
    cross_target_prior_matches : TargetEvidenceMatches claim priorEvidence;
    cross_target_new_matches : TargetEvidenceMatches claim newEvidence;
    cross_target_distinct_profiles :
      targetEvidenceTargetProfile priorEvidence <>
        targetEvidenceTargetProfile newEvidence
  }.

Theorem target_evidence_binds_exact_claim_revision :
  forall claim evidence,
    TargetEvidenceMatches claim evidence ->
    targetEvidenceClaimRevision evidence = targetClaimRevision claim.
Proof.
  intros claim evidence Hmatches.
  destruct Hmatches as [Hclaim _ _ _].
  exact Hclaim.
Qed.

Theorem target_evidence_binds_exact_required_interface :
  forall claim evidence,
    TargetEvidenceMatches claim evidence ->
    targetEvidenceRequiredInterface evidence = targetClaimRequiredInterface claim.
Proof.
  intros claim evidence Hmatches.
  destruct Hmatches as [_ Hinterface _ _].
  exact Hinterface.
Qed.

Theorem target_evidence_binds_exact_semantic_implementation :
  forall claim evidence,
    TargetEvidenceMatches claim evidence ->
    targetEvidenceSemanticImplementation evidence =
      targetClaimSemanticImplementation claim.
Proof.
  intros claim evidence Hmatches.
  destruct Hmatches as [_ _ Himplementation _].
  exact Himplementation.
Qed.

Theorem target_evidence_requires_translation_evidence :
  forall claim evidence,
    TargetEvidenceMatches claim evidence ->
    targetEvidenceHasTranslationEvidence evidence = true.
Proof.
  intros claim evidence Hmatches.
  destruct Hmatches as [_ _ _ Htranslation].
  exact Htranslation.
Qed.

Theorem cross_target_reuse_requires_semantic_layer :
  forall claim priorEvidence newEvidence,
    CrossTargetSemanticReuse claim priorEvidence newEvidence ->
    targetClaimLayer claim = SemanticImplementationQualification.
Proof.
  intros claim priorEvidence newEvidence Hreuse.
  destruct Hreuse as [Hlayer _ _ _ _].
  exact Hlayer.
Qed.

Theorem cross_target_reuse_requires_semantic_subject :
  forall claim priorEvidence newEvidence,
    CrossTargetSemanticReuse claim priorEvidence newEvidence ->
    targetClaimSubject claim =
      SemanticProviderImplementation (targetClaimSemanticImplementation claim).
Proof.
  intros claim priorEvidence newEvidence Hreuse.
  destruct Hreuse as [_ Hsubject _ _ _].
  exact Hsubject.
Qed.

Theorem cross_target_reuse_preserves_exact_claim_revision :
  forall claim priorEvidence newEvidence,
    CrossTargetSemanticReuse claim priorEvidence newEvidence ->
    targetEvidenceClaimRevision priorEvidence = targetClaimRevision claim /\
    targetEvidenceClaimRevision newEvidence = targetClaimRevision claim.
Proof.
  intros claim priorEvidence newEvidence Hreuse.
  destruct Hreuse as [_ _ Hprior Hnew _].
  destruct Hprior as [HpriorClaim _ _ _].
  destruct Hnew as [HnewClaim _ _ _].
  split; assumption.
Qed.

Theorem cross_target_reuse_preserves_exact_interface :
  forall claim priorEvidence newEvidence,
    CrossTargetSemanticReuse claim priorEvidence newEvidence ->
    targetEvidenceRequiredInterface priorEvidence = targetClaimRequiredInterface claim /\
    targetEvidenceRequiredInterface newEvidence = targetClaimRequiredInterface claim.
Proof.
  intros claim priorEvidence newEvidence Hreuse.
  destruct Hreuse as [_ _ Hprior Hnew _].
  destruct Hprior as [_ HpriorInterface _ _].
  destruct Hnew as [_ HnewInterface _ _].
  split; assumption.
Qed.

Theorem cross_target_reuse_preserves_exact_implementation :
  forall claim priorEvidence newEvidence,
    CrossTargetSemanticReuse claim priorEvidence newEvidence ->
    targetEvidenceSemanticImplementation priorEvidence =
      targetClaimSemanticImplementation claim /\
    targetEvidenceSemanticImplementation newEvidence =
      targetClaimSemanticImplementation claim.
Proof.
  intros claim priorEvidence newEvidence Hreuse.
  destruct Hreuse as [_ _ Hprior Hnew _].
  destruct Hprior as [_ _ HpriorImplementation _].
  destruct Hnew as [_ _ HnewImplementation _].
  split; assumption.
Qed.

Theorem cross_target_reuse_requires_fresh_translation_bindings :
  forall claim priorEvidence newEvidence,
    CrossTargetSemanticReuse claim priorEvidence newEvidence ->
    targetEvidenceHasTranslationEvidence priorEvidence = true /\
    targetEvidenceHasTranslationEvidence newEvidence = true.
Proof.
  intros claim priorEvidence newEvidence Hreuse.
  destruct Hreuse as [_ _ Hprior Hnew _].
  destruct Hprior as [_ _ _ HpriorTranslation].
  destruct Hnew as [_ _ _ HnewTranslation].
  split; assumption.
Qed.

Theorem cross_target_reuse_requires_distinct_profiles :
  forall claim priorEvidence newEvidence,
    CrossTargetSemanticReuse claim priorEvidence newEvidence ->
    targetEvidenceTargetProfile priorEvidence <>
      targetEvidenceTargetProfile newEvidence.
Proof.
  intros claim priorEvidence newEvidence Hreuse.
  destruct Hreuse as [_ _ _ _ Hdistinct].
  exact Hdistinct.
Qed.

Theorem same_target_is_not_cross_target_reuse :
  forall claim priorEvidence newEvidence,
    targetEvidenceTargetProfile priorEvidence =
      targetEvidenceTargetProfile newEvidence ->
    ~ CrossTargetSemanticReuse claim priorEvidence newEvidence.
Proof.
  intros claim priorEvidence newEvidence Hsame Hreuse.
  destruct Hreuse as [_ _ _ _ Hdistinct].
  apply Hdistinct.
  exact Hsame.
Qed.

Theorem concrete_claim_cannot_masquerade_as_semantic_reuse :
  forall claim priorEvidence newEvidence,
    targetClaimLayer claim = ConcreteRealizationQualification ->
    ~ CrossTargetSemanticReuse claim priorEvidence newEvidence.
Proof.
  intros claim priorEvidence newEvidence Hconcrete Hreuse.
  destruct Hreuse as [Hsemantic _ _ _ _].
  rewrite Hconcrete in Hsemantic.
  discriminate.
Qed.

Theorem missing_new_target_translation_evidence_rejects :
  forall claim priorEvidence newEvidence,
    targetEvidenceHasTranslationEvidence newEvidence = false ->
    ~ CrossTargetSemanticReuse claim priorEvidence newEvidence.
Proof.
  intros claim priorEvidence newEvidence Hmissing Hreuse.
  destruct Hreuse as [_ _ _ Hnew _].
  destruct Hnew as [_ _ _ Htranslation].
  rewrite Hmissing in Htranslation.
  discriminate.
Qed.

Definition withTargetAssumptionTag
  (tag : TargetAssumptionTag)
  (evidence : ProviderTargetRealizationEvidence) :
  ProviderTargetRealizationEvidence :=
  mkProviderTargetRealizationEvidence
    (targetEvidenceRevision evidence)
    (targetEvidenceClaimRevision evidence)
    (targetEvidenceRequiredInterface evidence)
    (targetEvidenceSemanticImplementation evidence)
    (targetEvidenceTargetProfile evidence)
    (targetEvidenceArtifact evidence)
    (targetEvidenceRuntimeAbi evidence)
    (targetEvidenceRealizationRelation evidence)
    (targetEvidenceHasTranslationEvidence evidence)
    tag.

Theorem target_specific_assumption_is_downstream_of_semantic_match :
  forall claim evidence tag,
    TargetEvidenceMatches claim evidence ->
    TargetEvidenceMatches claim (withTargetAssumptionTag tag evidence).
Proof.
  intros claim evidence tag Hmatches.
  destruct Hmatches as [Hclaim Hinterface Himplementation Htranslation].
  constructor; simpl; assumption.
Qed.

Inductive ProviderQualificationAdmissionDecision : Type :=
| QualificationAdmitted
| QualificationRejected.

Record CheckedProviderQualificationAdmission : Type :=
  mkCheckedProviderQualificationAdmission {
    checkedAdmissionClaimRevision : QualificationClaimRevision;
    checkedAdmissionRevision : QualificationAdmissionRevision;
    checkedAdmissionDecision : ProviderQualificationAdmissionDecision
  }.

Record ProviderConcreteAdmissionApplicability : Type :=
  mkProviderConcreteAdmissionApplicability {
    applicabilityAdmissionRevision : QualificationAdmissionRevision;
    applicabilityClaimRevision : QualificationClaimRevision;
    applicabilityTargetEvidenceRevision : TargetRealizationEvidenceRevision;
    applicabilityRequirementOccurrence : ProviderRequirementOccurrenceKey;
    applicabilityInstanceRevision : InstanceRevision;
    applicabilityRealizationRevision : RealizationRevision;
    applicabilityRequiredInterface : InterfaceRevision;
    applicabilityImplementationDefinition : DefinitionRevision;
    applicabilityTargetProfile : TargetProfileRevision;
    applicabilityArtifact : ArtifactRevision;
    applicabilityRuntimeAbi : RuntimeAbiRevision;
    applicabilityExportedSymbols : ExportedSymbolMetadata
  }.

Record SelectedProviderRealization : Type := mkSelectedProviderRealization {
  selectedAdmissionRevision : QualificationAdmissionRevision;
  selectedTargetEvidenceRevision : TargetRealizationEvidenceRevision;
  selectedRequirementOccurrence : ProviderRequirementOccurrenceKey;
  selectedInstanceRevision : InstanceRevision;
  selectedRealizationRevision : RealizationRevision;
  selectedRequiredInterface : InterfaceRevision;
  selectedImplementationDefinition : DefinitionRevision;
  selectedTargetProfile : TargetProfileRevision;
  selectedArtifact : ArtifactRevision;
  selectedRuntimeAbi : RuntimeAbiRevision;
  selectedExportedSymbols : ExportedSymbolMetadata
}.

Record AdmissionApplicable
  (admission : CheckedProviderQualificationAdmission)
  (evidence : ProviderTargetRealizationEvidence)
  (applicability : ProviderConcreteAdmissionApplicability)
  (selected : SelectedProviderRealization) : Prop :=
  mkAdmissionApplicable {
    applicable_admission_is_admitted :
      checkedAdmissionDecision admission = QualificationAdmitted;
    applicable_admission_revision_exact :
      applicabilityAdmissionRevision applicability = checkedAdmissionRevision admission;
    applicable_claim_revision_exact :
      applicabilityClaimRevision applicability = checkedAdmissionClaimRevision admission;
    applicable_target_evidence_revision_exact :
      applicabilityTargetEvidenceRevision applicability = targetEvidenceRevision evidence;
    applicable_target_evidence_claim_exact :
      targetEvidenceClaimRevision evidence = checkedAdmissionClaimRevision admission;
    applicable_interface_matches_evidence :
      applicabilityRequiredInterface applicability = targetEvidenceRequiredInterface evidence;
    applicable_implementation_matches_evidence :
      applicabilityImplementationDefinition applicability =
        targetEvidenceSemanticImplementation evidence;
    applicable_target_matches_evidence :
      applicabilityTargetProfile applicability = targetEvidenceTargetProfile evidence;
    applicable_artifact_matches_evidence :
      applicabilityArtifact applicability = targetEvidenceArtifact evidence;
    applicable_abi_matches_evidence :
      applicabilityRuntimeAbi applicability = targetEvidenceRuntimeAbi evidence;
    selected_admission_exact :
      selectedAdmissionRevision selected = applicabilityAdmissionRevision applicability;
    selected_target_evidence_exact :
      selectedTargetEvidenceRevision selected =
        applicabilityTargetEvidenceRevision applicability;
    selected_occurrence_exact :
      selectedRequirementOccurrence selected = applicabilityRequirementOccurrence applicability;
    selected_instance_exact :
      selectedInstanceRevision selected = applicabilityInstanceRevision applicability;
    selected_realization_exact :
      selectedRealizationRevision selected = applicabilityRealizationRevision applicability;
    selected_interface_exact :
      selectedRequiredInterface selected = applicabilityRequiredInterface applicability;
    selected_implementation_exact :
      selectedImplementationDefinition selected =
        applicabilityImplementationDefinition applicability;
    selected_target_exact :
      selectedTargetProfile selected = applicabilityTargetProfile applicability;
    selected_artifact_exact :
      selectedArtifact selected = applicabilityArtifact applicability;
    selected_runtime_abi_exact :
      selectedRuntimeAbi selected = applicabilityRuntimeAbi applicability
  }.

Theorem applicability_requires_admitted_qualification :
  forall admission evidence applicability selected,
    AdmissionApplicable admission evidence applicability selected ->
    checkedAdmissionDecision admission = QualificationAdmitted.
Proof.
  intros admission evidence applicability selected Happlicable.
  destruct Happlicable as [Hadmitted _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  exact Hadmitted.
Qed.

Theorem applicability_binds_exact_admission_and_claim :
  forall admission evidence applicability selected,
    AdmissionApplicable admission evidence applicability selected ->
    applicabilityAdmissionRevision applicability = checkedAdmissionRevision admission /\
    applicabilityClaimRevision applicability = checkedAdmissionClaimRevision admission.
Proof.
  intros admission evidence applicability selected Happlicable.
  destruct Happlicable as [_ Hadmission Hclaim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  split; assumption.
Qed.

Theorem applicability_binds_exact_target_evidence :
  forall admission evidence applicability selected,
    AdmissionApplicable admission evidence applicability selected ->
    applicabilityTargetEvidenceRevision applicability = targetEvidenceRevision evidence /\
    targetEvidenceClaimRevision evidence = checkedAdmissionClaimRevision admission.
Proof.
  intros admission evidence applicability selected Happlicable.
  destruct Happlicable as [_ _ _ Hevidence HevidenceClaim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  split; assumption.
Qed.

Theorem applicability_binds_exact_interface_implementation_target :
  forall admission evidence applicability selected,
    AdmissionApplicable admission evidence applicability selected ->
    applicabilityRequiredInterface applicability = targetEvidenceRequiredInterface evidence /\
    applicabilityImplementationDefinition applicability =
      targetEvidenceSemanticImplementation evidence /\
    applicabilityTargetProfile applicability = targetEvidenceTargetProfile evidence.
Proof.
  intros admission evidence applicability selected Happlicable.
  destruct Happlicable as [_ _ _ _ _ Hinterface Himplementation Htarget _ _ _ _ _ _ _ _ _ _ _ _].
  repeat split; assumption.
Qed.

Theorem applicability_binds_exact_artifact_and_abi :
  forall admission evidence applicability selected,
    AdmissionApplicable admission evidence applicability selected ->
    applicabilityArtifact applicability = targetEvidenceArtifact evidence /\
    applicabilityRuntimeAbi applicability = targetEvidenceRuntimeAbi evidence.
Proof.
  intros admission evidence applicability selected Happlicable.
  destruct Happlicable as [_ _ _ _ _ _ _ _ Hartifact Habi _ _ _ _ _ _ _ _ _ _].
  split; assumption.
Qed.

Theorem selected_realization_binds_exact_lineage :
  forall admission evidence applicability selected,
    AdmissionApplicable admission evidence applicability selected ->
    selectedAdmissionRevision selected = applicabilityAdmissionRevision applicability /\
    selectedTargetEvidenceRevision selected = applicabilityTargetEvidenceRevision applicability /\
    selectedRequirementOccurrence selected = applicabilityRequirementOccurrence applicability.
Proof.
  intros admission evidence applicability selected Happlicable.
  destruct Happlicable as [_ _ _ _ _ _ _ _ _ _ Hadmission Hevidence Hoccurrence _ _ _ _ _ _ _].
  repeat split; assumption.
Qed.

Theorem selected_realization_binds_exact_architecture :
  forall admission evidence applicability selected,
    AdmissionApplicable admission evidence applicability selected ->
    selectedInstanceRevision selected = applicabilityInstanceRevision applicability /\
    selectedRealizationRevision selected = applicabilityRealizationRevision applicability.
Proof.
  intros admission evidence applicability selected Happlicable.
  destruct Happlicable as [_ _ _ _ _ _ _ _ _ _ _ _ _ Hinstance Hrealization _ _ _ _ _].
  split; assumption.
Qed.

Theorem selected_realization_binds_exact_provider_target :
  forall admission evidence applicability selected,
    AdmissionApplicable admission evidence applicability selected ->
    selectedRequiredInterface selected = applicabilityRequiredInterface applicability /\
    selectedImplementationDefinition selected =
      applicabilityImplementationDefinition applicability /\
    selectedTargetProfile selected = applicabilityTargetProfile applicability.
Proof.
  intros admission evidence applicability selected Happlicable.
  destruct Happlicable as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinterface Himplementation Htarget _ _].
  repeat split; assumption.
Qed.

Theorem selected_realization_binds_exact_artifact_abi :
  forall admission evidence applicability selected,
    AdmissionApplicable admission evidence applicability selected ->
    selectedArtifact selected = applicabilityArtifact applicability /\
    selectedRuntimeAbi selected = applicabilityRuntimeAbi applicability.
Proof.
  intros admission evidence applicability selected Happlicable.
  destruct Happlicable as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hartifact Habi].
  split; assumption.
Qed.

Theorem rejected_admission_cannot_justify_realization :
  forall admission evidence applicability selected,
    checkedAdmissionDecision admission = QualificationRejected ->
    ~ AdmissionApplicable admission evidence applicability selected.
Proof.
  intros admission evidence applicability selected Hrejected Happlicable.
  destruct Happlicable as [Hadmitted _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  rewrite Hrejected in Hadmitted.
  discriminate.
Qed.

Definition withApplicabilitySymbols
  (symbols : ExportedSymbolMetadata)
  (applicability : ProviderConcreteAdmissionApplicability) :
  ProviderConcreteAdmissionApplicability :=
  mkProviderConcreteAdmissionApplicability
    (applicabilityAdmissionRevision applicability)
    (applicabilityClaimRevision applicability)
    (applicabilityTargetEvidenceRevision applicability)
    (applicabilityRequirementOccurrence applicability)
    (applicabilityInstanceRevision applicability)
    (applicabilityRealizationRevision applicability)
    (applicabilityRequiredInterface applicability)
    (applicabilityImplementationDefinition applicability)
    (applicabilityTargetProfile applicability)
    (applicabilityArtifact applicability)
    (applicabilityRuntimeAbi applicability)
    symbols.

Definition withSelectedSymbols
  (symbols : ExportedSymbolMetadata)
  (selected : SelectedProviderRealization) : SelectedProviderRealization :=
  mkSelectedProviderRealization
    (selectedAdmissionRevision selected)
    (selectedTargetEvidenceRevision selected)
    (selectedRequirementOccurrence selected)
    (selectedInstanceRevision selected)
    (selectedRealizationRevision selected)
    (selectedRequiredInterface selected)
    (selectedImplementationDefinition selected)
    (selectedTargetProfile selected)
    (selectedArtifact selected)
    (selectedRuntimeAbi selected)
    symbols.

Theorem exported_symbol_rename_is_nonsemantic_to_applicability :
  forall admission evidence applicability selected applicabilitySymbols selectedSymbols,
    AdmissionApplicable admission evidence applicability selected ->
    AdmissionApplicable
      admission evidence
      (withApplicabilitySymbols applicabilitySymbols applicability)
      (withSelectedSymbols selectedSymbols selected).
Proof.
  intros admission evidence applicability selected applicabilitySymbols selectedSymbols Happlicable.
  destruct Happlicable as
    [Hadmitted Hadmission Hclaim Hevidence HevidenceClaim Hinterface Himplementation
     Htarget Hartifact Habi HselectedAdmission HselectedEvidence Hoccurrence Hinstance
     Hrealization HselectedInterface HselectedImplementation HselectedTarget
     HselectedArtifact HselectedAbi].
  constructor; simpl; assumption.
Qed.
