From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Core Require Import ProviderQualificationLineageTarget.

Definition boolAnd11
  (a b c d e f g h i j k : bool) : bool :=
  a && b && c && d && e && f && g && h && i && j && k.

Definition boolAnd20
  (a b c d e f g h i j k l m n o p q r s t : bool) : bool :=
  a && b && c && d && e && f && g && h && i && j && k && l && m && n && o && p && q && r && s && t.

Inductive TargetReuseDecision : Type :=
| TargetReuseAcceptedDecision
| TargetReuseSemanticLayerDecision
| TargetReuseSemanticSubjectDecision
| TargetReusePriorClaimDecision
| TargetReusePriorInterfaceDecision
| TargetReusePriorImplementationDecision
| TargetReusePriorTranslationDecision
| TargetReuseNewClaimDecision
| TargetReuseNewInterfaceDecision
| TargetReuseNewImplementationDecision
| TargetReuseNewTranslationDecision
| TargetReuseDistinctProfileDecision.

Definition decideTargetReuseByFacts
  (semanticLayer semanticSubject
   priorClaim priorInterface priorImplementation priorTranslation
   newClaim newInterface newImplementation newTranslation
   distinctProfiles : bool) : TargetReuseDecision :=
  if semanticLayer then
    if semanticSubject then
      if priorClaim then
        if priorInterface then
          if priorImplementation then
            if priorTranslation then
              if newClaim then
                if newInterface then
                  if newImplementation then
                    if newTranslation then
                      if distinctProfiles
                      then TargetReuseAcceptedDecision
                      else TargetReuseDistinctProfileDecision
                    else TargetReuseNewTranslationDecision
                  else TargetReuseNewImplementationDecision
                else TargetReuseNewInterfaceDecision
              else TargetReuseNewClaimDecision
            else TargetReusePriorTranslationDecision
          else TargetReusePriorImplementationDecision
        else TargetReusePriorInterfaceDecision
      else TargetReusePriorClaimDecision
    else TargetReuseSemanticSubjectDecision
  else TargetReuseSemanticLayerDecision.

Definition TargetReuseFactsSatisfied
  (semanticLayer semanticSubject
   priorClaim priorInterface priorImplementation priorTranslation
   newClaim newInterface newImplementation newTranslation
   distinctProfiles : bool) : Prop :=
  semanticLayer = true /\
  semanticSubject = true /\
  priorClaim = true /\
  priorInterface = true /\
  priorImplementation = true /\
  priorTranslation = true /\
  newClaim = true /\
  newInterface = true /\
  newImplementation = true /\
  newTranslation = true /\
  distinctProfiles = true.

Theorem target_reuse_decision_accepted_iff :
  forall a b c d e f g h i j k,
    decideTargetReuseByFacts a b c d e f g h i j k = TargetReuseAcceptedDecision <->
    TargetReuseFactsSatisfied a b c d e f g h i j k.
Proof.
  intros a b c d e f g h i j k.
  unfold decideTargetReuseByFacts, TargetReuseFactsSatisfied.
  destruct a; simpl; [|intuition discriminate].
  destruct b; simpl; [|intuition discriminate].
  destruct c; simpl; [|intuition discriminate].
  destruct d; simpl; [|intuition discriminate].
  destruct e; simpl; [|intuition discriminate].
  destruct f; simpl; [|intuition discriminate].
  destruct g; simpl; [|intuition discriminate].
  destruct h; simpl; [|intuition discriminate].
  destruct i; simpl; [|intuition discriminate].
  destruct j; simpl; [|intuition discriminate].
  destruct k; simpl; intuition discriminate.
Qed.

Definition layerIsSemantic (layer : ProviderQualificationLayer) : bool :=
  match layer with
  | SemanticImplementationQualification => true
  | _ => false
  end.

Lemma layer_is_semantic_iff :
  forall layer,
    layerIsSemantic layer = true <-> layer = SemanticImplementationQualification.
Proof.
  intros layer; destruct layer; simpl; split; intro H; try reflexivity; discriminate.
Qed.

Definition subjectIsSemanticImplementation
  (subject : ProviderQualificationSubject)
  (implementation : DefinitionRevision) : bool :=
  match subject with
  | SemanticProviderImplementation actual => Nat.eqb actual implementation
  | _ => false
  end.

Lemma subject_is_semantic_implementation_iff :
  forall subject implementation,
    subjectIsSemanticImplementation subject implementation = true <->
    subject = SemanticProviderImplementation implementation.
Proof.
  intros subject implementation.
  destruct subject as [actual | actual artifact | boundary]; simpl.
  - split; intro H.
    + apply Nat.eqb_eq in H. subst. reflexivity.
    + inversion H. apply Nat.eqb_refl.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
Qed.

Definition distinctNat (left right : nat) : bool := negb (Nat.eqb left right).

Lemma distinct_nat_iff :
  forall left right,
    distinctNat left right = true <-> left <> right.
Proof.
  intros left right.
  unfold distinctNat.
  rewrite Bool.negb_true_iff.
  apply Nat.eqb_neq.
Qed.

Definition reflectedTargetReuseDecision
  (claim : ProviderQualificationClaim)
  (priorEvidence newEvidence : ProviderTargetRealizationEvidence) : TargetReuseDecision :=
  decideTargetReuseByFacts
    (layerIsSemantic (targetClaimLayer claim))
    (subjectIsSemanticImplementation
      (targetClaimSubject claim)
      (targetClaimSemanticImplementation claim))
    (Nat.eqb (targetEvidenceClaimRevision priorEvidence) (targetClaimRevision claim))
    (Nat.eqb (targetEvidenceRequiredInterface priorEvidence) (targetClaimRequiredInterface claim))
    (Nat.eqb (targetEvidenceSemanticImplementation priorEvidence) (targetClaimSemanticImplementation claim))
    (targetEvidenceHasTranslationEvidence priorEvidence)
    (Nat.eqb (targetEvidenceClaimRevision newEvidence) (targetClaimRevision claim))
    (Nat.eqb (targetEvidenceRequiredInterface newEvidence) (targetClaimRequiredInterface claim))
    (Nat.eqb (targetEvidenceSemanticImplementation newEvidence) (targetClaimSemanticImplementation claim))
    (targetEvidenceHasTranslationEvidence newEvidence)
    (distinctNat
      (targetEvidenceTargetProfile priorEvidence)
      (targetEvidenceTargetProfile newEvidence)).

Theorem reflected_target_reuse_decision_exact :
  forall claim priorEvidence newEvidence,
    reflectedTargetReuseDecision claim priorEvidence newEvidence = TargetReuseAcceptedDecision <->
    CrossTargetSemanticReuse claim priorEvidence newEvidence.
Proof.
  intros claim priorEvidence newEvidence.
  unfold reflectedTargetReuseDecision.
  rewrite target_reuse_decision_accepted_iff.
  split.
  - intros H.
    destruct H as [Hlayer [Hsubject [Hpc [Hpi [Hpimpl [Hpt [Hnc [Hni [Hnimpl [Hnt Hdistinct]]]]]]]]]].
    apply layer_is_semantic_iff in Hlayer.
    apply subject_is_semantic_implementation_iff in Hsubject.
    apply Nat.eqb_eq in Hpc.
    apply Nat.eqb_eq in Hpi.
    apply Nat.eqb_eq in Hpimpl.
    apply Nat.eqb_eq in Hnc.
    apply Nat.eqb_eq in Hni.
    apply Nat.eqb_eq in Hnimpl.
    apply distinct_nat_iff in Hdistinct.
    constructor.
    + exact Hlayer.
    + exact Hsubject.
    + constructor; assumption.
    + constructor; assumption.
    + exact Hdistinct.
  - intro Hreuse.
    destruct Hreuse as [Hlayer Hsubject Hprior Hnew Hdistinct].
    destruct Hprior as [Hpc Hpi Hpimpl Hpt].
    destruct Hnew as [Hnc Hni Hnimpl Hnt].
    repeat split.
    + apply layer_is_semantic_iff. exact Hlayer.
    + apply subject_is_semantic_implementation_iff. exact Hsubject.
    + apply Nat.eqb_eq. exact Hpc.
    + apply Nat.eqb_eq. exact Hpi.
    + apply Nat.eqb_eq. exact Hpimpl.
    + exact Hpt.
    + apply Nat.eqb_eq. exact Hnc.
    + apply Nat.eqb_eq. exact Hni.
    + apply Nat.eqb_eq. exact Hnimpl.
    + exact Hnt.
    + apply distinct_nat_iff. exact Hdistinct.
Qed.

Inductive AdmissionApplicabilityDecision : Type :=
| AdmissionApplicabilityAcceptedDecision
| AdmissionApplicabilityRejectedDecision
| AdmissionApplicabilityAdmissionRevisionDecision
| AdmissionApplicabilityClaimRevisionDecision
| AdmissionApplicabilityTargetEvidenceRevisionDecision
| AdmissionApplicabilityTargetEvidenceClaimDecision
| AdmissionApplicabilityInterfaceEvidenceDecision
| AdmissionApplicabilityImplementationEvidenceDecision
| AdmissionApplicabilityTargetEvidenceDecision
| AdmissionApplicabilityArtifactEvidenceDecision
| AdmissionApplicabilityAbiEvidenceDecision
| AdmissionApplicabilitySelectedAdmissionDecision
| AdmissionApplicabilitySelectedEvidenceDecision
| AdmissionApplicabilitySelectedOccurrenceDecision
| AdmissionApplicabilitySelectedInstanceDecision
| AdmissionApplicabilitySelectedRealizationDecision
| AdmissionApplicabilitySelectedInterfaceDecision
| AdmissionApplicabilitySelectedImplementationDecision
| AdmissionApplicabilitySelectedTargetDecision
| AdmissionApplicabilitySelectedArtifactDecision
| AdmissionApplicabilitySelectedAbiDecision.

Definition decideAdmissionApplicabilityByFacts
  (admitted admissionRevision claimRevision targetEvidenceRevision targetEvidenceClaim
   interfaceEvidence implementationEvidence targetEvidence artifactEvidence abiEvidence
   selectedAdmission selectedEvidence selectedOccurrence selectedInstance selectedRealization
   selectedInterface selectedImplementation selectedTarget selectedArtifact selectedAbi : bool)
  : AdmissionApplicabilityDecision :=
  if admitted then
    if admissionRevision then
      if claimRevision then
        if targetEvidenceRevision then
          if targetEvidenceClaim then
            if interfaceEvidence then
              if implementationEvidence then
                if targetEvidence then
                  if artifactEvidence then
                    if abiEvidence then
                      if selectedAdmission then
                        if selectedEvidence then
                          if selectedOccurrence then
                            if selectedInstance then
                              if selectedRealization then
                                if selectedInterface then
                                  if selectedImplementation then
                                    if selectedTarget then
                                      if selectedArtifact then
                                        if selectedAbi
                                        then AdmissionApplicabilityAcceptedDecision
                                        else AdmissionApplicabilitySelectedAbiDecision
                                      else AdmissionApplicabilitySelectedArtifactDecision
                                    else AdmissionApplicabilitySelectedTargetDecision
                                  else AdmissionApplicabilitySelectedImplementationDecision
                                else AdmissionApplicabilitySelectedInterfaceDecision
                              else AdmissionApplicabilitySelectedRealizationDecision
                            else AdmissionApplicabilitySelectedInstanceDecision
                          else AdmissionApplicabilitySelectedOccurrenceDecision
                        else AdmissionApplicabilitySelectedEvidenceDecision
                      else AdmissionApplicabilitySelectedAdmissionDecision
                    else AdmissionApplicabilityAbiEvidenceDecision
                  else AdmissionApplicabilityArtifactEvidenceDecision
                else AdmissionApplicabilityTargetEvidenceDecision
              else AdmissionApplicabilityImplementationEvidenceDecision
            else AdmissionApplicabilityInterfaceEvidenceDecision
          else AdmissionApplicabilityTargetEvidenceClaimDecision
        else AdmissionApplicabilityTargetEvidenceRevisionDecision
      else AdmissionApplicabilityClaimRevisionDecision
    else AdmissionApplicabilityAdmissionRevisionDecision
  else AdmissionApplicabilityRejectedDecision.

Definition AdmissionApplicabilityFactsSatisfied
  (admitted admissionRevision claimRevision targetEvidenceRevision targetEvidenceClaim
   interfaceEvidence implementationEvidence targetEvidence artifactEvidence abiEvidence
   selectedAdmission selectedEvidence selectedOccurrence selectedInstance selectedRealization
   selectedInterface selectedImplementation selectedTarget selectedArtifact selectedAbi : bool)
  : Prop :=
  admitted = true /\
  admissionRevision = true /\
  claimRevision = true /\
  targetEvidenceRevision = true /\
  targetEvidenceClaim = true /\
  interfaceEvidence = true /\
  implementationEvidence = true /\
  targetEvidence = true /\
  artifactEvidence = true /\
  abiEvidence = true /\
  selectedAdmission = true /\
  selectedEvidence = true /\
  selectedOccurrence = true /\
  selectedInstance = true /\
  selectedRealization = true /\
  selectedInterface = true /\
  selectedImplementation = true /\
  selectedTarget = true /\
  selectedArtifact = true /\
  selectedAbi = true.

Theorem admission_applicability_decision_accepted_iff :
  forall a b c d e f g h i j k l m n o p q r s t,
    decideAdmissionApplicabilityByFacts a b c d e f g h i j k l m n o p q r s t =
      AdmissionApplicabilityAcceptedDecision <->
    AdmissionApplicabilityFactsSatisfied a b c d e f g h i j k l m n o p q r s t.
Proof.
  intros a b c d e f g h i j k l m n o p q r s t.
  unfold decideAdmissionApplicabilityByFacts, AdmissionApplicabilityFactsSatisfied.
  destruct a; simpl; [|intuition discriminate].
  destruct b; simpl; [|intuition discriminate].
  destruct c; simpl; [|intuition discriminate].
  destruct d; simpl; [|intuition discriminate].
  destruct e; simpl; [|intuition discriminate].
  destruct f; simpl; [|intuition discriminate].
  destruct g; simpl; [|intuition discriminate].
  destruct h; simpl; [|intuition discriminate].
  destruct i; simpl; [|intuition discriminate].
  destruct j; simpl; [|intuition discriminate].
  destruct k; simpl; [|intuition discriminate].
  destruct l; simpl; [|intuition discriminate].
  destruct m; simpl; [|intuition discriminate].
  destruct n; simpl; [|intuition discriminate].
  destruct o; simpl; [|intuition discriminate].
  destruct p; simpl; [|intuition discriminate].
  destruct q; simpl; [|intuition discriminate].
  destruct r; simpl; [|intuition discriminate].
  destruct s; simpl; [|intuition discriminate].
  destruct t; simpl; intuition discriminate.
Qed.

Definition admissionIsAdmitted (decision : ProviderQualificationAdmissionDecision) : bool :=
  match decision with
  | QualificationAdmitted => true
  | QualificationRejected => false
  end.

Lemma admission_is_admitted_iff :
  forall decision,
    admissionIsAdmitted decision = true <-> decision = QualificationAdmitted.
Proof.
  intros decision; destruct decision; simpl; split; intro H; try reflexivity; discriminate.
Qed.

Definition reflectedAdmissionApplicabilityDecision
  (admission : CheckedProviderQualificationAdmission)
  (evidence : ProviderTargetRealizationEvidence)
  (applicability : ProviderConcreteAdmissionApplicability)
  (selected : SelectedProviderRealization) : AdmissionApplicabilityDecision :=
  decideAdmissionApplicabilityByFacts
    (admissionIsAdmitted (checkedAdmissionDecision admission))
    (Nat.eqb (applicabilityAdmissionRevision applicability) (checkedAdmissionRevision admission))
    (Nat.eqb (applicabilityClaimRevision applicability) (checkedAdmissionClaimRevision admission))
    (Nat.eqb (applicabilityTargetEvidenceRevision applicability) (targetEvidenceRevision evidence))
    (Nat.eqb (targetEvidenceClaimRevision evidence) (checkedAdmissionClaimRevision admission))
    (Nat.eqb (applicabilityRequiredInterface applicability) (targetEvidenceRequiredInterface evidence))
    (Nat.eqb (applicabilityImplementationDefinition applicability) (targetEvidenceSemanticImplementation evidence))
    (Nat.eqb (applicabilityTargetProfile applicability) (targetEvidenceTargetProfile evidence))
    (Nat.eqb (applicabilityArtifact applicability) (targetEvidenceArtifact evidence))
    (Nat.eqb (applicabilityRuntimeAbi applicability) (targetEvidenceRuntimeAbi evidence))
    (Nat.eqb (selectedAdmissionRevision selected) (applicabilityAdmissionRevision applicability))
    (Nat.eqb (selectedTargetEvidenceRevision selected) (applicabilityTargetEvidenceRevision applicability))
    (Nat.eqb (selectedRequirementOccurrence selected) (applicabilityRequirementOccurrence applicability))
    (Nat.eqb (selectedInstanceRevision selected) (applicabilityInstanceRevision applicability))
    (Nat.eqb (selectedRealizationRevision selected) (applicabilityRealizationRevision applicability))
    (Nat.eqb (selectedRequiredInterface selected) (applicabilityRequiredInterface applicability))
    (Nat.eqb (selectedImplementationDefinition selected) (applicabilityImplementationDefinition applicability))
    (Nat.eqb (selectedTargetProfile selected) (applicabilityTargetProfile applicability))
    (Nat.eqb (selectedArtifact selected) (applicabilityArtifact applicability))
    (Nat.eqb (selectedRuntimeAbi selected) (applicabilityRuntimeAbi applicability)).

Theorem reflected_admission_applicability_decision_exact :
  forall admission evidence applicability selected,
    reflectedAdmissionApplicabilityDecision admission evidence applicability selected =
      AdmissionApplicabilityAcceptedDecision <->
    AdmissionApplicable admission evidence applicability selected.
Proof.
  intros admission evidence applicability selected.
  unfold reflectedAdmissionApplicabilityDecision.
  rewrite admission_applicability_decision_accepted_iff.
  split.
  - intros H.
    destruct H as [H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 H19]]]]]]]]]]]]]]]]]]].
    apply admission_is_admitted_iff in H0.
    apply Nat.eqb_eq in H1.
    apply Nat.eqb_eq in H2.
    apply Nat.eqb_eq in H3.
    apply Nat.eqb_eq in H4.
    apply Nat.eqb_eq in H5.
    apply Nat.eqb_eq in H6.
    apply Nat.eqb_eq in H7.
    apply Nat.eqb_eq in H8.
    apply Nat.eqb_eq in H9.
    apply Nat.eqb_eq in H10.
    apply Nat.eqb_eq in H11.
    apply Nat.eqb_eq in H12.
    apply Nat.eqb_eq in H13.
    apply Nat.eqb_eq in H14.
    apply Nat.eqb_eq in H15.
    apply Nat.eqb_eq in H16.
    apply Nat.eqb_eq in H17.
    apply Nat.eqb_eq in H18.
    apply Nat.eqb_eq in H19.
    constructor; assumption.
  - intro H.
    destruct H as [H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19].
    repeat split.
    + apply admission_is_admitted_iff. exact H0.
    + apply Nat.eqb_eq. exact H1.
    + apply Nat.eqb_eq. exact H2.
    + apply Nat.eqb_eq. exact H3.
    + apply Nat.eqb_eq. exact H4.
    + apply Nat.eqb_eq. exact H5.
    + apply Nat.eqb_eq. exact H6.
    + apply Nat.eqb_eq. exact H7.
    + apply Nat.eqb_eq. exact H8.
    + apply Nat.eqb_eq. exact H9.
    + apply Nat.eqb_eq. exact H10.
    + apply Nat.eqb_eq. exact H11.
    + apply Nat.eqb_eq. exact H12.
    + apply Nat.eqb_eq. exact H13.
    + apply Nat.eqb_eq. exact H14.
    + apply Nat.eqb_eq. exact H15.
    + apply Nat.eqb_eq. exact H16.
    + apply Nat.eqb_eq. exact H17.
    + apply Nat.eqb_eq. exact H18.
    + apply Nat.eqb_eq. exact H19.
Qed.