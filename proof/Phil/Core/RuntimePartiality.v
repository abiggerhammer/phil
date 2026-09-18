From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import SystemsRealizationEffects StorageAllocationFailure.
From Phil.Verification Require Import VerificationArtifact.

(*
  PHIL-SYS-PARTIALITY-001 — target-independent realization partiality.

  Every reachable lower-level validity/capacity hazard must be an exact
  target-strengthening precondition and must have exactly one explicit
  disposition.  There is deliberately no "native target behavior" disposition.

  This proof composes:
  - PHIL-SYS-REALIZE-001 / target strengthening for exact target preconditions
    and retained derived realization obligations;
  - PHIL-MEM-FAIL-001 for allocation-failure widening; and
  - PHIL-VERIFY-ARTIFACT-001 as an independent final-artifact closure layer.

  Concrete Text/Map/Set identities, target/profile facts, evidence truth,
  runtime enforcement correctness, and backend/toolchain execution remain
  explicit correspondence/evidence/TCB boundaries.
*)

Definition RuntimeSourceOutcome := nat.
Definition RuntimeEnforcementKey := nat.
Definition RuntimeAssumptionKey := nat.
Definition RuntimeDeploymentRequirementKey := nat.
Definition RuntimeAssuranceRevision := nat.
Definition RuntimeCapacityClass := nat.
Definition RuntimeOtherPartialityIdentity := nat.

Inductive RuntimePartialityKind : Type :=
| RuntimeUndefinedBehavior
| RuntimePoison
| RuntimeUnreachable
| RuntimeTrap
| RuntimeExceptionalHalt
| RuntimeCapacityExhaustion (capacity : RuntimeCapacityClass)
| RuntimeOtherPartiality (identity : RuntimeOtherPartialityIdentity).

Record RuntimePartialityHazard : Type := mkRuntimePartialityHazard {
  runtimeHazardPrecondition : RealizationFactId;
  runtimeHazardKind : RuntimePartialityKind
}.

Definition RuntimePartialityHazardSet := RuntimePartialityHazard -> bool.
Definition RuntimeSourceOutcomeSet := RuntimeSourceOutcome -> bool.
Definition RuntimeAssuranceRevisionEnvironment :=
  RealizationFactId -> RuntimeAssuranceRevision -> bool.

Inductive RuntimePartialityDisposition : Type :=
| RuntimePartialityMapsToSourceOutcome :
    RuntimeSourceOutcome -> RuntimePartialityDisposition
| RuntimePartialityProvedSatisfied :
    RuntimeAssuranceRevision -> RuntimePartialityDisposition
| RuntimePartialityRuntimeEnforced :
    RuntimeEnforcementKey -> RuntimePartialityDisposition
| RuntimePartialityAssumption :
    RuntimeAssumptionKey -> RuntimePartialityDisposition
| RuntimePartialityDeploymentRequirement :
    RuntimeDeploymentRequirementKey -> RuntimePartialityDisposition.

Definition RuntimePartialityDispositionEnvironment :=
  RuntimePartialityHazard -> option RuntimePartialityDisposition.

Definition RuntimePartialityKindValid
  (kind : RuntimePartialityKind) : Prop :=
  match kind with
  | RuntimeCapacityExhaustion capacity => capacity <> 0
  | RuntimeOtherPartiality identity => identity <> 0
  | _ => True
  end.

Definition RetainedDerivedRealizationObligation
  (fact : TargetStrengtheningFact) : Prop :=
  exists obligation,
    strengtheningDerivedObligation fact = Some obligation /\
    DerivedRealizationObligationValid
      (strengtheningIntroducer fact) obligation.

Definition RuntimePartialityDispositionValid
  (precondition : RealizationFactId)
  (fact : TargetStrengtheningFact)
  (sourceOutcomes : RuntimeSourceOutcomeSet)
  (assuranceRevisions : RuntimeAssuranceRevisionEnvironment)
  (disposition : RuntimePartialityDisposition) : Prop :=
  match disposition with
  | RuntimePartialityMapsToSourceOutcome outcome =>
      outcome <> 0 /\ sourceOutcomes outcome = true
  | RuntimePartialityProvedSatisfied revision =>
      revision <> 0 /\
      strengtheningHasSourceAssurance fact = true /\
      strengtheningSourceAssuranceKnown fact = true /\
      assuranceRevisions precondition revision = true
  | RuntimePartialityRuntimeEnforced key =>
      key <> 0 /\ RetainedDerivedRealizationObligation fact
  | RuntimePartialityAssumption key =>
      key <> 0 /\ RetainedDerivedRealizationObligation fact
  | RuntimePartialityDeploymentRequirement key =>
      key <> 0 /\ RetainedDerivedRealizationObligation fact
  end.

Definition HazardPreconditionsKnown
  (liveStrengthenings : RealizationFactSet)
  (hazards : RuntimePartialityHazardSet) : Prop :=
  forall hazard,
    hazards hazard = true ->
    liveStrengthenings (runtimeHazardPrecondition hazard) = true.

Definition ExactRuntimePartialityDispositionCoverage
  (hazards : RuntimePartialityHazardSet)
  (dispositions : RuntimePartialityDispositionEnvironment) : Prop :=
  forall hazard,
    hazards hazard = true <->
    exists disposition, dispositions hazard = Some disposition.

Record RuntimePartialityClosure
  (liveStrengthenings : RealizationFactSet)
  (strengthenings : StrengtheningEnvironment)
  (hazards : RuntimePartialityHazardSet)
  (dispositions : RuntimePartialityDispositionEnvironment)
  (sourceOutcomes : RuntimeSourceOutcomeSet)
  (assuranceRevisions : RuntimeAssuranceRevisionEnvironment) : Prop :=
  mkRuntimePartialityClosure {
    runtimePartialityTargetStrengtheningClosure :
      TargetStrengtheningClosure liveStrengthenings strengthenings;
    runtimePartialityHazardPreconditionsKnown :
      HazardPreconditionsKnown liveStrengthenings hazards;
    runtimePartialityHazardKindsValid :
      forall hazard,
        hazards hazard = true ->
        RuntimePartialityKindValid (runtimeHazardKind hazard);
    runtimePartialityDispositionCoverageExact :
      ExactRuntimePartialityDispositionCoverage hazards dispositions;
    runtimePartialityDispositionsValid :
      forall hazard disposition fact,
        hazards hazard = true ->
        dispositions hazard = Some disposition ->
        strengthenings (runtimeHazardPrecondition hazard) = Some fact ->
        RuntimePartialityDispositionValid
          (runtimeHazardPrecondition hazard)
          fact
          sourceOutcomes
          assuranceRevisions
          disposition
  }.

Theorem every_classified_hazard_has_exact_strengthening_and_disposition :
  forall liveStrengthenings strengthenings hazards dispositions
         sourceOutcomes assuranceRevisions hazard,
    RuntimePartialityClosure
      liveStrengthenings strengthenings hazards dispositions
      sourceOutcomes assuranceRevisions ->
    hazards hazard = true ->
    exists fact disposition,
      strengthenings (runtimeHazardPrecondition hazard) = Some fact /\
      TargetStrengtheningValid fact /\
      dispositions hazard = Some disposition /\
      RuntimePartialityDispositionValid
        (runtimeHazardPrecondition hazard)
        fact
        sourceOutcomes
        assuranceRevisions
        disposition.
Proof.
  intros liveStrengthenings strengthenings hazards dispositions
    sourceOutcomes assuranceRevisions hazard Hclosure Hhazard.
  destruct Hclosure as
    [Hstrengthening Hknown Hkind Hcoverage Hvalid].
  destruct Hstrengthening as [HstrengtheningCoverage HstrengtheningValid].
  specialize (Hknown hazard Hhazard) as Hlive.
  apply (proj1 (HstrengtheningCoverage
    (runtimeHazardPrecondition hazard))) in Hlive.
  destruct Hlive as [fact Hfact].
  apply (proj1 (Hcoverage hazard)) in Hhazard.
  destruct Hhazard as [disposition Hdisposition].
  exists fact, disposition.
  split.
  - exact Hfact.
  - split.
    + eapply HstrengtheningValid.
      exact Hfact.
    + split.
      * exact Hdisposition.
      * eapply Hvalid.
        -- apply (proj2 (Hcoverage hazard)).
           exists disposition.
           exact Hdisposition.
        -- exact Hdisposition.
        -- exact Hfact.
Qed.

Theorem missing_partiality_disposition_cannot_close :
  forall liveStrengthenings strengthenings hazards dispositions
         sourceOutcomes assuranceRevisions hazard,
    hazards hazard = true ->
    dispositions hazard = None ->
    ~ RuntimePartialityClosure
        liveStrengthenings strengthenings hazards dispositions
        sourceOutcomes assuranceRevisions.
Proof.
  intros liveStrengthenings strengthenings hazards dispositions
    sourceOutcomes assuranceRevisions hazard Hhazard Hmissing Hclosure.
  destruct Hclosure as [_ _ _ Hcoverage _].
  apply (proj1 (Hcoverage hazard)) in Hhazard.
  destruct Hhazard as [disposition Hlookup].
  rewrite Hmissing in Hlookup.
  discriminate Hlookup.
Qed.

Theorem invalid_partiality_kind_cannot_close :
  forall liveStrengthenings strengthenings hazards dispositions
         sourceOutcomes assuranceRevisions hazard,
    hazards hazard = true ->
    ~ RuntimePartialityKindValid (runtimeHazardKind hazard) ->
    ~ RuntimePartialityClosure
        liveStrengthenings strengthenings hazards dispositions
        sourceOutcomes assuranceRevisions.
Proof.
  intros liveStrengthenings strengthenings hazards dispositions
    sourceOutcomes assuranceRevisions hazard Hhazard Hinvalid Hclosure.
  destruct Hclosure as [_ _ Hkinds _ _].
  apply Hinvalid.
  eapply Hkinds.
  exact Hhazard.
Qed.

Theorem mapped_partiality_requires_declared_source_outcome :
  forall precondition fact sourceOutcomes assuranceRevisions outcome,
    RuntimePartialityDispositionValid
      precondition fact sourceOutcomes assuranceRevisions
      (RuntimePartialityMapsToSourceOutcome outcome) ->
    outcome <> 0 /\ sourceOutcomes outcome = true.
Proof.
  intros precondition fact sourceOutcomes assuranceRevisions outcome Hvalid.
  exact Hvalid.
Qed.

Theorem proved_partiality_requires_exact_admitted_assurance :
  forall precondition fact sourceOutcomes assuranceRevisions revision,
    RuntimePartialityDispositionValid
      precondition fact sourceOutcomes assuranceRevisions
      (RuntimePartialityProvedSatisfied revision) ->
    revision <> 0 /\
    strengtheningHasSourceAssurance fact = true /\
    strengtheningSourceAssuranceKnown fact = true /\
    assuranceRevisions precondition revision = true.
Proof.
  intros precondition fact sourceOutcomes assuranceRevisions revision Hvalid.
  exact Hvalid.
Qed.

Theorem runtime_enforcement_requires_retained_realization_obligation :
  forall precondition fact sourceOutcomes assuranceRevisions key,
    RuntimePartialityDispositionValid
      precondition fact sourceOutcomes assuranceRevisions
      (RuntimePartialityRuntimeEnforced key) ->
    key <> 0 /\ RetainedDerivedRealizationObligation fact.
Proof.
  intros precondition fact sourceOutcomes assuranceRevisions key Hvalid.
  exact Hvalid.
Qed.

Theorem assumption_requires_retained_realization_obligation :
  forall precondition fact sourceOutcomes assuranceRevisions key,
    RuntimePartialityDispositionValid
      precondition fact sourceOutcomes assuranceRevisions
      (RuntimePartialityAssumption key) ->
    key <> 0 /\ RetainedDerivedRealizationObligation fact.
Proof.
  intros precondition fact sourceOutcomes assuranceRevisions key Hvalid.
  exact Hvalid.
Qed.

Theorem deployment_requirement_requires_retained_realization_obligation :
  forall precondition fact sourceOutcomes assuranceRevisions key,
    RuntimePartialityDispositionValid
      precondition fact sourceOutcomes assuranceRevisions
      (RuntimePartialityDeploymentRequirement key) ->
    key <> 0 /\ RetainedDerivedRealizationObligation fact.
Proof.
  intros precondition fact sourceOutcomes assuranceRevisions key Hvalid.
  exact Hvalid.
Qed.

Theorem retained_partiality_obligation_keeps_exact_target_introducer :
  forall fact obligation other,
    TargetStrengtheningValid fact ->
    strengtheningDerivedObligation fact = Some obligation ->
    derivedRealizationIntroducers obligation other = true ->
    other = strengtheningIntroducer fact.
Proof.
  apply derived_obligation_retains_exact_introducer.
Qed.

Theorem certified_allocation_failure_has_explicit_disposition :
  forall base surface disposition,
    StorageFailureRealizationValid
      (makeStorageFailureRealization
        base surface (PhysicalAllocationMayFail disposition)) ->
    (exists failure,
      disposition = StorageFailureMapsToSource failure /\
      failure <> 0 /\
      sourceFailureContains failure surface = true) /
    (exists evidence,
      disposition = StorageFailureProvedUnreachable evidence /\
      evidence <> 0) /
    (exists assumption,
      disposition = StorageFailureAssumption assumption /\
      assumption <> 0) /
    (exists requirement,
      disposition = StorageFailureDeploymentRequirement requirement /\
      requirement <> 0).
Proof.
  apply accepted_potential_failure_has_one_explicit_disposition.
Qed.

Definition PartialityClosedArtifactCertified
  (source : SourceAssuranceFacts)
  (stage : ArtifactStageContext)
  (manifest : FinalManifestFacts)
  (partialityClosed : Prop) : Prop :=
  FinalArtifactCertified source stage manifest /\ partialityClosed.

Theorem final_artifact_certification_does_not_excuse_unclosed_partiality :
  forall source stage manifest partialityClosed,
    FinalArtifactCertified source stage manifest ->
    ~ partialityClosed ->
    ~ PartialityClosedArtifactCertified
        source stage manifest partialityClosed.
Proof.
  intros source stage manifest partialityClosed Hartifact Hnot Hcombined.
  apply Hnot.
  exact (proj2 Hcombined).
Qed.

Theorem exact_artifact_and_partiality_composition_closes :
  forall source stage manifest partialityClosed,
    FinalArtifactCertified source stage manifest ->
    partialityClosed ->
    PartialityClosedArtifactCertified
      source stage manifest partialityClosed.
Proof.
  intros.
  split; assumption.
Qed.
