From Stdlib Require Import Bool.Bool.

From Phil.Assurance Require Import ValidityScope.
From Phil.Systems Require Import FactDisposition.
From Phil.Core Require Import SystemsStageClosure.

(*
  PHIL-VERIFY-ARTIFACT-001 — source closure, realization preservation, and
  final artifact certification.

  Source-level assurance is necessary but not sufficient for an emitted
  artifact.  Final certification composes three independently checkable facts:

  - an already accepted source-assurance identity;
  - the already-Certified PHIL-SYS-STAGE-CLOSURE-001 preservation boundary for
    the exact emitted realization; and
  - final scoped manifest closure bound to that exact source assurance and
    StageClosure identity.

  The Systems predecessor already owns exact source-disposition coverage,
  exact target-mechanism justification, validity-scope matching, and exact
  subject/instance/realization/systems/StageContract/verifier-profile identity.
  This proof deliberately imports those semantics rather than re-defining them.

  Concrete GenericApplicationAssurance construction, Haskell StageClosureBundle
  representation, AssuranceManifest/ledger verification, canonical digest
  construction, compiler/backend/toolchain correctness, provider behavior, and
  target execution remain explicit predecessor/representation/TCB boundaries.
*)

Record SourceAssuranceFacts : Type := mkSourceAssuranceFacts {
  sourceAssuranceIdentity : nat;
  sourceAssuranceVerificationRevision : nat;
  sourceAssurancePolicyRevision : nat
}.

Definition SourceAssuranceValid (source : SourceAssuranceFacts) : Prop :=
  sourceAssuranceIdentity source <> 0 /\
  sourceAssuranceVerificationRevision source <> 0 /\
  sourceAssurancePolicyRevision source <> 0.

Record ArtifactStageContext : Type := mkArtifactStageContext {
  artifactFactModel : StageFactModel;
  artifactLiveSource : SourceResponsibilitySet;
  artifactTargetMechanisms : TargetMechanismSet;
  artifactSourceDispositions : SourceDispositionEnvironment;
  artifactTargetKinds : TargetMechanismKindEnvironment;
  artifactTargetJustifications : TargetJustificationEnvironment;
  artifactValidityScope : ValidityMap;
  artifactEffectiveValidity : ValidityMap;
  artifactStageIdentity : StageClosureIdentityFacts
}.

Definition ArtifactStagePreserved (stage : ArtifactStageContext) : Prop :=
  SystemsStageClosurePreserved
    (artifactFactModel stage)
    (artifactLiveSource stage)
    (artifactTargetMechanisms stage)
    (artifactSourceDispositions stage)
    (artifactTargetKinds stage)
    (artifactTargetJustifications stage)
    (artifactValidityScope stage)
    (artifactEffectiveValidity stage)
    (artifactStageIdentity stage).

Record FinalManifestFacts : Type := mkFinalManifestFacts {
  finalManifestIdentity : nat;
  finalManifestSourceAssuranceIdentity : nat;
  finalManifestSubjectRevision : nat;
  finalManifestInstanceRevision : nat;
  finalManifestRealizationRevision : nat;
  finalManifestSystemsRevision : nat;
  finalManifestStageContractRevision : nat;
  finalManifestVerifierProfileRevision : nat;
  finalManifestClosed : bool;
  finalManifestScopeMatches : bool
}.

Definition FinalManifestMatches
  (source : SourceAssuranceFacts)
  (stage : ArtifactStageContext)
  (manifest : FinalManifestFacts) : Prop :=
  finalManifestIdentity manifest <> 0 /\
  finalManifestClosed manifest = true /\
  finalManifestScopeMatches manifest = true /\
  finalManifestSourceAssuranceIdentity manifest = sourceAssuranceIdentity source /\
  finalManifestSubjectRevision manifest =
    closureConcreteSubjectRevision (artifactStageIdentity stage) /\
  finalManifestInstanceRevision manifest =
    closureConcreteInstanceRevision (artifactStageIdentity stage) /\
  finalManifestRealizationRevision manifest =
    closureConcreteRealizationRevision (artifactStageIdentity stage) /\
  finalManifestSystemsRevision manifest =
    closureConcreteSystemsRevision (artifactStageIdentity stage) /\
  finalManifestStageContractRevision manifest =
    closureConcreteStageContractRevision (artifactStageIdentity stage) /\
  finalManifestVerifierProfileRevision manifest =
    closureConcreteVerifierProfileRevision (artifactStageIdentity stage).

Definition FinalArtifactCertified
  (source : SourceAssuranceFacts)
  (stage : ArtifactStageContext)
  (manifest : FinalManifestFacts) : Prop :=
  SourceAssuranceValid source /\
  ArtifactStagePreserved stage /\
  FinalManifestMatches source stage manifest.

Theorem final_artifact_requires_source_assurance :
  forall source stage manifest,
    FinalArtifactCertified source stage manifest ->
    SourceAssuranceValid source.
Proof.
  intros source stage manifest Hcertified.
  exact (proj1 Hcertified).
Qed.

Theorem final_artifact_requires_exact_stage_closure :
  forall source stage manifest,
    FinalArtifactCertified source stage manifest ->
    ArtifactStagePreserved stage.
Proof.
  intros source stage manifest Hcertified.
  exact (proj1 (proj2 Hcertified)).
Qed.

Theorem final_artifact_requires_final_manifest_closure :
  forall source stage manifest,
    FinalArtifactCertified source stage manifest ->
    FinalManifestMatches source stage manifest.
Proof.
  intros source stage manifest Hcertified.
  exact (proj2 (proj2 Hcertified)).
Qed.

Theorem source_assurance_alone_is_not_artifact_certification :
  forall source stage manifest,
    SourceAssuranceValid source ->
    ~ ArtifactStagePreserved stage ->
    ~ FinalArtifactCertified source stage manifest.
Proof.
  intros source stage manifest Hsource HstageMissing Hcertified.
  apply HstageMissing.
  eapply final_artifact_requires_exact_stage_closure.
  exact Hcertified.
Qed.

Theorem exact_composition_certifies_artifact :
  forall source stage manifest,
    SourceAssuranceValid source ->
    ArtifactStagePreserved stage ->
    FinalManifestMatches source stage manifest ->
    FinalArtifactCertified source stage manifest.
Proof.
  intros source stage manifest Hsource Hstage Hmanifest.
  split.
  - exact Hsource.
  - split.
    + exact Hstage.
    + exact Hmanifest.
Qed.

Theorem stale_stored_systems_identity_prevents_artifact_certification :
  forall source stage manifest,
    closureRecomputedSystemsRevision (artifactStageIdentity stage) <>
      closureStoredSystemsRevision (artifactStageIdentity stage) ->
    ~ FinalArtifactCertified source stage manifest.
Proof.
  intros source stage manifest Hstale Hcertified.
  pose proof
    (final_artifact_requires_exact_stage_closure
      source stage manifest Hcertified) as Hstage.
  destruct Hstage as [_ _ _ _ _ Hidentity].
  eapply (stale_stored_systems_revision_cannot_close
    (artifactStageIdentity stage) Hstale).
  exact Hidentity.
Qed.

Theorem stale_stored_final_identity_prevents_artifact_certification :
  forall source stage manifest,
    closureRecomputedFinalRevision (artifactStageIdentity stage) <>
      closureStoredFinalRevision (artifactStageIdentity stage) ->
    ~ FinalArtifactCertified source stage manifest.
Proof.
  intros source stage manifest Hstale Hcertified.
  pose proof
    (final_artifact_requires_exact_stage_closure
      source stage manifest Hcertified) as Hstage.
  destruct Hstage as [_ _ _ _ _ Hidentity].
  eapply (stale_stored_final_revision_cannot_close
    (artifactStageIdentity stage) Hstale).
  exact Hidentity.
Qed.

Theorem mutated_realization_manifest_binding_prevents_certification :
  forall source stage manifest,
    finalManifestRealizationRevision manifest <>
      closureConcreteRealizationRevision (artifactStageIdentity stage) ->
    ~ FinalArtifactCertified source stage manifest.
Proof.
  intros source stage manifest Hmismatch Hcertified.
  pose proof
    (final_artifact_requires_final_manifest_closure
      source stage manifest Hcertified) as Hmanifest.
  destruct Hmanifest as
    [_ [_ [_ [_ [_ [_ [Hrealization _]]]]]]].
  apply Hmismatch.
  exact Hrealization.
Qed.

Theorem mutated_systems_manifest_binding_prevents_certification :
  forall source stage manifest,
    finalManifestSystemsRevision manifest <>
      closureConcreteSystemsRevision (artifactStageIdentity stage) ->
    ~ FinalArtifactCertified source stage manifest.
Proof.
  intros source stage manifest Hmismatch Hcertified.
  pose proof
    (final_artifact_requires_final_manifest_closure
      source stage manifest Hcertified) as Hmanifest.
  destruct Hmanifest as
    [_ [_ [_ [_ [_ [_ [_ [Hsystems _]]]]]]]].
  apply Hmismatch.
  exact Hsystems.
Qed.

Theorem unjustified_target_mechanism_prevents_artifact_certification :
  forall source stage manifest mechanism,
    artifactTargetMechanisms stage mechanism = true ->
    artifactTargetJustifications stage mechanism = None ->
    ~ FinalArtifactCertified source stage manifest.
Proof.
  intros source stage manifest mechanism Hlive Hnone Hcertified.
  pose proof
    (final_artifact_requires_exact_stage_closure
      source stage manifest Hcertified) as Hstage.
  destruct Hstage as [_ _ _ Htarget _ _].
  pose proof
    (every_live_target_mechanism_has_exact_justification
      (artifactLiveSource stage)
      (artifactTargetMechanisms stage)
      (artifactTargetKinds stage)
      (artifactTargetJustifications stage)
      mechanism
      Htarget
      Hlive) as Hjustified.
  destruct Hjustified as
    [kind [justification [Hkind [Hlookup Hvalid]]]].
  rewrite Hnone in Hlookup.
  discriminate Hlookup.
Qed.

Theorem closed_manifest_is_bound_to_exact_stage_identity :
  forall source stage manifest,
    FinalArtifactCertified source stage manifest ->
    finalManifestRealizationRevision manifest =
      closureConcreteRealizationRevision (artifactStageIdentity stage) /\
    finalManifestSystemsRevision manifest =
      closureConcreteSystemsRevision (artifactStageIdentity stage) /\
    finalManifestStageContractRevision manifest =
      closureConcreteStageContractRevision (artifactStageIdentity stage).
Proof.
  intros source stage manifest Hcertified.
  pose proof
    (final_artifact_requires_final_manifest_closure
      source stage manifest Hcertified) as Hmanifest.
  destruct Hmanifest as
    [_ [_ [_ [_ [_ [_ [Hrealization [Hsystems [Hstage _]]]]]]]]].
  split.
  - exact Hrealization.
  - split.
    + exact Hsystems.
    + exact Hstage.
Qed.
