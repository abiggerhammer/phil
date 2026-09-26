From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import SystemsStageClosure.
From Phil.Verification Require Import
  VerificationArtifact
  FinalManifestStageReflection.

(*
  D-ARTIFACT-MANIFEST-REFLECTION-01 — native certified-release coordinate
  separation.

  The existing FinalManifestStageReflection proof deliberately requires an
  exact representation premise for an independently authoritative native
  manifest.  The independent package audit then identified an important
  representation pressure point: the native release path contains several
  distinct identity classes which must not be collapsed merely because the
  proof model uses nat-valued abstract coordinates.

  In particular, Phil.Verification.CertifiedRelease checks a manifest
  implementation digest against the raw Systems artifact digest and separately
  checks the lowering-ledger root.  The accepted StageClosure additionally
  carries a normalized/common Systems revision, the common Phase-1 StageContract
  revision, and the final closed-stage contract revision.  Those meanings are
  distinct.

  This model therefore keeps the native manifest and native stage coordinates
  separate, then projects them into the older NativeFinalManifestAuthority only
  after explicit binding and representation premises have been supplied.
  Nothing here claims that a Haskell record is automatically an extraction of
  this model; the concrete native-to-model adapter remains a correspondence
  boundary.
*)

Record NativeCertifiedReleaseManifest : Type :=
  mkNativeCertifiedReleaseManifest {
    nativeReleaseManifestIdentity : nat;
    nativeReleaseSourceAssuranceIdentity : nat;
    nativeReleaseImplementationDigest : nat;
    nativeReleaseLoweringLedgerRoot : nat;
    nativeReleaseManifestClosed : bool;
    nativeReleaseManifestScopeMatches : bool
  }.

Record NativeCertifiedReleaseStage : Type :=
  mkNativeCertifiedReleaseStage {
    nativeReleaseRawSystemsDigest : nat;
    nativeReleaseStageLoweringLedgerRoot : nat;
    nativeReleaseSubjectRevision : nat;
    nativeReleaseInstanceRevision : nat;
    nativeReleaseRealizationRevision : nat;
    nativeReleaseNormalizedSystemsRevision : nat;
    nativeReleaseCommonStageContractRevision : nat;
    nativeReleaseClosedStageContractRevision : nat;
    nativeReleaseVerifierProfileRevision : nat
  }.

Definition NativeCertifiedReleaseManifestAccepted
  (manifest : NativeCertifiedReleaseManifest) : Prop :=
  nativeReleaseManifestIdentity manifest <> 0 /\
  nativeReleaseManifestClosed manifest = true /\
  nativeReleaseManifestScopeMatches manifest = true.

Definition NativeCertifiedReleaseBinding
  (source : SourceAssuranceFacts)
  (manifest : NativeCertifiedReleaseManifest)
  (stage : NativeCertifiedReleaseStage) : Prop :=
  nativeReleaseSourceAssuranceIdentity manifest =
    sourceAssuranceIdentity source /\
  nativeReleaseImplementationDigest manifest =
    nativeReleaseRawSystemsDigest stage /\
  nativeReleaseLoweringLedgerRoot manifest =
    nativeReleaseStageLoweringLedgerRoot stage.

Definition NativeCertifiedReleaseStageRepresentsArtifactStage
  (stage : NativeCertifiedReleaseStage)
  (artifact : ArtifactStageContext) : Prop :=
  nativeReleaseSubjectRevision stage =
    closureConcreteSubjectRevision (artifactStageIdentity artifact) /\
  nativeReleaseInstanceRevision stage =
    closureConcreteInstanceRevision (artifactStageIdentity artifact) /\
  nativeReleaseRealizationRevision stage =
    closureConcreteRealizationRevision (artifactStageIdentity artifact) /\
  nativeReleaseNormalizedSystemsRevision stage =
    closureConcreteSystemsRevision (artifactStageIdentity artifact) /\
  nativeReleaseCommonStageContractRevision stage =
    closureConcreteStageContractRevision (artifactStageIdentity artifact) /\
  nativeReleaseClosedStageContractRevision stage =
    closureStoredFinalRevision (artifactStageIdentity artifact) /\
  nativeReleaseVerifierProfileRevision stage =
    closureConcreteVerifierProfileRevision (artifactStageIdentity artifact).

Definition FinalManifestRepresentsCertifiedRelease
  (nativeManifest : NativeCertifiedReleaseManifest)
  (nativeStage : NativeCertifiedReleaseStage)
  (manifest : FinalManifestFacts) : Prop :=
  finalManifestIdentity manifest =
    nativeReleaseManifestIdentity nativeManifest /\
  finalManifestClosed manifest =
    nativeReleaseManifestClosed nativeManifest /\
  finalManifestScopeMatches manifest =
    nativeReleaseManifestScopeMatches nativeManifest /\
  finalManifestSourceAssuranceIdentity manifest =
    nativeReleaseSourceAssuranceIdentity nativeManifest /\
  finalManifestSubjectRevision manifest =
    nativeReleaseSubjectRevision nativeStage /\
  finalManifestInstanceRevision manifest =
    nativeReleaseInstanceRevision nativeStage /\
  finalManifestRealizationRevision manifest =
    nativeReleaseRealizationRevision nativeStage /\
  finalManifestSystemsRevision manifest =
    nativeReleaseNormalizedSystemsRevision nativeStage /\
  finalManifestStageContractRevision manifest =
    nativeReleaseCommonStageContractRevision nativeStage /\
  finalManifestVerifierProfileRevision manifest =
    nativeReleaseVerifierProfileRevision nativeStage.

Definition projectCertifiedReleaseManifestAuthority
  (nativeManifest : NativeCertifiedReleaseManifest)
  (nativeStage : NativeCertifiedReleaseStage) : NativeFinalManifestAuthority :=
  mkNativeFinalManifestAuthority
    (nativeReleaseManifestIdentity nativeManifest)
    (nativeReleaseSourceAssuranceIdentity nativeManifest)
    (nativeReleaseSubjectRevision nativeStage)
    (nativeReleaseInstanceRevision nativeStage)
    (nativeReleaseRealizationRevision nativeStage)
    (nativeReleaseNormalizedSystemsRevision nativeStage)
    (nativeReleaseCommonStageContractRevision nativeStage)
    (nativeReleaseVerifierProfileRevision nativeStage)
    (nativeReleaseManifestClosed nativeManifest)
    (nativeReleaseManifestScopeMatches nativeManifest).

Theorem accepted_certified_release_manifest_projects_to_native_authority :
  forall nativeManifest nativeStage,
    NativeCertifiedReleaseManifestAccepted nativeManifest ->
    NativeFinalManifestAccepted
      (projectCertifiedReleaseManifestAuthority nativeManifest nativeStage).
Proof.
  intros nativeManifest nativeStage Haccepted.
  destruct Haccepted as [Hidentity [Hclosed Hscope]].
  unfold NativeFinalManifestAccepted.
  simpl.
  repeat split; assumption.
Qed.

Theorem certified_release_binding_and_stage_representation_bind_projection :
  forall source nativeManifest nativeStage artifact,
    NativeCertifiedReleaseBinding source nativeManifest nativeStage ->
    NativeCertifiedReleaseStageRepresentsArtifactStage nativeStage artifact ->
    NativeFinalManifestBoundToSourceAndStage
      source artifact
      (projectCertifiedReleaseManifestAuthority nativeManifest nativeStage).
Proof.
  intros source nativeManifest nativeStage artifact Hbinding Hstage.
  destruct Hbinding as [Hsource [Himplementation Hlowering]].
  destruct Hstage as
    [Hsubject
      [Hinstance
        [Hrealization
          [Hsystems [Hcommon [Hclosed Hprofile]]]]]].
  unfold NativeFinalManifestBoundToSourceAndStage.
  simpl.
  repeat split; assumption.
Qed.

Theorem certified_release_manifest_representation_projects_exactly :
  forall nativeManifest nativeStage manifest,
    FinalManifestRepresentsCertifiedRelease
      nativeManifest nativeStage manifest ->
    FinalManifestRepresentsNative
      (projectCertifiedReleaseManifestAuthority nativeManifest nativeStage)
      manifest.
Proof.
  intros nativeManifest nativeStage manifest Hrepresentation.
  unfold FinalManifestRepresentsCertifiedRelease in Hrepresentation.
  unfold FinalManifestRepresentsNative.
  simpl.
  exact Hrepresentation.
Qed.

Theorem exact_certified_release_coordinate_reflection_establishes_manifest_match :
  forall source artifact nativeManifest nativeStage manifest,
    NativeCertifiedReleaseManifestAccepted nativeManifest ->
    NativeCertifiedReleaseBinding source nativeManifest nativeStage ->
    NativeCertifiedReleaseStageRepresentsArtifactStage nativeStage artifact ->
    FinalManifestRepresentsCertifiedRelease
      nativeManifest nativeStage manifest ->
    FinalManifestMatches source artifact manifest.
Proof.
  intros source artifact nativeManifest nativeStage manifest
    Haccepted Hbinding Hstage Hrepresentation.
  eapply exact_native_manifest_reflection_establishes_final_manifest_matches
    with
      (native :=
        projectCertifiedReleaseManifestAuthority nativeManifest nativeStage).
  - eapply accepted_certified_release_manifest_projects_to_native_authority.
    exact Haccepted.
  - eapply certified_release_binding_and_stage_representation_bind_projection.
    + exact Hbinding.
    + exact Hstage.
  - eapply certified_release_manifest_representation_projects_exactly.
    exact Hrepresentation.
Qed.

Theorem exact_certified_release_coordinate_reflection_establishes_artifact :
  forall source artifact nativeManifest nativeStage manifest,
    SourceAssuranceValid source ->
    ArtifactStagePreserved artifact ->
    NativeCertifiedReleaseManifestAccepted nativeManifest ->
    NativeCertifiedReleaseBinding source nativeManifest nativeStage ->
    NativeCertifiedReleaseStageRepresentsArtifactStage nativeStage artifact ->
    FinalManifestRepresentsCertifiedRelease
      nativeManifest nativeStage manifest ->
    FinalArtifactCertified source artifact manifest.
Proof.
  intros source artifact nativeManifest nativeStage manifest
    Hsource Hartifact Haccepted Hbinding Hstage Hrepresentation.
  apply exact_composition_certifies_artifact.
  - exact Hsource.
  - exact Hartifact.
  - eapply exact_certified_release_coordinate_reflection_establishes_manifest_match.
    + exact Haccepted.
    + exact Hbinding.
    + exact Hstage.
    + exact Hrepresentation.
Qed.

Theorem manifest_implementation_digest_drift_breaks_release_binding :
  forall source nativeManifest nativeStage,
    nativeReleaseImplementationDigest nativeManifest <>
      nativeReleaseRawSystemsDigest nativeStage ->
    ~ NativeCertifiedReleaseBinding source nativeManifest nativeStage.
Proof.
  intros source nativeManifest nativeStage Hmismatch Hbinding.
  destruct Hbinding as [_ [Hdigest _]].
  apply Hmismatch.
  exact Hdigest.
Qed.

Theorem manifest_lowering_root_drift_breaks_release_binding :
  forall source nativeManifest nativeStage,
    nativeReleaseLoweringLedgerRoot nativeManifest <>
      nativeReleaseStageLoweringLedgerRoot nativeStage ->
    ~ NativeCertifiedReleaseBinding source nativeManifest nativeStage.
Proof.
  intros source nativeManifest nativeStage Hmismatch Hbinding.
  destruct Hbinding as [_ [_ Hroot]].
  apply Hmismatch.
  exact Hroot.
Qed.

Theorem raw_systems_digest_cannot_replace_normalized_systems_revision :
  forall nativeManifest nativeStage manifest,
    nativeReleaseRawSystemsDigest nativeStage <>
      nativeReleaseNormalizedSystemsRevision nativeStage ->
    finalManifestSystemsRevision manifest =
      nativeReleaseRawSystemsDigest nativeStage ->
    ~ FinalManifestRepresentsCertifiedRelease
        nativeManifest nativeStage manifest.
Proof.
  intros nativeManifest nativeStage manifest Hdistinct Hraw Hrepresentation.
  destruct Hrepresentation as
    [_ [_ [_ [_ [_ [_ [_ [Hnormalized _]]]]]]]].
  rewrite Hraw in Hnormalized.
  apply Hdistinct.
  exact Hnormalized.
Qed.

Theorem closed_stage_revision_cannot_replace_common_stage_contract :
  forall nativeManifest nativeStage manifest,
    nativeReleaseClosedStageContractRevision nativeStage <>
      nativeReleaseCommonStageContractRevision nativeStage ->
    finalManifestStageContractRevision manifest =
      nativeReleaseClosedStageContractRevision nativeStage ->
    ~ FinalManifestRepresentsCertifiedRelease
        nativeManifest nativeStage manifest.
Proof.
  intros nativeManifest nativeStage manifest Hdistinct Hclosed Hrepresentation.
  destruct Hrepresentation as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hcommon _]]]]]]]]].
  rewrite Hclosed in Hcommon.
  apply Hdistinct.
  exact Hcommon.
Qed.

Theorem represented_closed_stage_revision_targets_stored_final_identity :
  forall nativeStage artifact,
    NativeCertifiedReleaseStageRepresentsArtifactStage nativeStage artifact ->
    nativeReleaseClosedStageContractRevision nativeStage =
      closureStoredFinalRevision (artifactStageIdentity artifact).
Proof.
  intros nativeStage artifact Hrepresentation.
  destruct Hrepresentation as
    [_ [_ [_ [_ [_ [Hclosed _]]]]]].
  exact Hclosed.
Qed.
