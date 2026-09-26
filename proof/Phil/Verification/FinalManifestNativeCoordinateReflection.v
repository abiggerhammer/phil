From Stdlib Require Import Bool.Bool.
From Phil.Core Require Import SystemsStageClosure.
From Phil.Verification Require Import VerificationArtifact FinalManifestStageReflection.

(*
  D-ARTIFACT-MANIFEST-REFLECTION-01.
  Keep the native release manifest's raw Systems digest separate from the
  normalized Systems revision used by the semantic stage model, and keep the
  common Phase-1 StageContract revision separate from the final closed-stage
  revision.
*)

Record NativeReleaseManifest : Type := mkNativeReleaseManifest {
  releaseManifestIdentity : nat;
  releaseSourceAssuranceIdentity : nat;
  releaseImplementationDigest : nat;
  releaseLoweringRoot : nat;
  releaseManifestClosed : bool;
  releaseManifestScopeMatches : bool
}.

Record NativeReleaseStage : Type := mkNativeReleaseStage {
  releaseRawSystemsDigest : nat;
  releaseStageLoweringRoot : nat;
  releaseSubjectRevision : nat;
  releaseInstanceRevision : nat;
  releaseRealizationRevision : nat;
  releaseNormalizedSystemsRevision : nat;
  releaseCommonStageContractRevision : nat;
  releaseClosedStageContractRevision : nat;
  releaseVerifierProfileRevision : nat
}.

Definition NativeReleaseManifestAccepted (m : NativeReleaseManifest) : Prop :=
  releaseManifestIdentity m <> 0 /\
  releaseManifestClosed m = true /\
  releaseManifestScopeMatches m = true.

Definition NativeReleaseBound
  (source : SourceAssuranceFacts)
  (m : NativeReleaseManifest)
  (s : NativeReleaseStage) : Prop :=
  releaseSourceAssuranceIdentity m = sourceAssuranceIdentity source /\
  releaseImplementationDigest m = releaseRawSystemsDigest s /\
  releaseLoweringRoot m = releaseStageLoweringRoot s.

Definition NativeReleaseStageRepresents
  (s : NativeReleaseStage)
  (artifact : ArtifactStageContext) : Prop :=
  releaseSubjectRevision s =
    closureConcreteSubjectRevision (artifactStageIdentity artifact) /\
  releaseInstanceRevision s =
    closureConcreteInstanceRevision (artifactStageIdentity artifact) /\
  releaseRealizationRevision s =
    closureConcreteRealizationRevision (artifactStageIdentity artifact) /\
  releaseNormalizedSystemsRevision s =
    closureConcreteSystemsRevision (artifactStageIdentity artifact) /\
  releaseCommonStageContractRevision s =
    closureConcreteStageContractRevision (artifactStageIdentity artifact) /\
  releaseClosedStageContractRevision s =
    closureStoredFinalRevision (artifactStageIdentity artifact) /\
  releaseVerifierProfileRevision s =
    closureConcreteVerifierProfileRevision (artifactStageIdentity artifact).

Definition FinalManifestRepresentsRelease
  (m : NativeReleaseManifest)
  (s : NativeReleaseStage)
  (final : FinalManifestFacts) : Prop :=
  finalManifestIdentity final = releaseManifestIdentity m /\
  finalManifestClosed final = releaseManifestClosed m /\
  finalManifestScopeMatches final = releaseManifestScopeMatches m /\
  finalManifestSourceAssuranceIdentity final = releaseSourceAssuranceIdentity m /\
  finalManifestSubjectRevision final = releaseSubjectRevision s /\
  finalManifestInstanceRevision final = releaseInstanceRevision s /\
  finalManifestRealizationRevision final = releaseRealizationRevision s /\
  finalManifestSystemsRevision final = releaseNormalizedSystemsRevision s /\
  finalManifestStageContractRevision final =
    releaseCommonStageContractRevision s /\
  finalManifestVerifierProfileRevision final = releaseVerifierProfileRevision s.

Definition projectReleaseAuthority
  (m : NativeReleaseManifest) (s : NativeReleaseStage)
  : NativeFinalManifestAuthority :=
  mkNativeFinalManifestAuthority
    (releaseManifestIdentity m)
    (releaseSourceAssuranceIdentity m)
    (releaseSubjectRevision s)
    (releaseInstanceRevision s)
    (releaseRealizationRevision s)
    (releaseNormalizedSystemsRevision s)
    (releaseCommonStageContractRevision s)
    (releaseVerifierProfileRevision s)
    (releaseManifestClosed m)
    (releaseManifestScopeMatches m).

Lemma accepted_projection :
  forall m s,
    NativeReleaseManifestAccepted m ->
    NativeFinalManifestAccepted (projectReleaseAuthority m s).
Proof.
  intros m s [Hid [Hclosed Hscope]].
  unfold NativeFinalManifestAccepted, projectReleaseAuthority; simpl.
  repeat split; assumption.
Qed.

Lemma bound_projection :
  forall source m s artifact,
    NativeReleaseBound source m s ->
    NativeReleaseStageRepresents s artifact ->
    NativeFinalManifestBoundToSourceAndStage
      source artifact (projectReleaseAuthority m s).
Proof.
  intros source m s artifact [Hsource _] Hstage.
  destruct Hstage as
    [Hsub [Hinst [Hreal [Hsys [Hcommon [_ Hprofile]]]]]].
  unfold NativeFinalManifestBoundToSourceAndStage, projectReleaseAuthority; simpl.
  repeat split; assumption.
Qed.

Lemma represented_projection :
  forall m s final,
    FinalManifestRepresentsRelease m s final ->
    FinalManifestRepresentsNative (projectReleaseAuthority m s) final.
Proof.
  intros m s final H.
  unfold FinalManifestRepresentsRelease in H.
  unfold FinalManifestRepresentsNative, projectReleaseAuthority; simpl.
  exact H.
Qed.

Theorem exact_native_release_coordinates_establish_manifest_match :
  forall source artifact m s final,
    NativeReleaseManifestAccepted m ->
    NativeReleaseBound source m s ->
    NativeReleaseStageRepresents s artifact ->
    FinalManifestRepresentsRelease m s final ->
    FinalManifestMatches source artifact final.
Proof.
  intros source artifact m s final Haccepted Hbound Hstage Hrep.
  eapply exact_native_manifest_reflection_establishes_final_manifest_matches
    with (native := projectReleaseAuthority m s).
  - now apply accepted_projection.
  - now apply bound_projection.
  - now apply represented_projection.
Qed.

Theorem raw_digest_cannot_replace_normalized_systems_revision :
  forall m s final,
    releaseRawSystemsDigest s <> releaseNormalizedSystemsRevision s ->
    finalManifestSystemsRevision final = releaseRawSystemsDigest s ->
    ~ FinalManifestRepresentsRelease m s final.
Proof.
  intros m s final Hneq Hraw Hrep.
  destruct Hrep as [_ [_ [_ [_ [_ [_ [_ [Hnorm _]]]]]]]].
  rewrite Hraw in Hnorm.
  now apply Hneq.
Qed.

Theorem closed_stage_cannot_replace_common_stage_contract :
  forall m s final,
    releaseClosedStageContractRevision s <>
      releaseCommonStageContractRevision s ->
    finalManifestStageContractRevision final =
      releaseClosedStageContractRevision s ->
    ~ FinalManifestRepresentsRelease m s final.
Proof.
  intros m s final Hneq Hclosed Hrep.
  destruct Hrep as [_ [_ [_ [_ [_ [_ [_ [_ [Hcommon _]]]]]]]]].
  rewrite Hclosed in Hcommon.
  now apply Hneq.
Qed.

Theorem release_digest_drift_breaks_binding :
  forall source m s,
    releaseImplementationDigest m <> releaseRawSystemsDigest s ->
    ~ NativeReleaseBound source m s.
Proof.
  intros source m s Hneq [_ [Heq _]].
  now apply Hneq.
Qed.

Theorem release_lowering_root_drift_breaks_binding :
  forall source m s,
    releaseLoweringRoot m <> releaseStageLoweringRoot s ->
    ~ NativeReleaseBound source m s.
Proof.
  intros source m s Hneq [_ [_ Heq]].
  now apply Hneq.
Qed.
