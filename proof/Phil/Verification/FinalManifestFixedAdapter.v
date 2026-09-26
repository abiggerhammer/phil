From Phil.Verification Require Import
  VerificationArtifact
  FinalManifestStageReflection
  FinalManifestNativeCoordinateReflection.

(*
  D-ARTIFACT-MANIFEST-REFLECTION-01.
  A supplied Phase-1 final-authority adapter is useful only when its source,
  native manifest, native stage, and proof-side stage coordinates agree exactly.
  This record is an explicit correspondence premise, not an extraction from
  Haskell and not a Boolean trust shortcut.
*)

Record FixedFinalAuthorityAdapter
  (source : SourceAssuranceFacts)
  (artifact : ArtifactStageContext)
  (manifest : NativeReleaseManifest)
  (stage : NativeReleaseStage) : Prop :=
  mkFixedFinalAuthorityAdapter {
    adapterSource :
      releaseSourceAssuranceIdentity manifest = sourceAssuranceIdentity source;
    adapterDigest :
      releaseImplementationDigest manifest = releaseRawSystemsDigest stage;
    adapterRoot :
      releaseLoweringRoot manifest = releaseStageLoweringRoot stage;
    adapterSubject :
      releaseSubjectRevision stage =
        closureConcreteSubjectRevision (artifactStageIdentity artifact);
    adapterInstance :
      releaseInstanceRevision stage =
        closureConcreteInstanceRevision (artifactStageIdentity artifact);
    adapterRealization :
      releaseRealizationRevision stage =
        closureConcreteRealizationRevision (artifactStageIdentity artifact);
    adapterSystems :
      releaseNormalizedSystemsRevision stage =
        closureConcreteSystemsRevision (artifactStageIdentity artifact);
    adapterStageContract :
      releaseCommonStageContractRevision stage =
        closureConcreteStageContractRevision (artifactStageIdentity artifact);
    adapterClosedStage :
      releaseClosedStageContractRevision stage =
        closureStoredFinalRevision (artifactStageIdentity artifact);
    adapterProfile :
      releaseVerifierProfileRevision stage =
        closureConcreteVerifierProfileRevision (artifactStageIdentity artifact)
  }.

Lemma fixed_adapter_release_bound :
  forall source artifact manifest stage,
    FixedFinalAuthorityAdapter source artifact manifest stage ->
    NativeReleaseBound source manifest stage.
Proof.
  intros source artifact manifest stage H.
  destruct H as [Hs Hd Hr _ _ _ _ _ _ _].
  unfold NativeReleaseBound.
  repeat split; assumption.
Qed.

Lemma fixed_adapter_stage_represents :
  forall source artifact manifest stage,
    FixedFinalAuthorityAdapter source artifact manifest stage ->
    NativeReleaseStageRepresents stage artifact.
Proof.
  intros source artifact manifest stage H.
  destruct H as [_ _ _ Hs Hi Hr Hsys Hc Hf Hp].
  unfold NativeReleaseStageRepresents.
  repeat split; assumption.
Qed.

Theorem fixed_adapter_establishes_final_manifest_match :
  forall source artifact manifest stage final,
    NativeReleaseManifestAccepted manifest ->
    FixedFinalAuthorityAdapter source artifact manifest stage ->
    FinalManifestRepresentsRelease manifest stage final ->
    FinalManifestMatches source artifact final.
Proof.
  intros source artifact manifest stage final Haccepted Hadapter Hrepresents.
  eapply exact_native_release_coordinates_establish_manifest_match
    with (m := manifest) (s := stage).
  - exact Haccepted.
  - eapply fixed_adapter_release_bound; exact Hadapter.
  - eapply fixed_adapter_stage_represents; exact Hadapter.
  - exact Hrepresents.
Qed.

Theorem fixed_adapter_source_identity_is_exact :
  forall source artifact manifest stage,
    FixedFinalAuthorityAdapter source artifact manifest stage ->
    releaseSourceAssuranceIdentity manifest = sourceAssuranceIdentity source.
Proof.
  intros source artifact manifest stage H.
  now destruct H.
Qed.

Theorem fixed_adapter_stage_subject_is_exact :
  forall source artifact manifest stage,
    FixedFinalAuthorityAdapter source artifact manifest stage ->
    releaseSubjectRevision stage =
      closureConcreteSubjectRevision (artifactStageIdentity artifact).
Proof.
  intros source artifact manifest stage H.
  now destruct H.
Qed.
