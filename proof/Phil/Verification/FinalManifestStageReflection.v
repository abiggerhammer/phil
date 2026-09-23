From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import SystemsStageClosure.
From Phil.Verification Require Import VerificationArtifact.

(*
  D-ARTIFACT-MANIFEST-REFLECTION-01 — the semantic final-manifest predicate
  must be fed by the independently authoritative native manifest, not rebuilt
  from the StageClosure values that it is supposed to check.

  Native correspondence:

  - Phil.Verification.CertifiedRelease verifies the supplied AssuranceManifest
    and the supplied StageClosure independently before comparing their shared
    release coordinates.
  - Phil.Verification.VerificationArtifact.FinalManifestMatches is the proof-side
    relation for the same source-assurance and StageClosure coordinates.

  This slice makes the representation premise explicit.  Exact native checks
  imply FinalManifestMatches only when the proof-side FinalManifestFacts are an
  exact representation of that same independently supplied native manifest.
  A model manifest synthesized from stage values can satisfy the local predicate
  while failing to represent a different authoritative native manifest; that is
  why representation is an input to the correspondence theorem rather than a
  definition by construction.
*)

Record NativeFinalManifestAuthority : Type := mkNativeFinalManifestAuthority {
  nativeManifestIdentity : nat;
  nativeManifestSourceAssuranceIdentity : nat;
  nativeManifestSubjectRevision : nat;
  nativeManifestInstanceRevision : nat;
  nativeManifestRealizationRevision : nat;
  nativeManifestSystemsRevision : nat;
  nativeManifestStageContractRevision : nat;
  nativeManifestVerifierProfileRevision : nat;
  nativeManifestClosed : bool;
  nativeManifestScopeMatches : bool
}.

Definition NativeFinalManifestAccepted
  (native : NativeFinalManifestAuthority) : Prop :=
  nativeManifestIdentity native <> 0 /\
  nativeManifestClosed native = true /\
  nativeManifestScopeMatches native = true.

Definition NativeFinalManifestBoundToSourceAndStage
  (source : SourceAssuranceFacts)
  (stage : ArtifactStageContext)
  (native : NativeFinalManifestAuthority) : Prop :=
  nativeManifestSourceAssuranceIdentity native = sourceAssuranceIdentity source /\
  nativeManifestSubjectRevision native =
    closureConcreteSubjectRevision (artifactStageIdentity stage) /\
  nativeManifestInstanceRevision native =
    closureConcreteInstanceRevision (artifactStageIdentity stage) /\
  nativeManifestRealizationRevision native =
    closureConcreteRealizationRevision (artifactStageIdentity stage) /\
  nativeManifestSystemsRevision native =
    closureConcreteSystemsRevision (artifactStageIdentity stage) /\
  nativeManifestStageContractRevision native =
    closureConcreteStageContractRevision (artifactStageIdentity stage) /\
  nativeManifestVerifierProfileRevision native =
    closureConcreteVerifierProfileRevision (artifactStageIdentity stage).

Definition FinalManifestRepresentsNative
  (native : NativeFinalManifestAuthority)
  (manifest : FinalManifestFacts) : Prop :=
  finalManifestIdentity manifest = nativeManifestIdentity native /\
  finalManifestClosed manifest = nativeManifestClosed native /\
  finalManifestScopeMatches manifest = nativeManifestScopeMatches native /\
  finalManifestSourceAssuranceIdentity manifest =
    nativeManifestSourceAssuranceIdentity native /\
  finalManifestSubjectRevision manifest = nativeManifestSubjectRevision native /\
  finalManifestInstanceRevision manifest = nativeManifestInstanceRevision native /\
  finalManifestRealizationRevision manifest =
    nativeManifestRealizationRevision native /\
  finalManifestSystemsRevision manifest = nativeManifestSystemsRevision native /\
  finalManifestStageContractRevision manifest =
    nativeManifestStageContractRevision native /\
  finalManifestVerifierProfileRevision manifest =
    nativeManifestVerifierProfileRevision native.

Theorem exact_native_manifest_reflection_establishes_final_manifest_matches :
  forall source stage native manifest,
    NativeFinalManifestAccepted native ->
    NativeFinalManifestBoundToSourceAndStage source stage native ->
    FinalManifestRepresentsNative native manifest ->
    FinalManifestMatches source stage manifest.
Proof.
  intros source stage native manifest Haccepted Hbound Hrepresents.
  destruct Haccepted as [Hidentity [Hclosed Hscope]].
  destruct Hbound as
    [Hsource
      [Hsubject
        [Hinstance
          [Hrealization [Hsystems [HstageContract Hprofile]]]]]].
  destruct Hrepresents as
    [Ridentity
      [Rclosed
        [Rscope
          [Rsource
            [Rsubject
              [Rinstance
                [Rrealization [Rsystems [RstageContract Rprofile]]]]]]]]].
  unfold FinalManifestMatches.
  repeat split.
  - rewrite Ridentity. exact Hidentity.
  - rewrite Rclosed. exact Hclosed.
  - rewrite Rscope. exact Hscope.
  - rewrite Rsource. exact Hsource.
  - rewrite Rsubject. exact Hsubject.
  - rewrite Rinstance. exact Hinstance.
  - rewrite Rrealization. exact Hrealization.
  - rewrite Rsystems. exact Hsystems.
  - rewrite RstageContract. exact HstageContract.
  - rewrite Rprofile. exact Hprofile.
Qed.

Theorem exact_native_manifest_reflection_establishes_artifact_certification :
  forall source stage native manifest,
    SourceAssuranceValid source ->
    ArtifactStagePreserved stage ->
    NativeFinalManifestAccepted native ->
    NativeFinalManifestBoundToSourceAndStage source stage native ->
    FinalManifestRepresentsNative native manifest ->
    FinalArtifactCertified source stage manifest.
Proof.
  intros source stage native manifest Hsource Hstage Haccepted Hbound Hrepresents.
  apply exact_composition_certifies_artifact.
  - exact Hsource.
  - exact Hstage.
  - eapply exact_native_manifest_reflection_establishes_final_manifest_matches.
    + exact Haccepted.
    + exact Hbound.
    + exact Hrepresents.
Qed.

Theorem stage_local_match_does_not_replace_native_manifest_representation :
  forall source stage native manifest,
    FinalManifestMatches source stage manifest ->
    nativeManifestSystemsRevision native <>
      finalManifestSystemsRevision manifest ->
    ~ FinalManifestRepresentsNative native manifest.
Proof.
  intros source stage native manifest Hlocal HnativeMismatch Hrepresents.
  destruct Hrepresents as
    [_ [_ [_ [_ [_ [_ [_ [Rsystems _]]]]]]]].
  apply HnativeMismatch.
  symmetry.
  exact Rsystems.
Qed.

Theorem source_identity_drift_breaks_native_manifest_binding :
  forall source stage native,
    nativeManifestSourceAssuranceIdentity native <>
      sourceAssuranceIdentity source ->
    ~ NativeFinalManifestBoundToSourceAndStage source stage native.
Proof.
  intros source stage native Hmismatch Hbound.
  apply Hmismatch.
  exact (proj1 Hbound).
Qed.

Theorem stage_contract_drift_breaks_native_manifest_binding :
  forall source stage native,
    nativeManifestStageContractRevision native <>
      closureConcreteStageContractRevision (artifactStageIdentity stage) ->
    ~ NativeFinalManifestBoundToSourceAndStage source stage native.
Proof.
  intros source stage native Hmismatch Hbound.
  destruct Hbound as
    [_ [_ [_ [_ [_ [HstageContract _]]]]]].
  apply Hmismatch.
  exact HstageContract.
Qed.
