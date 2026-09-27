From Phil.Verification Require Import
  VerificationArtifact
  FinalManifestNativeCoordinateReflection
  FinalManifestFixedAdapter.

(*
  D-ARTIFACT-MANIFEST-REFLECTION-01.

  The fixed final-authority adapter establishes the final-manifest correspondence
  needed by artifact certification, but it does not replace the independently
  required source-assurance and exact-stage-preservation predecessors.

  This is a conditional model composition result. It does not synthesize native
  acceptance, discharge SourceAssuranceValid or ArtifactStagePreserved, identify
  raw Systems digests with normalized Systems revisions, or broaden the Phase 1
  trusted computing base.
*)

Theorem fixed_adapter_full_certification_preserves_predecessors :
  forall source artifact manifest stage final,
    SourceAssuranceValid source ->
    ArtifactStagePreserved artifact ->
    NativeReleaseManifestAccepted manifest ->
    FixedFinalAuthorityAdapter source artifact manifest stage ->
    FinalManifestRepresentsRelease manifest stage final ->
    FinalArtifactCertified source artifact final.
Proof.
  intros source artifact manifest stage final
    Hsource Hstage Haccepted Hadapter Hrepresents.
  apply exact_composition_certifies_artifact.
  - exact Hsource.
  - exact Hstage.
  - eapply fixed_adapter_establishes_final_manifest_match.
    + exact Haccepted.
    + exact Hadapter.
    + exact Hrepresents.
Qed.
