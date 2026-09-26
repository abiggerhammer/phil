From Phil.Verification Require Import
  VerificationArtifact
  FinalManifestStageReflection
  FinalManifestNativeCoordinateReflection
  FinalManifestFixedAdapter.

(*
  D-ARTIFACT-MANIFEST-REFLECTION-01.
  The fixed final-authority adapter is exactly the conjunction of the two
  pre-existing release-coordinate relations.  This rules out treating the
  adapter as either weaker or stronger than those explicit correspondence
  premises; it does not synthesize native authority or discharge the outer
  SourceAssuranceValid / ArtifactStagePreserved predecessors.
*)

Theorem fixed_adapter_iff_native_release_relations :
  forall source artifact manifest stage,
    FixedFinalAuthorityAdapter source artifact manifest stage <->
    NativeReleaseBound source manifest stage /\
    NativeReleaseStageRepresents stage artifact.
Proof.
  intros source artifact manifest stage; split.
  - intro H; split.
    + eapply fixed_adapter_release_bound; exact H.
    + eapply fixed_adapter_stage_represents; exact H.
  - intros [Hbound Hrepresents].
    destruct Hbound as [Hsource [Hdigest Hroot]].
    destruct Hrepresents as [Hsubject [Hinstance [Hrealization
      [Hsystems [Hcontract [Hclosed Hprofile]]]]]].
    constructor; assumption.
Qed.
