From Phil.Verification Require Import
  VerificationArtifact FinalManifestStageReflection
  FinalManifestNativeCoordinateReflection FinalManifestFixedAdapter.

(* Independent review of the exact existing predicates. No native object is
   synthesized here and no Boolean is asserted to stand for native acceptance.
   These are conditional model results, not Haskell extraction or execution. *)

Theorem audit_adapter_iff_existing_relations :
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

Theorem audit_unequal_raw_digest_excludes_adapter :
  forall source artifact manifest stage,
    releaseImplementationDigest manifest <> releaseRawSystemsDigest stage ->
    ~ FixedFinalAuthorityAdapter source artifact manifest stage.
Proof.
  intros source artifact manifest stage Hneq Hadapter.
  apply Hneq.
  destruct Hadapter as [_ Hdigest _ _ _ _ _ _ _ _].
  exact Hdigest.
Qed.

Theorem audit_full_certification_keeps_predecessors :
  forall source artifact manifest stage final,
    SourceAssuranceValid source ->
    ArtifactStagePreserved artifact ->
    NativeReleaseManifestAccepted manifest ->
    FixedFinalAuthorityAdapter source artifact manifest stage ->
    FinalManifestRepresentsRelease manifest stage final ->
    FinalArtifactCertified source artifact final.
Proof.
  intros source artifact manifest stage final Hsource Hstage Haccepted Hadapter Hrep.
  apply exact_composition_certifies_artifact.
  - exact Hsource.
  - exact Hstage.
  - eapply fixed_adapter_establishes_final_manifest_match.
    + exact Haccepted.
    + exact Hadapter.
    + exact Hrep.
Qed.

Print Assumptions fixed_adapter_release_bound.
Print Assumptions fixed_adapter_stage_represents.
Print Assumptions fixed_adapter_establishes_final_manifest_match.
Print Assumptions fixed_adapter_source_identity_is_exact.
Print Assumptions fixed_adapter_stage_subject_is_exact.
Print Assumptions audit_adapter_iff_existing_relations.
Print Assumptions audit_unequal_raw_digest_excludes_adapter.
Print Assumptions audit_full_certification_keeps_predecessors.
