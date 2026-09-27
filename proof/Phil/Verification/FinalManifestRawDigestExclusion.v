From Phil.Verification Require Import
  VerificationArtifact
  FinalManifestNativeCoordinateReflection
  FinalManifestFixedAdapter.

(*
  D-ARTIFACT-MANIFEST-REFLECTION-01.

  A fixed final-authority adapter must carry the exact raw Systems digest
  equality already present in its ten-coordinate correspondence record.
  Therefore an explicitly unequal manifest implementation digest and supplied
  stage raw Systems digest excludes the adapter.

  This is a conditional model result.  It does not synthesize native
  acceptance, identify normalized Systems revisions with raw digests, or
  discharge SourceAssuranceValid / ArtifactStagePreserved predecessors.
*)

Theorem unequal_raw_systems_digest_excludes_fixed_adapter :
  forall source artifact manifest stage,
    releaseImplementationDigest manifest <> releaseRawSystemsDigest stage ->
    ~ FixedFinalAuthorityAdapter source artifact manifest stage.
Proof.
  intros source artifact manifest stage Hneq Hadapter.
  apply Hneq.
  destruct Hadapter as [_ Hdigest _ _ _ _ _ _ _ _].
  exact Hdigest.
Qed.
