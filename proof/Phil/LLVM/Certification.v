From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Assurance Require Import Manifest EvidenceUse.
From Phil.LLVM Require Import Identity Preservation Strengthening.

(*
  PHIL-LLVM-CERT-001 — composition theorem for the concrete Phase 0
  Systems -> pre-optimization LLVM certification boundary.

  The component proof modules establish the authority-relevant contracts of
  Phil.LLVM.Verify and Phil.Assurance.Verify:

  - Identity.v: exact source/target/text/target-profile/runtime-ABI/profile
    binding;
  - Preservation.v: source re-verification and preservation of runtime sites,
    ordinary projection, control witnesses, and trace/resource relations;
  - Strengthening.v: explicit strengthening authority and defined-execution
    discipline;
  - EvidenceUse.v: TranslationValidated is artifact-backed and cannot gain
    authority from a missing or mismatched trusted artifact;
  - Manifest.v: an in-scope certification revision is locally accepted and
    cannot be silently exported.

  LLVM assembler acceptance is intentionally represented as an external gate.
  Rocq proves that certification requires that gate; it does not claim to have
  executed LLVM or proved LLVM's implementation correct.  Concrete SHA-256,
  Text/Map/Set correspondence, the Haskell-to-normalized-model correspondence,
  and LLVM 18 itself remain the explicit TCB boundaries recorded in the logic
  ledger.
*)

Record Phase0CertificationModel : Type := mkPhase0CertificationModel {
  certificationIdentity : LLVMIdentityModel;
  certificationPreservation : LLVMPreservationModel;
  certificationStrengthening : StrengtheningEnvironment;
  certificationArtifactAuthority : ArtifactAuthority;
  certificationScopeModel : ScopeModel;
  certificationRevision : RevisionId;
  certificationLLVM18Accepted : bool
}.

Definition Phase0CertificationSuccess
  (model : Phase0CertificationModel) : Prop :=
  LLVMIdentityVerificationSuccess (certificationIdentity model) /\
  LLVMPreservationVerificationSuccess (certificationPreservation model) /\
  StrengtheningVerificationSuccess (certificationStrengthening model) /\
  verifyArtifactAuthority (certificationArtifactAuthority model) = GateAccepted /\
  CertificationClosure (certificationScopeModel model) /\
  certificationScope
    (certificationScopeModel model) (certificationRevision model) = true /\
  certificationLLVM18Accepted model = true.

Theorem phase0_certification_requires_exact_translation_and_external_llvm_gate :
  forall model,
    Phase0CertificationSuccess model ->
    identityContractSourceDigest (certificationIdentity model) =
      identityExpectedSourceDigest (certificationIdentity model) /\
    identityContractTargetDigest (certificationIdentity model) =
      identityComputedTargetDigest (certificationIdentity model) /\
    identityStoredArtifactText (certificationIdentity model) =
      identityRenderedText (certificationIdentity model) /\
    (identityActualLanguageVersion (certificationIdentity model) =
       identityExpectedLanguageVersion (certificationIdentity model) /\
     identityActualToolVersion (certificationIdentity model) =
       identityExpectedToolVersion (certificationIdentity model) /\
     identityActualTargetTriple (certificationIdentity model) =
       identityExpectedTargetTriple (certificationIdentity model) /\
     identityActualDataLayout (certificationIdentity model) =
       identityExpectedDataLayout (certificationIdentity model)) /\
    (identityActualRuntimeABIDigest (certificationIdentity model) =
       identityExpectedRuntimeABIDigest (certificationIdentity model) /\
     identityActualRuntimeABIProfile (certificationIdentity model) =
       identityExpectedRuntimeABIProfile (certificationIdentity model)) /\
    identityActualCompilationProfile (certificationIdentity model) =
      identityExpectedCompilationProfile (certificationIdentity model) /\
    preservationSystemsSourceReverified (certificationPreservation model) = true /\
    (forall site,
      preservationSourceRuntimeCount (certificationPreservation model) site =
      preservationTargetRuntimeCount (certificationPreservation model) site) /\
    (preservationTargetTraceRelation (certificationPreservation model) =
       preservationSourceTraceRelation (certificationPreservation model) /\
     preservationTargetResourceFailureRelation (certificationPreservation model) =
       preservationSourceResourceFailureRelation (certificationPreservation model)) /\
    artifactDeclared (certificationArtifactAuthority model) = true /\
    artifactIdentityMatches (certificationArtifactAuthority model) = true /\
    artifactDigestMatchesTrustedAvailability
      (certificationArtifactAuthority model) = true /\
    revisionDisposition
      (certificationScopeModel model) (certificationRevision model) =
      LocallyAccepted /\
    strengtheningPoisonPresent (certificationStrengthening model) = false /\
    strengtheningUndefPresent (certificationStrengthening model) = false /\
    strengtheningFreezePresent (certificationStrengthening model) = false /\
    strengtheningUnjustifiedUnreachablePresent
      (certificationStrengthening model) = false /\
    certificationLLVM18Accepted model = true.
Proof.
  intros model Hcertified.
  destruct Hcertified as
    [Hidentity [Hpreservation [Hstrengthening [Hartifact [Hclosure [Hscope Hllvm]]]]]].

  pose proof
    (verified_llvm_source_digest_is_exact
      (certificationIdentity model) Hidentity) as Hsource.
  pose proof
    (verified_llvm_target_digest_is_exact
      (certificationIdentity model) Hidentity) as Htarget.
  pose proof
    (verified_llvm_artifact_text_is_renderer_output
      (certificationIdentity model) Hidentity) as Htext.
  pose proof
    (verified_llvm_target_profile_is_exact
      (certificationIdentity model) Hidentity) as HtargetProfile.
  pose proof
    (verified_llvm_runtime_abi_is_exact
      (certificationIdentity model) Hidentity) as HruntimeABI.
  pose proof
    (verified_llvm_compilation_profile_is_exact
      (certificationIdentity model) Hidentity) as HcompilationProfile.
  pose proof
    (verified_llvm_rechecks_source_systems_artifact
      (certificationPreservation model) Hpreservation) as HsourceReverified.
  assert (HruntimeSites : forall site,
    preservationSourceRuntimeCount (certificationPreservation model) site =
    preservationTargetRuntimeCount (certificationPreservation model) site).
  {
    intro site.
    eapply verified_llvm_preserves_runtime_site_multiplicity.
    exact Hpreservation.
  }
  pose proof
    (verified_llvm_preserves_contract_relations
      (certificationPreservation model) Hpreservation) as Hrelations.
  pose proof
    (successful_artifact_authority_is_exact
      (certificationArtifactAuthority model) Hartifact) as HartifactExact.
  pose proof
    (in_scope_revision_is_locally_accepted
      (certificationScopeModel model)
      (certificationRevision model)
      Hclosure Hscope) as HlocallyAccepted.

  destruct HtargetProfile as [Hlanguage [Htool [Htriple Hlayout]]].
  destruct HruntimeABI as [HabiDigest HabiProfile].
  destruct Hrelations as [Htrace Hresource].
  destruct HartifactExact as [HartifactDeclared [HartifactIdentity HartifactDigest]].
  destruct Hstrengthening as
    [_ [_ [Hpoison [Hundef [Hfreeze Hunreachable]]]]].

  repeat split; assumption.
Qed.

Theorem phase0_certification_cannot_succeed_without_llvm18_acceptance :
  forall model,
    certificationLLVM18Accepted model = false ->
    ~ Phase0CertificationSuccess model.
Proof.
  intros model HllvmRejected Hcertified.
  destruct Hcertified as [_ [_ [_ [_ [_ [_ HllvmAccepted]]]]]].
  rewrite HllvmRejected in HllvmAccepted.
  discriminate.
Qed.

Theorem phase0_certification_cannot_succeed_with_mismatched_translation_artifact :
  forall model,
    artifactDigestMatchesTrustedAvailability
      (certificationArtifactAuthority model) = false ->
    ~ Phase0CertificationSuccess model.
Proof.
  intros model Hmismatch Hcertified.
  destruct Hcertified as [_ [_ [_ [Hartifact _]]]].
  pose proof
    (successful_artifact_authority_is_exact
      (certificationArtifactAuthority model) Hartifact) as Hexact.
  destruct Hexact as [_ [_ Hdigest]].
  rewrite Hmismatch in Hdigest.
  discriminate.
Qed.
