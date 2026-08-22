From Stdlib Require Import Arith.PeanoNat.

(*
  PHIL-LLVM-ID-001 — proof-oriented model of the exact identity gates in
  Phil.LLVM.Verify.verifyIdentity.

  Digests, rendered text, target-profile fields, runtime-ABI identity, and the
  compilation profile are represented by opaque identifiers.  Concrete Text
  serialization and SHA-256 remain implementation / cryptographic
  correspondence boundaries.  The theorem target is the verifier's authority
  rule: successful LLVM verification admits no source, target, text, profile,
  ABI, or compilation-profile drift.
*)

Definition DigestId := nat.
Definition TextId := nat.
Definition ProfileId := nat.

Record LLVMIdentityModel : Type := mkLLVMIdentityModel {
  identityExpectedSourceDigest : DigestId;
  identityContractSourceDigest : DigestId;
  identityComputedTargetDigest : DigestId;
  identityContractTargetDigest : DigestId;
  identityRenderedText : TextId;
  identityStoredArtifactText : TextId;
  identityExpectedLanguageVersion : TextId;
  identityActualLanguageVersion : TextId;
  identityExpectedToolVersion : TextId;
  identityActualToolVersion : TextId;
  identityExpectedTargetTriple : TextId;
  identityActualTargetTriple : TextId;
  identityExpectedDataLayout : TextId;
  identityActualDataLayout : TextId;
  identityExpectedRuntimeABIDigest : DigestId;
  identityActualRuntimeABIDigest : DigestId;
  identityExpectedRuntimeABIProfile : TextId;
  identityActualRuntimeABIProfile : TextId;
  identityExpectedCompilationProfile : ProfileId;
  identityActualCompilationProfile : ProfileId
}.

Definition LLVMIdentityVerificationSuccess (model : LLVMIdentityModel) : Prop :=
  identityContractSourceDigest model = identityExpectedSourceDigest model /\
  identityContractTargetDigest model = identityComputedTargetDigest model /\
  identityStoredArtifactText model = identityRenderedText model /\
  identityActualLanguageVersion model = identityExpectedLanguageVersion model /\
  identityActualToolVersion model = identityExpectedToolVersion model /\
  identityActualTargetTriple model = identityExpectedTargetTriple model /\
  identityActualDataLayout model = identityExpectedDataLayout model /\
  identityActualRuntimeABIDigest model = identityExpectedRuntimeABIDigest model /\
  identityActualRuntimeABIProfile model = identityExpectedRuntimeABIProfile model /\
  identityActualCompilationProfile model = identityExpectedCompilationProfile model.

Theorem verified_llvm_source_digest_is_exact :
  forall model,
    LLVMIdentityVerificationSuccess model ->
    identityContractSourceDigest model = identityExpectedSourceDigest model.
Proof.
  intros model Hverified.
  destruct Hverified as [Hsource _].
  exact Hsource.
Qed.

Theorem verified_llvm_target_digest_is_exact :
  forall model,
    LLVMIdentityVerificationSuccess model ->
    identityContractTargetDigest model = identityComputedTargetDigest model.
Proof.
  intros model Hverified.
  destruct Hverified as [_ [Htarget _]].
  exact Htarget.
Qed.

Theorem verified_llvm_artifact_text_is_renderer_output :
  forall model,
    LLVMIdentityVerificationSuccess model ->
    identityStoredArtifactText model = identityRenderedText model.
Proof.
  intros model Hverified.
  destruct Hverified as [_ [_ [Htext _]]].
  exact Htext.
Qed.

Theorem verified_llvm_target_profile_is_exact :
  forall model,
    LLVMIdentityVerificationSuccess model ->
    identityActualLanguageVersion model = identityExpectedLanguageVersion model /\
    identityActualToolVersion model = identityExpectedToolVersion model /\
    identityActualTargetTriple model = identityExpectedTargetTriple model /\
    identityActualDataLayout model = identityExpectedDataLayout model.
Proof.
  intros model Hverified.
  destruct Hverified as [_ [_ [_ [Hlanguage [Htool [Htriple [Hlayout _]]]]]]].
  repeat split; assumption.
Qed.

Theorem verified_llvm_runtime_abi_is_exact :
  forall model,
    LLVMIdentityVerificationSuccess model ->
    identityActualRuntimeABIDigest model = identityExpectedRuntimeABIDigest model /\
    identityActualRuntimeABIProfile model = identityExpectedRuntimeABIProfile model.
Proof.
  intros model Hverified.
  destruct Hverified as
    [_ [_ [_ [_ [_ [_ [_ [Hdigest [Hprofile _]]]]]]]]].
  split; assumption.
Qed.

Theorem verified_llvm_compilation_profile_is_exact :
  forall model,
    LLVMIdentityVerificationSuccess model ->
    identityActualCompilationProfile model = identityExpectedCompilationProfile model.
Proof.
  intros model Hverified.
  destruct Hverified as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ Hprofile]]]]]]]]].
  exact Hprofile.
Qed.

Theorem source_digest_drift_is_rejected :
  forall model,
    identityContractSourceDigest model <> identityExpectedSourceDigest model ->
    ~ LLVMIdentityVerificationSuccess model.
Proof.
  intros model Hdrift Hverified.
  apply Hdrift.
  apply verified_llvm_source_digest_is_exact.
  exact Hverified.
Qed.

Theorem target_digest_drift_is_rejected :
  forall model,
    identityContractTargetDigest model <> identityComputedTargetDigest model ->
    ~ LLVMIdentityVerificationSuccess model.
Proof.
  intros model Hdrift Hverified.
  apply Hdrift.
  apply verified_llvm_target_digest_is_exact.
  exact Hverified.
Qed.

Theorem artifact_text_tampering_is_rejected :
  forall model,
    identityStoredArtifactText model <> identityRenderedText model ->
    ~ LLVMIdentityVerificationSuccess model.
Proof.
  intros model Htampered Hverified.
  apply Htampered.
  apply verified_llvm_artifact_text_is_renderer_output.
  exact Hverified.
Qed.

Theorem target_triple_drift_is_rejected :
  forall model,
    identityActualTargetTriple model <> identityExpectedTargetTriple model ->
    ~ LLVMIdentityVerificationSuccess model.
Proof.
  intros model Hdrift Hverified.
  pose proof (verified_llvm_target_profile_is_exact model Hverified) as Hprofile.
  destruct Hprofile as [_ [_ [Htriple _]]].
  contradiction.
Qed.
