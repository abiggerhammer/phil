From Stdlib Require Import Arith.PeanoNat.

(*
  PHIL-SYS-ID-001 — proof-oriented model of the identity gates in
  Phil.Systems.Verify.

  Digests are intentionally opaque values here.  The theorem establishes that
  successful verification requires all authority-bearing identity equalities;
  it does not claim collision resistance or injectivity of the concrete
  serialization/hash functions.
*)

Definition Digest := nat.
Definition DecisionId := nat.

Record ArtifactIdentityModel : Type := mkArtifactIdentityModel {
  trustedSourceArtifact : Digest;
  stageSourceArtifact : Digest;
  computedSystemsProgram : Digest;
  stageTargetArtifact : Digest;
  computedSystemsArtifact : Digest;
  manifestImplementationArtifact : Digest;
  computedLoweringRoot : Digest;
  declaredLoweringRoot : Digest;
  manifestLoweringRoot : Digest
}.

Definition ArtifactIdentityVerified (model : ArtifactIdentityModel) : Prop :=
  stageSourceArtifact model = trustedSourceArtifact model /\
  stageTargetArtifact model = computedSystemsProgram model /\
  manifestImplementationArtifact model = computedSystemsArtifact model /\
  declaredLoweringRoot model = computedLoweringRoot model /\
  manifestLoweringRoot model = declaredLoweringRoot model.

Theorem verified_source_is_exact_trusted_source :
  forall model,
    ArtifactIdentityVerified model ->
    stageSourceArtifact model = trustedSourceArtifact model.
Proof.
  intros model Hverified.
  destruct Hverified as [Hsource _].
  exact Hsource.
Qed.

Theorem verified_target_is_exact_program_digest :
  forall model,
    ArtifactIdentityVerified model ->
    stageTargetArtifact model = computedSystemsProgram model.
Proof.
  intros model Hverified.
  destruct Hverified as [_ [Htarget _]].
  exact Htarget.
Qed.

Theorem verified_manifest_binds_complete_systems_artifact :
  forall model,
    ArtifactIdentityVerified model ->
    manifestImplementationArtifact model = computedSystemsArtifact model.
Proof.
  intros model Hverified.
  destruct Hverified as [_ [_ [Himplementation _]]].
  exact Himplementation.
Qed.

Theorem verified_manifest_lowering_root_is_recomputed_root :
  forall model,
    ArtifactIdentityVerified model ->
    manifestLoweringRoot model = computedLoweringRoot model.
Proof.
  intros model Hverified.
  destruct Hverified as [_ [_ [_ [Hdeclared Hmanifest]]]].
  rewrite Hmanifest.
  exact Hdeclared.
Qed.

Record DecisionBinding : Type := mkDecisionBinding {
  decisionMapKey : DecisionId;
  decisionStableId : DecisionId;
  decisionDeclaredDigest : Digest;
  decisionComputedDigest : Digest;
  decisionSourceArtifact : Digest;
  decisionTargetArtifact : Digest
}.

Definition DecisionBindingVerified
  (source target : Digest)
  (decision : DecisionBinding) : Prop :=
  decisionMapKey decision <> 0 /\
  decisionMapKey decision = decisionStableId decision /\
  decisionDeclaredDigest decision = decisionComputedDigest decision /\
  decisionSourceArtifact decision = source /\
  decisionTargetArtifact decision = target.

Theorem verified_decision_has_nonempty_stable_identity :
  forall source target decision,
    DecisionBindingVerified source target decision ->
    decisionMapKey decision <> 0.
Proof.
  intros source target decision Hverified.
  destruct Hverified as [Hnonempty _].
  exact Hnonempty.
Qed.

Theorem verified_decision_key_matches_embedded_identity :
  forall source target decision,
    DecisionBindingVerified source target decision ->
    decisionMapKey decision = decisionStableId decision.
Proof.
  intros source target decision Hverified.
  destruct Hverified as [_ [Hidentity _]].
  exact Hidentity.
Qed.

Theorem verified_decision_digest_is_recomputed_digest :
  forall source target decision,
    DecisionBindingVerified source target decision ->
    decisionDeclaredDigest decision = decisionComputedDigest decision.
Proof.
  intros source target decision Hverified.
  destruct Hverified as [_ [_ [Hdigest _]]].
  exact Hdigest.
Qed.

Theorem verified_decision_is_bound_to_stage_artifacts :
  forall source target decision,
    DecisionBindingVerified source target decision ->
    decisionSourceArtifact decision = source /\
    decisionTargetArtifact decision = target.
Proof.
  intros source target decision Hverified.
  destruct Hverified as [_ [_ [_ [Hsource Htarget]]]].
  split; assumption.
Qed.

Theorem verified_decision_is_bound_end_to_end :
  forall model decision,
    ArtifactIdentityVerified model ->
    DecisionBindingVerified
      (stageSourceArtifact model)
      (stageTargetArtifact model)
      decision ->
    decisionSourceArtifact decision = trustedSourceArtifact model /\
    decisionTargetArtifact decision = computedSystemsProgram model.
Proof.
  intros model decision Hartifact Hdecision.
  destruct Hartifact as [Hsource [Htarget _]].
  destruct Hdecision as [_ [_ [_ [HdecisionSource HdecisionTarget]]]].
  split.
  - rewrite HdecisionSource. exact Hsource.
  - rewrite HdecisionTarget. exact Htarget.
Qed.
