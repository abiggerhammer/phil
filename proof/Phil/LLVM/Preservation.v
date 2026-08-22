From Stdlib Require Import Arith.PeanoNat Bool.Bool.

(*
  PHIL-LLVM-PRESERVE-001 — proof-oriented model of the conservative
  translation-preservation checks in Phil.LLVM.Verify.

  Concrete Map/list enumeration, edge-path extraction, and correspondence to
  Phil.LLVM.Lower.lowerSystemsConservative remain implementation boundaries.
  The normalized model proves the authority-relevant acceptance contract:
  source Systems verification is mandatory; runtime-site multiplicities are
  exact; ordinary operations and terminators match the conservative lowering;
  every source edge has exactly one connected witness and non-source edges have
  no witness; every target edge is witnessed; and trace/resource-failure
  relations are unchanged.
*)

Definition RuntimeSiteId := nat.
Definition BlockId := nat.
Definition SourceEdgeId := nat.
Definition TargetEdgeId := nat.
Definition ProjectionDigest := nat.
Definition RelationId := nat.

Record LLVMPreservationModel : Type := mkLLVMPreservationModel {
  preservationSystemsSourceReverified : bool;
  preservationSourceRuntimeCount : RuntimeSiteId -> nat;
  preservationTargetRuntimeCount : RuntimeSiteId -> nat;
  preservationExpectedOrdinaryOps : BlockId -> ProjectionDigest;
  preservationActualOrdinaryOps : BlockId -> ProjectionDigest;
  preservationExpectedOrdinaryTerminator : BlockId -> ProjectionDigest;
  preservationActualOrdinaryTerminator : BlockId -> ProjectionDigest;
  preservationSourceEdgePresent : SourceEdgeId -> bool;
  preservationSourceEdgeWitnessCount : SourceEdgeId -> nat;
  preservationSourceEdgeWitnessConnected : SourceEdgeId -> bool;
  preservationTargetEdgePresent : TargetEdgeId -> bool;
  preservationTargetEdgeWitnessed : TargetEdgeId -> bool;
  preservationSourceTraceRelation : RelationId;
  preservationTargetTraceRelation : RelationId;
  preservationSourceResourceFailureRelation : RelationId;
  preservationTargetResourceFailureRelation : RelationId
}.

Definition LLVMPreservationVerificationSuccess
  (model : LLVMPreservationModel) : Prop :=
  preservationSystemsSourceReverified model = true /\
  (forall site,
    preservationSourceRuntimeCount model site =
    preservationTargetRuntimeCount model site) /\
  (forall block,
    preservationExpectedOrdinaryOps model block =
      preservationActualOrdinaryOps model block /\
    preservationExpectedOrdinaryTerminator model block =
      preservationActualOrdinaryTerminator model block) /\
  (forall edge,
    preservationSourceEdgePresent model edge = true ->
    preservationSourceEdgeWitnessCount model edge = 1 /\
    preservationSourceEdgeWitnessConnected model edge = true) /\
  (forall edge,
    preservationSourceEdgePresent model edge = false ->
    preservationSourceEdgeWitnessCount model edge = 0) /\
  (forall edge,
    preservationTargetEdgePresent model edge =
      preservationTargetEdgeWitnessed model edge) /\
  preservationTargetTraceRelation model =
    preservationSourceTraceRelation model /\
  preservationTargetResourceFailureRelation model =
    preservationSourceResourceFailureRelation model.

Theorem verified_llvm_rechecks_source_systems_artifact :
  forall model,
    LLVMPreservationVerificationSuccess model ->
    preservationSystemsSourceReverified model = true.
Proof.
  intros model Hverified.
  destruct Hverified as [Hsource _].
  exact Hsource.
Qed.

Theorem verified_llvm_preserves_runtime_site_multiplicity :
  forall model site,
    LLVMPreservationVerificationSuccess model ->
    preservationSourceRuntimeCount model site =
      preservationTargetRuntimeCount model site.
Proof.
  intros model site Hverified.
  destruct Hverified as [_ [Hruntime _]].
  apply Hruntime.
Qed.

Theorem verified_llvm_matches_conservative_ordinary_projection :
  forall model block,
    LLVMPreservationVerificationSuccess model ->
    preservationExpectedOrdinaryOps model block =
      preservationActualOrdinaryOps model block /\
    preservationExpectedOrdinaryTerminator model block =
      preservationActualOrdinaryTerminator model block.
Proof.
  intros model block Hverified.
  destruct Hverified as [_ [_ [Hordinary _]]].
  apply Hordinary.
Qed.

Theorem verified_source_edge_has_exactly_one_connected_witness :
  forall model edge,
    LLVMPreservationVerificationSuccess model ->
    preservationSourceEdgePresent model edge = true ->
    preservationSourceEdgeWitnessCount model edge = 1 /\
    preservationSourceEdgeWitnessConnected model edge = true.
Proof.
  intros model edge Hverified Hsource.
  destruct Hverified as [_ [_ [_ [Hwitness _]]]].
  apply Hwitness.
  exact Hsource.
Qed.

Theorem verified_non_source_edge_has_no_witness :
  forall model edge,
    LLVMPreservationVerificationSuccess model ->
    preservationSourceEdgePresent model edge = false ->
    preservationSourceEdgeWitnessCount model edge = 0.
Proof.
  intros model edge Hverified HnotSource.
  destruct Hverified as [_ [_ [_ [_ [Hnone _]]]]].
  apply Hnone.
  exact HnotSource.
Qed.

Theorem verified_target_edge_is_witnessed_exactly :
  forall model edge,
    LLVMPreservationVerificationSuccess model ->
    preservationTargetEdgePresent model edge =
      preservationTargetEdgeWitnessed model edge.
Proof.
  intros model edge Hverified.
  destruct Hverified as [_ [_ [_ [_ [_ [Htarget _]]]]]].
  apply Htarget.
Qed.

Theorem verified_llvm_preserves_contract_relations :
  forall model,
    LLVMPreservationVerificationSuccess model ->
    preservationTargetTraceRelation model =
      preservationSourceTraceRelation model /\
    preservationTargetResourceFailureRelation model =
      preservationSourceResourceFailureRelation model.
Proof.
  intros model Hverified.
  destruct Hverified as [_ [_ [_ [_ [_ [_ [Htrace Hresource]]]]]]].
  split; assumption.
Qed.

Theorem missing_runtime_site_is_rejected :
  forall model site,
    preservationSourceRuntimeCount model site <>
      preservationTargetRuntimeCount model site ->
    ~ LLVMPreservationVerificationSuccess model.
Proof.
  intros model site Hmismatch Hverified.
  apply Hmismatch.
  apply verified_llvm_preserves_runtime_site_multiplicity.
  exact Hverified.
Qed.

Theorem invented_ordinary_projection_is_rejected :
  forall model block,
    preservationExpectedOrdinaryOps model block <>
      preservationActualOrdinaryOps model block ->
    ~ LLVMPreservationVerificationSuccess model.
Proof.
  intros model block Hmismatch Hverified.
  pose proof
    (verified_llvm_matches_conservative_ordinary_projection model block Hverified)
    as Hordinary.
  destruct Hordinary as [Hops _].
  contradiction.
Qed.

Theorem missing_source_edge_witness_is_rejected :
  forall model edge,
    preservationSourceEdgePresent model edge = true ->
    preservationSourceEdgeWitnessCount model edge = 0 ->
    ~ LLVMPreservationVerificationSuccess model.
Proof.
  intros model edge Hsource Hnone Hverified.
  pose proof
    (verified_source_edge_has_exactly_one_connected_witness
      model edge Hverified Hsource)
    as Hwitness.
  destruct Hwitness as [Hone _].
  rewrite Hnone in Hone.
  discriminate.
Qed.

Theorem duplicate_source_edge_witness_is_rejected :
  forall model edge count,
    preservationSourceEdgePresent model edge = true ->
    preservationSourceEdgeWitnessCount model edge = S (S count) ->
    ~ LLVMPreservationVerificationSuccess model.
Proof.
  intros model edge count Hsource Hduplicate Hverified.
  pose proof
    (verified_source_edge_has_exactly_one_connected_witness
      model edge Hverified Hsource)
    as Hwitness.
  destruct Hwitness as [Hone _].
  rewrite Hduplicate in Hone.
  discriminate.
Qed.

Theorem disconnected_source_edge_witness_is_rejected :
  forall model edge,
    preservationSourceEdgePresent model edge = true ->
    preservationSourceEdgeWitnessConnected model edge = false ->
    ~ LLVMPreservationVerificationSuccess model.
Proof.
  intros model edge Hsource Hbroken Hverified.
  pose proof
    (verified_source_edge_has_exactly_one_connected_witness
      model edge Hverified Hsource)
    as Hwitness.
  destruct Hwitness as [_ Hconnected].
  rewrite Hbroken in Hconnected.
  discriminate.
Qed.

Theorem unwitnessed_target_edge_is_rejected :
  forall model edge,
    preservationTargetEdgePresent model edge = true ->
    preservationTargetEdgeWitnessed model edge = false ->
    ~ LLVMPreservationVerificationSuccess model.
Proof.
  intros model edge Htarget Hunwitnessed Hverified.
  pose proof (verified_target_edge_is_witnessed_exactly model edge Hverified) as Heq.
  rewrite Htarget in Heq.
  rewrite Hunwitnessed in Heq.
  discriminate.
Qed.

Theorem trace_relation_drift_is_rejected :
  forall model,
    preservationTargetTraceRelation model <>
      preservationSourceTraceRelation model ->
    ~ LLVMPreservationVerificationSuccess model.
Proof.
  intros model Hdrift Hverified.
  pose proof (verified_llvm_preserves_contract_relations model Hverified) as Hrelations.
  destruct Hrelations as [Htrace _].
  contradiction.
Qed.
