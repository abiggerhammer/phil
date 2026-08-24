(*
  PHIL-SURF-SYS-UPLOAD-PROJ-001 — normalized proof model for the
  template-directed Phase 0 upload source -> Systems projection introduced by
  PR #117.

  The concrete bridge parses and Surface-checks exactly one UploadClient and
  one UploadServer, compares their normalized semantic traces to the frozen
  Phase 0 upload template, independently digests the exact client/server source
  texts before labeled pair composition, rebinds the canonical base and final
  StorageFailure Systems artifacts to that source identity, rederives lowering
  metadata and assurance contexts, re-verifies both Systems artifacts and
  scalar dataflow, and checks that the rebound final artifact still feeds the
  control-codec-v1 LLVM target.

  This proof models those correspondence obligations. It does not prove the
  cryptographic collision resistance of SHA-256, the Megaparsec parser, the
  Haskell Surface checker, Text traversal, or a generic .phil -> Systems
  compiler. In particular, the pair-digest theorem below establishes labeled
  independent digest *structure*, not hash-function injectivity.
*)

Record Phase0UploadProjectionModel : Type := mkPhase0UploadProjectionModel {
  projection_client_trace_exact : bool;
  projection_server_trace_exact : bool;
  projection_client_digest_independent : bool;
  projection_server_digest_independent : bool;
  projection_pair_domain_labeled : bool;
  projection_base_program_unchanged : bool;
  projection_final_program_unchanged : bool;
  projection_base_stage_source_bound : bool;
  projection_final_stage_source_bound : bool;
  projection_base_decisions_source_bound : bool;
  projection_final_decisions_source_bound : bool;
  projection_base_decision_digests_rederived : bool;
  projection_final_decision_digests_rederived : bool;
  projection_base_lowering_root_rederived : bool;
  projection_final_lowering_root_rederived : bool;
  projection_base_manifest_context_rederived : bool;
  projection_final_manifest_context_rederived : bool;
  projection_base_systems_verifies : bool;
  projection_final_systems_verifies : bool;
  projection_base_scalar_dataflow_verifies : bool;
  projection_final_scalar_dataflow_verifies : bool;
  projection_control_codec_translation_verifies : bool;
  projection_generic_lowerer_claimed : bool
}.

Definition VerifiedPhase0UploadProjection
  (p : Phase0UploadProjectionModel) : Prop :=
  projection_client_trace_exact p = true /\
  projection_server_trace_exact p = true /\
  projection_client_digest_independent p = true /\
  projection_server_digest_independent p = true /\
  projection_pair_domain_labeled p = true /\
  projection_base_program_unchanged p = true /\
  projection_final_program_unchanged p = true /\
  projection_base_stage_source_bound p = true /\
  projection_final_stage_source_bound p = true /\
  projection_base_decisions_source_bound p = true /\
  projection_final_decisions_source_bound p = true /\
  projection_base_decision_digests_rederived p = true /\
  projection_final_decision_digests_rederived p = true /\
  projection_base_lowering_root_rederived p = true /\
  projection_final_lowering_root_rederived p = true /\
  projection_base_manifest_context_rederived p = true /\
  projection_final_manifest_context_rederived p = true /\
  projection_base_systems_verifies p = true /\
  projection_final_systems_verifies p = true /\
  projection_base_scalar_dataflow_verifies p = true /\
  projection_final_scalar_dataflow_verifies p = true /\
  projection_control_codec_translation_verifies p = true /\
  projection_generic_lowerer_claimed p = false.

Theorem verified_phase0_upload_projection_requires_exact_frozen_traces :
  forall p,
    VerifiedPhase0UploadProjection p ->
    projection_client_trace_exact p = true /\
    projection_server_trace_exact p = true.
Proof.
  intros p H.
  destruct H as [Hclient [Hserver _]].
  auto.
Qed.

Theorem verified_phase0_upload_projection_binds_labeled_independent_source_digests :
  forall p,
    VerifiedPhase0UploadProjection p ->
    projection_client_digest_independent p = true /\
    projection_server_digest_independent p = true /\
    projection_pair_domain_labeled p = true.
Proof.
  intros p H.
  destruct H as [_ [_ [Hclient [Hserver [Hpair _]]]]].
  auto.
Qed.

Theorem verified_phase0_upload_projection_preserves_both_systems_programs :
  forall p,
    VerifiedPhase0UploadProjection p ->
    projection_base_program_unchanged p = true /\
    projection_final_program_unchanged p = true.
Proof.
  intros p H.
  destruct H as [_ [_ [_ [_ [_ [Hbase [Hfinal _]]]]]]].
  auto.
Qed.

Theorem verified_phase0_upload_projection_rebinds_source_authority_uniformly :
  forall p,
    VerifiedPhase0UploadProjection p ->
    projection_base_stage_source_bound p = true /\
    projection_final_stage_source_bound p = true /\
    projection_base_decisions_source_bound p = true /\
    projection_final_decisions_source_bound p = true.
Proof.
  intros p H.
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [HbaseStage [HfinalStage [HbaseDecisions [HfinalDecisions _]]]].
  auto.
Qed.

Theorem verified_phase0_upload_projection_rederives_identity_metadata :
  forall p,
    VerifiedPhase0UploadProjection p ->
    projection_base_decision_digests_rederived p = true /\
    projection_final_decision_digests_rederived p = true /\
    projection_base_lowering_root_rederived p = true /\
    projection_final_lowering_root_rederived p = true /\
    projection_base_manifest_context_rederived p = true /\
    projection_final_manifest_context_rederived p = true.
Proof.
  intros p H.
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as
    [HbaseDigests [HfinalDigests [HbaseRoot [HfinalRoot
      [HbaseContext [HfinalContext _]]]]]].
  repeat split; assumption.
Qed.

Theorem verified_phase0_upload_projection_rechecks_rebound_systems_authority :
  forall p,
    VerifiedPhase0UploadProjection p ->
    projection_base_systems_verifies p = true /\
    projection_final_systems_verifies p = true /\
    projection_base_scalar_dataflow_verifies p = true /\
    projection_final_scalar_dataflow_verifies p = true.
Proof.
  intros p H.
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [HbaseSystems [HfinalSystems [HbaseFlow [HfinalFlow _]]]].
  auto.
Qed.

Theorem verified_phase0_upload_projection_reaches_control_codec_target :
  forall p,
    VerifiedPhase0UploadProjection p ->
    projection_control_codec_translation_verifies p = true.
Proof.
  intros p H.
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [Hcodec _].
  exact Hcodec.
Qed.

Theorem verified_phase0_upload_projection_claims_no_generic_lowerer :
  forall p,
    VerifiedPhase0UploadProjection p ->
    projection_generic_lowerer_claimed p = false.
Proof.
  intros p H.
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  destruct H as [_ H].
  exact H.
Qed.

Theorem phase0_upload_projection_client_semantic_drift_is_rejected :
  forall p,
    projection_client_trace_exact p = false ->
    ~ VerifiedPhase0UploadProjection p.
Proof.
  intros p Hdrift Hverified.
  pose proof
    (verified_phase0_upload_projection_requires_exact_frozen_traces p Hverified)
    as Hexact.
  destruct Hexact as [Hclient _].
  rewrite Hdrift in Hclient.
  discriminate.
Qed.

Theorem phase0_upload_projection_server_semantic_drift_is_rejected :
  forall p,
    projection_server_trace_exact p = false ->
    ~ VerifiedPhase0UploadProjection p.
Proof.
  intros p Hdrift Hverified.
  pose proof
    (verified_phase0_upload_projection_requires_exact_frozen_traces p Hverified)
    as Hexact.
  destruct Hexact as [_ Hserver].
  rewrite Hdrift in Hserver.
  discriminate.
Qed.

Theorem phase0_upload_projection_program_drift_is_rejected :
  forall p,
    projection_base_program_unchanged p = false \/
    projection_final_program_unchanged p = false ->
    ~ VerifiedPhase0UploadProjection p.
Proof.
  intros p Hdrift Hverified.
  pose proof
    (verified_phase0_upload_projection_preserves_both_systems_programs p Hverified)
    as Hprograms.
  destruct Hprograms as [Hbase Hfinal].
  destruct Hdrift as [Hdrift | Hdrift].
  - rewrite Hdrift in Hbase. discriminate.
  - rewrite Hdrift in Hfinal. discriminate.
Qed.

Theorem phase0_upload_projection_source_binding_drift_is_rejected :
  forall p,
    projection_base_stage_source_bound p = false \/
    projection_final_stage_source_bound p = false \/
    projection_base_decisions_source_bound p = false \/
    projection_final_decisions_source_bound p = false ->
    ~ VerifiedPhase0UploadProjection p.
Proof.
  intros p Hdrift Hverified.
  pose proof
    (verified_phase0_upload_projection_rebinds_source_authority_uniformly p Hverified)
    as Hbound.
  destruct Hbound as [Hb [Hf [Hbd Hfd]]].
  destruct Hdrift as [H | [H | [H | H]]];
    rewrite H in *; discriminate.
Qed.
