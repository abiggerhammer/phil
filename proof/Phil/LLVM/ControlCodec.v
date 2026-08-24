(*
  PHIL-LLVM-CONTROL-CODEC-001 — normalized proof model for the
  control-codec-v1 runtime-profile successor introduced by #111.

  This theorem deliberately proves the compiler/profile boundary only.
  Concrete C codec behavior is established separately by content-bound
  DifferentialTested evidence and is not promoted into a Rocq theorem.
*)

Record control_codec_facts : Type := {
  cc_source_is_storage_failure_detail : Prop;
  cc_cert016_predecessor_is_bound : Prop;
  cc_function_bodies_equal_predecessor : Prop;
  cc_strengthenings_equal_predecessor : Prop;
  cc_runtime_profile_is_control_codec_v1 : Prop;
  cc_runtime_abi_digest_binds_codec_descriptor : Prop;
  cc_required_control_primitives_remain_explicit : Prop;
  cc_legacy_storage_profile_is_absent : Prop;
  cc_runtime_codec_evidence_is_separate : Prop;
  cc_no_universal_provider_or_io_claim : Prop
}.

Definition verified_llvm_control_codec (facts : control_codec_facts) : Prop :=
  cc_source_is_storage_failure_detail facts /\
  cc_cert016_predecessor_is_bound facts /\
  cc_function_bodies_equal_predecessor facts /\
  cc_strengthenings_equal_predecessor facts /\
  cc_runtime_profile_is_control_codec_v1 facts /\
  cc_runtime_abi_digest_binds_codec_descriptor facts /\
  cc_required_control_primitives_remain_explicit facts /\
  cc_legacy_storage_profile_is_absent facts /\
  cc_runtime_codec_evidence_is_separate facts /\
  cc_no_universal_provider_or_io_claim facts.

Theorem verified_llvm_control_codec_reuses_source_and_cert016_predecessor :
  forall facts,
    verified_llvm_control_codec facts ->
    cc_source_is_storage_failure_detail facts /\
    cc_cert016_predecessor_is_bound facts.
Proof.
  intros facts H.
  unfold verified_llvm_control_codec in H.
  tauto.
Qed.

Theorem verified_llvm_control_codec_preserves_function_bodies_and_strengthenings :
  forall facts,
    verified_llvm_control_codec facts ->
    cc_function_bodies_equal_predecessor facts /\
    cc_strengthenings_equal_predecessor facts.
Proof.
  intros facts H.
  unfold verified_llvm_control_codec in H.
  tauto.
Qed.

Theorem verified_llvm_control_codec_selects_exact_runtime_profile :
  forall facts,
    verified_llvm_control_codec facts ->
    cc_runtime_profile_is_control_codec_v1 facts /\
    cc_legacy_storage_profile_is_absent facts.
Proof.
  intros facts H.
  unfold verified_llvm_control_codec in H.
  tauto.
Qed.

Theorem verified_llvm_control_codec_binds_exact_descriptor_dimensions :
  forall facts,
    verified_llvm_control_codec facts ->
    cc_runtime_abi_digest_binds_codec_descriptor facts /\
    cc_required_control_primitives_remain_explicit facts.
Proof.
  intros facts H.
  unfold verified_llvm_control_codec in H.
  tauto.
Qed.

Theorem verified_llvm_control_codec_requires_concrete_runtime_evidence :
  forall facts,
    verified_llvm_control_codec facts ->
    cc_runtime_codec_evidence_is_separate facts.
Proof.
  intros facts H.
  unfold verified_llvm_control_codec in H.
  tauto.
Qed.

Theorem verified_llvm_control_codec_claims_no_universal_provider_or_io_theorem :
  forall facts,
    verified_llvm_control_codec facts ->
    cc_no_universal_provider_or_io_claim facts.
Proof.
  intros facts H.
  unfold verified_llvm_control_codec in H.
  tauto.
Qed.

Definition llvm_control_codec_profile_or_body_drift (facts : control_codec_facts) : Prop :=
  ~ (cc_function_bodies_equal_predecessor facts /\
     cc_strengthenings_equal_predecessor facts /\
     cc_runtime_profile_is_control_codec_v1 facts /\
     cc_runtime_abi_digest_binds_codec_descriptor facts /\
     cc_legacy_storage_profile_is_absent facts).

Theorem llvm_control_codec_profile_or_body_drift_is_rejected :
  forall facts,
    llvm_control_codec_profile_or_body_drift facts ->
    ~ verified_llvm_control_codec facts.
Proof.
  intros facts Hdrift Hverified.
  apply Hdrift.
  unfold verified_llvm_control_codec in Hverified.
  tauto.
Qed.
