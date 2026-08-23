From Phil.Systems Require Import ScalarDataflow VersionSessionChoice.

(*
  PHIL-SYS-VERSION-CHOICE-OPERANDS-001 — normalized proof model for the
  explicit runtime operands introduced by PR #69.

  This is a successor proof.  PHIL-SYS-VERSION-SESSION-CHOICE-001 remains
  semantic predecessor authority; the final artifact additionally materializes
  serverSupported, recognized Hello, and Hello.versions so choose_supported has
  explicit operands.  Runtime-provider set semantics are not proved here.
*)

Definition VersionChoiceOperandsDecisionId := nat.

Record SystemsVersionChoiceOperandsModel : Type :=
  mkSystemsVersionChoiceOperandsModel {
    systemsVersionOperandsSemanticPredecessor : SystemsVersionSessionChoiceModel;

    systemsVersionOperandsServerSupportedExact : bool;
    systemsVersionOperandsServerSupportedRuntimeInput : bool;
    systemsVersionOperandsServerSupportedHasProducer : bool;

    systemsVersionOperandsHelloRecordExact : bool;
    systemsVersionOperandsHelloRecordRuntimeRecord : bool;
    systemsVersionOperandsHelloVersionsExact : bool;
    systemsVersionOperandsHelloVersionsRuntimeOpaque : bool;

    systemsVersionOperandsCommitBeforeMaterialize : bool;
    systemsVersionOperandsMaterializeCount : nat;
    systemsVersionOperandsMaterializeExact : bool;
    systemsVersionOperandsProjectionCount : nat;
    systemsVersionOperandsProjectionExact : bool;

    systemsVersionOperandsChooserNameExact : bool;
    systemsVersionOperandsChooserInputCount : nat;
    systemsVersionOperandsChooserInput0ServerSupported : bool;
    systemsVersionOperandsChooserInput1HelloVersions : bool;
    systemsVersionOperandsChooserSiteAbsent : bool;
    systemsVersionOperandsChooserArmsTransferred : bool;
    systemsVersionOperandsSelectedVersionBindingTransferred : bool;
    systemsVersionOperandsInvariantTransferred : bool;

    systemsVersionOperandsServerUnsupportedSelectCount : nat;
    systemsVersionOperandsServerVersionSelectCount : nat;
    systemsVersionOperandsClientOfferTransferred : bool;
    systemsVersionOperandsClientRefinementTransferred : bool;
    systemsVersionOperandsPayloadCancelAuthorityTransferred : bool;

    systemsVersionOperandsWitnessDecision : VersionChoiceOperandsDecisionId;
    systemsVersionOperandsActualDecision : VersionChoiceOperandsDecisionId;
    systemsVersionOperandsDecisionExact : bool;

    systemsVersionOperandsProviderSetSemanticsClaimed : bool;
    systemsVersionOperandsTieBreakingClaimed : bool
  }.

Record SystemsVersionChoiceOperandsVerificationSuccess
  (model : SystemsVersionChoiceOperandsModel) : Prop :=
  mkSystemsVersionChoiceOperandsVerificationSuccess {
    systems_version_operands_success_semantic_predecessor :
      SystemsVersionSessionChoiceVerificationSuccess
        (systemsVersionOperandsSemanticPredecessor model);

    systems_version_operands_success_server_supported_exact :
      systemsVersionOperandsServerSupportedExact model = true;
    systems_version_operands_success_server_supported_role :
      systemsVersionOperandsServerSupportedRuntimeInput model = true;
    systems_version_operands_success_server_supported_no_producer :
      systemsVersionOperandsServerSupportedHasProducer model = false;

    systems_version_operands_success_hello_record_exact :
      systemsVersionOperandsHelloRecordExact model = true;
    systems_version_operands_success_hello_record_role :
      systemsVersionOperandsHelloRecordRuntimeRecord model = true;
    systems_version_operands_success_hello_versions_exact :
      systemsVersionOperandsHelloVersionsExact model = true;
    systems_version_operands_success_hello_versions_role :
      systemsVersionOperandsHelloVersionsRuntimeOpaque model = true;

    systems_version_operands_success_commit_before_materialize :
      systemsVersionOperandsCommitBeforeMaterialize model = true;
    systems_version_operands_success_materialize_count :
      systemsVersionOperandsMaterializeCount model = 1;
    systems_version_operands_success_materialize_exact :
      systemsVersionOperandsMaterializeExact model = true;
    systems_version_operands_success_projection_count :
      systemsVersionOperandsProjectionCount model = 1;
    systems_version_operands_success_projection_exact :
      systemsVersionOperandsProjectionExact model = true;

    systems_version_operands_success_chooser_name :
      systemsVersionOperandsChooserNameExact model = true;
    systems_version_operands_success_chooser_input_count :
      systemsVersionOperandsChooserInputCount model = 2;
    systems_version_operands_success_chooser_input0 :
      systemsVersionOperandsChooserInput0ServerSupported model = true;
    systems_version_operands_success_chooser_input1 :
      systemsVersionOperandsChooserInput1HelloVersions model = true;
    systems_version_operands_success_chooser_site_absent :
      systemsVersionOperandsChooserSiteAbsent model = true;
    systems_version_operands_success_chooser_arms :
      systemsVersionOperandsChooserArmsTransferred model = true;
    systems_version_operands_success_selected_binding :
      systemsVersionOperandsSelectedVersionBindingTransferred model = true;
    systems_version_operands_success_invariant :
      systemsVersionOperandsInvariantTransferred model = true;

    systems_version_operands_success_unsupported_select_count :
      systemsVersionOperandsServerUnsupportedSelectCount model = 1;
    systems_version_operands_success_version_select_count :
      systemsVersionOperandsServerVersionSelectCount model = 1;
    systems_version_operands_success_client_offer :
      systemsVersionOperandsClientOfferTransferred model = true;
    systems_version_operands_success_client_refinement :
      systemsVersionOperandsClientRefinementTransferred model = true;
    systems_version_operands_success_payload_cancel :
      systemsVersionOperandsPayloadCancelAuthorityTransferred model = true;

    systems_version_operands_success_decision_identity :
      systemsVersionOperandsActualDecision model =
        systemsVersionOperandsWitnessDecision model;
    systems_version_operands_success_decision_exact :
      systemsVersionOperandsDecisionExact model = true;

    systems_version_operands_success_no_provider_semantics_claim :
      systemsVersionOperandsProviderSetSemanticsClaimed model = false;
    systems_version_operands_success_no_tie_breaking_claim :
      systemsVersionOperandsTieBreakingClaimed model = false
  }.

Theorem verified_systems_version_operands_reuses_semantic_authority :
  forall model,
    SystemsVersionChoiceOperandsVerificationSuccess model ->
    SystemsVersionSessionChoiceVerificationSuccess
      (systemsVersionOperandsSemanticPredecessor model).
Proof.
  intros model H.
  exact (systems_version_operands_success_semantic_predecessor model H).
Qed.

Theorem verified_systems_version_operands_materializes_exact_runtime_values :
  forall model,
    SystemsVersionChoiceOperandsVerificationSuccess model ->
    systemsVersionOperandsServerSupportedExact model = true /\
    systemsVersionOperandsServerSupportedRuntimeInput model = true /\
    systemsVersionOperandsServerSupportedHasProducer model = false /\
    systemsVersionOperandsHelloRecordExact model = true /\
    systemsVersionOperandsHelloRecordRuntimeRecord model = true /\
    systemsVersionOperandsHelloVersionsExact model = true /\
    systemsVersionOperandsHelloVersionsRuntimeOpaque model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_version_operands_success_server_supported_exact model H).
  - exact (systems_version_operands_success_server_supported_role model H).
  - exact (systems_version_operands_success_server_supported_no_producer model H).
  - exact (systems_version_operands_success_hello_record_exact model H).
  - exact (systems_version_operands_success_hello_record_role model H).
  - exact (systems_version_operands_success_hello_versions_exact model H).
  - exact (systems_version_operands_success_hello_versions_role model H).
Qed.

Theorem verified_systems_version_operands_preserves_commit_projection_order :
  forall model,
    SystemsVersionChoiceOperandsVerificationSuccess model ->
    systemsVersionOperandsCommitBeforeMaterialize model = true /\
    systemsVersionOperandsMaterializeCount model = 1 /\
    systemsVersionOperandsMaterializeExact model = true /\
    systemsVersionOperandsProjectionCount model = 1 /\
    systemsVersionOperandsProjectionExact model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_version_operands_success_commit_before_materialize model H).
  - exact (systems_version_operands_success_materialize_count model H).
  - exact (systems_version_operands_success_materialize_exact model H).
  - exact (systems_version_operands_success_projection_count model H).
  - exact (systems_version_operands_success_projection_exact model H).
Qed.

Theorem verified_systems_version_operands_binds_exact_chooser_inputs :
  forall model,
    SystemsVersionChoiceOperandsVerificationSuccess model ->
    systemsVersionOperandsChooserNameExact model = true /\
    systemsVersionOperandsChooserInputCount model = 2 /\
    systemsVersionOperandsChooserInput0ServerSupported model = true /\
    systemsVersionOperandsChooserInput1HelloVersions model = true /\
    systemsVersionOperandsChooserSiteAbsent model = true /\
    systemsVersionOperandsChooserArmsTransferred model = true /\
    systemsVersionOperandsSelectedVersionBindingTransferred model = true /\
    systemsVersionOperandsInvariantTransferred model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_version_operands_success_chooser_name model H).
  - exact (systems_version_operands_success_chooser_input_count model H).
  - exact (systems_version_operands_success_chooser_input0 model H).
  - exact (systems_version_operands_success_chooser_input1 model H).
  - exact (systems_version_operands_success_chooser_site_absent model H).
  - exact (systems_version_operands_success_chooser_arms model H).
  - exact (systems_version_operands_success_selected_binding model H).
  - exact (systems_version_operands_success_invariant model H).
Qed.

Theorem verified_systems_version_operands_preserves_session_and_refinement_authority :
  forall model,
    SystemsVersionChoiceOperandsVerificationSuccess model ->
    systemsVersionOperandsServerUnsupportedSelectCount model = 1 /\
    systemsVersionOperandsServerVersionSelectCount model = 1 /\
    systemsVersionOperandsClientOfferTransferred model = true /\
    systemsVersionOperandsClientRefinementTransferred model = true /\
    systemsVersionOperandsPayloadCancelAuthorityTransferred model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_version_operands_success_unsupported_select_count model H).
  - exact (systems_version_operands_success_version_select_count model H).
  - exact (systems_version_operands_success_client_offer model H).
  - exact (systems_version_operands_success_client_refinement model H).
  - exact (systems_version_operands_success_payload_cancel model H).
Qed.

Theorem verified_systems_version_operands_binds_lowering_decision_without_provider_claim :
  forall model,
    SystemsVersionChoiceOperandsVerificationSuccess model ->
    systemsVersionOperandsActualDecision model =
      systemsVersionOperandsWitnessDecision model /\
    systemsVersionOperandsDecisionExact model = true /\
    systemsVersionOperandsProviderSetSemanticsClaimed model = false /\
    systemsVersionOperandsTieBreakingClaimed model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_version_operands_success_decision_identity model H).
  - exact (systems_version_operands_success_decision_exact model H).
  - exact (systems_version_operands_success_no_provider_semantics_claim model H).
  - exact (systems_version_operands_success_no_tie_breaking_claim model H).
Qed.

Theorem systems_version_operands_value_or_projection_drift_is_rejected :
  forall model,
    systemsVersionOperandsServerSupportedExact model = false \/
    systemsVersionOperandsServerSupportedRuntimeInput model = false \/
    systemsVersionOperandsServerSupportedHasProducer model = true \/
    systemsVersionOperandsHelloRecordExact model = false \/
    systemsVersionOperandsHelloRecordRuntimeRecord model = false \/
    systemsVersionOperandsHelloVersionsExact model = false \/
    systemsVersionOperandsHelloVersionsRuntimeOpaque model = false \/
    systemsVersionOperandsCommitBeforeMaterialize model = false \/
    systemsVersionOperandsMaterializeCount model <> 1 \/
    systemsVersionOperandsProjectionCount model <> 1 ->
    ~ SystemsVersionChoiceOperandsVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hss | [Hsr | [Hsp | [Hhr | [Hhrr | [Hhv | [Hhvr | [Hcommit | [Hmc | Hpc]]]]]]]]].
  - rewrite (systems_version_operands_success_server_supported_exact model H) in Hss. discriminate.
  - rewrite (systems_version_operands_success_server_supported_role model H) in Hsr. discriminate.
  - rewrite (systems_version_operands_success_server_supported_no_producer model H) in Hsp. discriminate.
  - rewrite (systems_version_operands_success_hello_record_exact model H) in Hhr. discriminate.
  - rewrite (systems_version_operands_success_hello_record_role model H) in Hhrr. discriminate.
  - rewrite (systems_version_operands_success_hello_versions_exact model H) in Hhv. discriminate.
  - rewrite (systems_version_operands_success_hello_versions_role model H) in Hhvr. discriminate.
  - rewrite (systems_version_operands_success_commit_before_materialize model H) in Hcommit. discriminate.
  - apply Hmc. exact (systems_version_operands_success_materialize_count model H).
  - apply Hpc. exact (systems_version_operands_success_projection_count model H).
Qed.

Theorem systems_version_operands_chooser_session_or_provider_drift_is_rejected :
  forall model,
    systemsVersionOperandsChooserInputCount model <> 2 \/
    systemsVersionOperandsChooserInput0ServerSupported model = false \/
    systemsVersionOperandsChooserInput1HelloVersions model = false \/
    systemsVersionOperandsServerUnsupportedSelectCount model <> 1 \/
    systemsVersionOperandsServerVersionSelectCount model <> 1 \/
    systemsVersionOperandsClientOfferTransferred model = false \/
    systemsVersionOperandsClientRefinementTransferred model = false \/
    systemsVersionOperandsDecisionExact model = false \/
    systemsVersionOperandsProviderSetSemanticsClaimed model = true \/
    systemsVersionOperandsTieBreakingClaimed model = true ->
    ~ SystemsVersionChoiceOperandsVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hic | [Hi0 | [Hi1 | [Hus | [Hvs | [Hoffer | [Href | [Hdec | [Hprovider | Htie]]]]]]]]].
  - apply Hic. exact (systems_version_operands_success_chooser_input_count model H).
  - rewrite (systems_version_operands_success_chooser_input0 model H) in Hi0. discriminate.
  - rewrite (systems_version_operands_success_chooser_input1 model H) in Hi1. discriminate.
  - apply Hus. exact (systems_version_operands_success_unsupported_select_count model H).
  - apply Hvs. exact (systems_version_operands_success_version_select_count model H).
  - rewrite (systems_version_operands_success_client_offer model H) in Hoffer. discriminate.
  - rewrite (systems_version_operands_success_client_refinement model H) in Href. discriminate.
  - rewrite (systems_version_operands_success_decision_exact model H) in Hdec. discriminate.
  - rewrite (systems_version_operands_success_no_provider_semantics_claim model H) in Hprovider. discriminate.
  - rewrite (systems_version_operands_success_no_tie_breaking_claim model H) in Htie. discriminate.
Qed.
