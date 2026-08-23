From Phil.Systems Require Import ScalarDataflow LocalRuntimeChoice.

(*
  PHIL-SYS-VERSION-SESSION-CHOICE-001 — normalized proof model for the
  semantic unsupported/version(selected : UInt16) dual session choice
  introduced by PR #67.

  The proof deliberately treats the #68 local-runtime-choice theorem as
  predecessor authority rather than pretending that the final artifact still
  has the predecessor's generic select-version consumer.  PR #67 advances that
  consumer to an OpSessionSelect while preserving the local none/some choice,
  branch-local selected version, dedicated binder target, and stable invariant.

  No physical discriminator, UInt16 wire layout, runtime ABI, buffering rule,
  or outer framing is selected here.
*)

Definition VersionSessionChoiceBlockId := nat.
Definition VersionSessionChoiceDecisionId := nat.

Record SystemsVersionSessionChoiceModel : Type :=
  mkSystemsVersionSessionChoiceModel {
    systemsVersionChoiceLocalPredecessor : SystemsLocalRuntimeChoiceModel;

    systemsVersionChoiceLocalShapeTransferred : bool;
    systemsVersionChoiceLocalBindingTransferred : bool;
    systemsVersionChoiceLocalInvariantTransferred : bool;
    systemsVersionChoiceServerBinderSoleLocalPredecessor : bool;

    systemsVersionChoiceServerTransportExact : bool;
    systemsVersionChoiceServerTransportRole : bool;
    systemsVersionChoiceClientTransportExact : bool;
    systemsVersionChoiceClientTransportRole : bool;

    systemsVersionChoiceUnsupportedLabelExact : bool;
    systemsVersionChoiceUnsupportedPayloadPresent : bool;
    systemsVersionChoiceUnsupportedSelectCount : nat;
    systemsVersionChoiceUnsupportedDecisionExact : bool;

    systemsVersionChoiceVersionLabelExact : bool;
    systemsVersionChoiceVersionPayloadPresent : bool;
    systemsVersionChoiceVersionSelectCount : nat;
    systemsVersionChoiceVersionDecisionExact : bool;
    systemsVersionChoiceWitnessServerSelectedVersion : ValueId;
    systemsVersionChoiceActualServerSelectedVersion : ValueId;
    systemsVersionChoiceServerSelectedVersionIsUInt16 : bool;

    systemsVersionChoiceClientOfferExact : bool;
    systemsVersionChoiceClientUnsupportedPayloadPresent : bool;
    systemsVersionChoiceClientUnsupportedTargetExact : bool;
    systemsVersionChoiceClientVersionPayloadPresent : bool;
    systemsVersionChoiceClientVersionTargetExact : bool;
    systemsVersionChoiceWitnessClientSelectedVersion : ValueId;
    systemsVersionChoiceActualClientSelectedVersion : ValueId;
    systemsVersionChoiceClientSelectedVersionIsUInt16 : bool;
    systemsVersionChoiceClientBinderSoleOfferPredecessor : bool;

    systemsVersionChoiceEndpointPayloadIdentitiesDistinct : bool;
    systemsVersionChoiceRefinementConsumesSelectedVersion : bool;
    systemsVersionChoiceRefinementTargetsExact : bool;

    systemsVersionChoiceLegacyClientDiscriminatorPresent : bool;
    systemsVersionChoiceLegacyClientReceivePresent : bool;

    systemsVersionChoiceWitnessLoweringDecision : VersionSessionChoiceDecisionId;
    systemsVersionChoiceActualLoweringDecision : VersionSessionChoiceDecisionId;
    systemsVersionChoiceLoweringDecisionExact : bool;

    systemsVersionChoicePhysicalDiscriminatorSelected : bool;
    systemsVersionChoiceUInt16WireLayoutSelected : bool;
    systemsVersionChoiceRuntimeABISelected : bool;
    systemsVersionChoiceOuterFramingSelected : bool
  }.

Record SystemsVersionSessionChoiceVerificationSuccess
  (model : SystemsVersionSessionChoiceModel) : Prop :=
  mkSystemsVersionSessionChoiceVerificationSuccess {
    systems_version_choice_success_local_predecessor :
      SystemsLocalRuntimeChoiceVerificationSuccess
        (systemsVersionChoiceLocalPredecessor model);

    systems_version_choice_success_local_shape_transfer :
      systemsVersionChoiceLocalShapeTransferred model = true;
    systems_version_choice_success_local_binding_transfer :
      systemsVersionChoiceLocalBindingTransferred model = true;
    systems_version_choice_success_local_invariant_transfer :
      systemsVersionChoiceLocalInvariantTransferred model = true;
    systems_version_choice_success_server_binder_predecessor :
      systemsVersionChoiceServerBinderSoleLocalPredecessor model = true;

    systems_version_choice_success_server_transport :
      systemsVersionChoiceServerTransportExact model = true;
    systems_version_choice_success_server_transport_role :
      systemsVersionChoiceServerTransportRole model = true;
    systems_version_choice_success_client_transport :
      systemsVersionChoiceClientTransportExact model = true;
    systems_version_choice_success_client_transport_role :
      systemsVersionChoiceClientTransportRole model = true;

    systems_version_choice_success_unsupported_label :
      systemsVersionChoiceUnsupportedLabelExact model = true;
    systems_version_choice_success_unsupported_payload_absent :
      systemsVersionChoiceUnsupportedPayloadPresent model = false;
    systems_version_choice_success_unsupported_select_count :
      systemsVersionChoiceUnsupportedSelectCount model = 1;
    systems_version_choice_success_unsupported_decision :
      systemsVersionChoiceUnsupportedDecisionExact model = true;

    systems_version_choice_success_version_label :
      systemsVersionChoiceVersionLabelExact model = true;
    systems_version_choice_success_version_payload_present :
      systemsVersionChoiceVersionPayloadPresent model = true;
    systems_version_choice_success_version_select_count :
      systemsVersionChoiceVersionSelectCount model = 1;
    systems_version_choice_success_version_decision :
      systemsVersionChoiceVersionDecisionExact model = true;
    systems_version_choice_success_server_payload_identity :
      systemsVersionChoiceActualServerSelectedVersion model =
        systemsVersionChoiceWitnessServerSelectedVersion model;
    systems_version_choice_success_server_payload_u16 :
      systemsVersionChoiceServerSelectedVersionIsUInt16 model = true;

    systems_version_choice_success_client_offer :
      systemsVersionChoiceClientOfferExact model = true;
    systems_version_choice_success_client_unsupported_payload_absent :
      systemsVersionChoiceClientUnsupportedPayloadPresent model = false;
    systems_version_choice_success_client_unsupported_target :
      systemsVersionChoiceClientUnsupportedTargetExact model = true;
    systems_version_choice_success_client_version_payload_present :
      systemsVersionChoiceClientVersionPayloadPresent model = true;
    systems_version_choice_success_client_version_target :
      systemsVersionChoiceClientVersionTargetExact model = true;
    systems_version_choice_success_client_payload_identity :
      systemsVersionChoiceActualClientSelectedVersion model =
        systemsVersionChoiceWitnessClientSelectedVersion model;
    systems_version_choice_success_client_payload_u16 :
      systemsVersionChoiceClientSelectedVersionIsUInt16 model = true;
    systems_version_choice_success_client_binder_predecessor :
      systemsVersionChoiceClientBinderSoleOfferPredecessor model = true;

    systems_version_choice_success_endpoint_payload_distinct :
      systemsVersionChoiceEndpointPayloadIdentitiesDistinct model = true;
    systems_version_choice_success_refinement_input :
      systemsVersionChoiceRefinementConsumesSelectedVersion model = true;
    systems_version_choice_success_refinement_targets :
      systemsVersionChoiceRefinementTargetsExact model = true;

    systems_version_choice_success_no_legacy_discriminator :
      systemsVersionChoiceLegacyClientDiscriminatorPresent model = false;
    systems_version_choice_success_no_legacy_receive :
      systemsVersionChoiceLegacyClientReceivePresent model = false;

    systems_version_choice_success_lowering_identity :
      systemsVersionChoiceActualLoweringDecision model =
        systemsVersionChoiceWitnessLoweringDecision model;
    systems_version_choice_success_lowering_exact :
      systemsVersionChoiceLoweringDecisionExact model = true;

    systems_version_choice_success_no_physical_discriminator :
      systemsVersionChoicePhysicalDiscriminatorSelected model = false;
    systems_version_choice_success_no_wire_layout :
      systemsVersionChoiceUInt16WireLayoutSelected model = false;
    systems_version_choice_success_no_runtime_abi :
      systemsVersionChoiceRuntimeABISelected model = false;
    systems_version_choice_success_no_outer_framing :
      systemsVersionChoiceOuterFramingSelected model = false
  }.

Theorem verified_systems_version_choice_reuses_local_predecessor_authority :
  forall model,
    SystemsVersionSessionChoiceVerificationSuccess model ->
    SystemsLocalRuntimeChoiceVerificationSuccess
      (systemsVersionChoiceLocalPredecessor model).
Proof.
  intros model H.
  exact (systems_version_choice_success_local_predecessor model H).
Qed.

Theorem verified_systems_version_choice_transfers_local_choice_authority :
  forall model,
    SystemsVersionSessionChoiceVerificationSuccess model ->
    systemsVersionChoiceLocalShapeTransferred model = true /\
    systemsVersionChoiceLocalBindingTransferred model = true /\
    systemsVersionChoiceLocalInvariantTransferred model = true /\
    systemsVersionChoiceServerBinderSoleLocalPredecessor model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_version_choice_success_local_shape_transfer model H).
  - exact (systems_version_choice_success_local_binding_transfer model H).
  - exact (systems_version_choice_success_local_invariant_transfer model H).
  - exact (systems_version_choice_success_server_binder_predecessor model H).
Qed.

Theorem verified_systems_version_choice_preserves_exact_transports :
  forall model,
    SystemsVersionSessionChoiceVerificationSuccess model ->
    systemsVersionChoiceServerTransportExact model = true /\
    systemsVersionChoiceServerTransportRole model = true /\
    systemsVersionChoiceClientTransportExact model = true /\
    systemsVersionChoiceClientTransportRole model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_version_choice_success_server_transport model H).
  - exact (systems_version_choice_success_server_transport_role model H).
  - exact (systems_version_choice_success_client_transport model H).
  - exact (systems_version_choice_success_client_transport_role model H).
Qed.

Theorem verified_systems_version_choice_preserves_exact_server_selects :
  forall model,
    SystemsVersionSessionChoiceVerificationSuccess model ->
    systemsVersionChoiceUnsupportedLabelExact model = true /\
    systemsVersionChoiceUnsupportedPayloadPresent model = false /\
    systemsVersionChoiceUnsupportedSelectCount model = 1 /\
    systemsVersionChoiceUnsupportedDecisionExact model = true /\
    systemsVersionChoiceVersionLabelExact model = true /\
    systemsVersionChoiceVersionPayloadPresent model = true /\
    systemsVersionChoiceVersionSelectCount model = 1 /\
    systemsVersionChoiceVersionDecisionExact model = true /\
    systemsVersionChoiceActualServerSelectedVersion model =
      systemsVersionChoiceWitnessServerSelectedVersion model /\
    systemsVersionChoiceServerSelectedVersionIsUInt16 model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_version_choice_success_unsupported_label model H).
  - exact (systems_version_choice_success_unsupported_payload_absent model H).
  - exact (systems_version_choice_success_unsupported_select_count model H).
  - exact (systems_version_choice_success_unsupported_decision model H).
  - exact (systems_version_choice_success_version_label model H).
  - exact (systems_version_choice_success_version_payload_present model H).
  - exact (systems_version_choice_success_version_select_count model H).
  - exact (systems_version_choice_success_version_decision model H).
  - exact (systems_version_choice_success_server_payload_identity model H).
  - exact (systems_version_choice_success_server_payload_u16 model H).
Qed.

Theorem verified_systems_version_choice_preserves_exact_client_offer :
  forall model,
    SystemsVersionSessionChoiceVerificationSuccess model ->
    systemsVersionChoiceClientOfferExact model = true /\
    systemsVersionChoiceClientUnsupportedPayloadPresent model = false /\
    systemsVersionChoiceClientUnsupportedTargetExact model = true /\
    systemsVersionChoiceClientVersionPayloadPresent model = true /\
    systemsVersionChoiceClientVersionTargetExact model = true /\
    systemsVersionChoiceActualClientSelectedVersion model =
      systemsVersionChoiceWitnessClientSelectedVersion model /\
    systemsVersionChoiceClientSelectedVersionIsUInt16 model = true /\
    systemsVersionChoiceClientBinderSoleOfferPredecessor model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_version_choice_success_client_offer model H).
  - exact (systems_version_choice_success_client_unsupported_payload_absent model H).
  - exact (systems_version_choice_success_client_unsupported_target model H).
  - exact (systems_version_choice_success_client_version_payload_present model H).
  - exact (systems_version_choice_success_client_version_target model H).
  - exact (systems_version_choice_success_client_payload_identity model H).
  - exact (systems_version_choice_success_client_payload_u16 model H).
  - exact (systems_version_choice_success_client_binder_predecessor model H).
Qed.

Theorem verified_systems_version_choice_preserves_endpoint_separation_and_refinement :
  forall model,
    SystemsVersionSessionChoiceVerificationSuccess model ->
    systemsVersionChoiceEndpointPayloadIdentitiesDistinct model = true /\
    systemsVersionChoiceRefinementConsumesSelectedVersion model = true /\
    systemsVersionChoiceRefinementTargetsExact model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_version_choice_success_endpoint_payload_distinct model H).
  - exact (systems_version_choice_success_refinement_input model H).
  - exact (systems_version_choice_success_refinement_targets model H).
Qed.

Theorem verified_systems_version_choice_eliminates_legacy_client_choice_and_binds_decision :
  forall model,
    SystemsVersionSessionChoiceVerificationSuccess model ->
    systemsVersionChoiceLegacyClientDiscriminatorPresent model = false /\
    systemsVersionChoiceLegacyClientReceivePresent model = false /\
    systemsVersionChoiceActualLoweringDecision model =
      systemsVersionChoiceWitnessLoweringDecision model /\
    systemsVersionChoiceLoweringDecisionExact model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_version_choice_success_no_legacy_discriminator model H).
  - exact (systems_version_choice_success_no_legacy_receive model H).
  - exact (systems_version_choice_success_lowering_identity model H).
  - exact (systems_version_choice_success_lowering_exact model H).
Qed.

Theorem verified_systems_version_choice_selects_no_physical_representation :
  forall model,
    SystemsVersionSessionChoiceVerificationSuccess model ->
    systemsVersionChoicePhysicalDiscriminatorSelected model = false /\
    systemsVersionChoiceUInt16WireLayoutSelected model = false /\
    systemsVersionChoiceRuntimeABISelected model = false /\
    systemsVersionChoiceOuterFramingSelected model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_version_choice_success_no_physical_discriminator model H).
  - exact (systems_version_choice_success_no_wire_layout model H).
  - exact (systems_version_choice_success_no_runtime_abi model H).
  - exact (systems_version_choice_success_no_outer_framing model H).
Qed.

Theorem systems_version_choice_local_or_transport_drift_is_rejected :
  forall model,
    systemsVersionChoiceLocalShapeTransferred model = false \/
    systemsVersionChoiceLocalBindingTransferred model = false \/
    systemsVersionChoiceLocalInvariantTransferred model = false \/
    systemsVersionChoiceServerBinderSoleLocalPredecessor model = false \/
    systemsVersionChoiceServerTransportExact model = false \/
    systemsVersionChoiceServerTransportRole model = false \/
    systemsVersionChoiceClientTransportExact model = false \/
    systemsVersionChoiceClientTransportRole model = false ->
    ~ SystemsVersionSessionChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hshape | [Hbinding | [Hinv | [Hpred | [Hst | [Hsr | [Hct | Hcr]]]]]]].
  - rewrite (systems_version_choice_success_local_shape_transfer model H) in Hshape. discriminate.
  - rewrite (systems_version_choice_success_local_binding_transfer model H) in Hbinding. discriminate.
  - rewrite (systems_version_choice_success_local_invariant_transfer model H) in Hinv. discriminate.
  - rewrite (systems_version_choice_success_server_binder_predecessor model H) in Hpred. discriminate.
  - rewrite (systems_version_choice_success_server_transport model H) in Hst. discriminate.
  - rewrite (systems_version_choice_success_server_transport_role model H) in Hsr. discriminate.
  - rewrite (systems_version_choice_success_client_transport model H) in Hct. discriminate.
  - rewrite (systems_version_choice_success_client_transport_role model H) in Hcr. discriminate.
Qed.

Theorem systems_version_choice_server_select_drift_is_rejected :
  forall model,
    systemsVersionChoiceUnsupportedLabelExact model = false \/
    systemsVersionChoiceUnsupportedPayloadPresent model = true \/
    systemsVersionChoiceUnsupportedSelectCount model <> 1 \/
    systemsVersionChoiceUnsupportedDecisionExact model = false \/
    systemsVersionChoiceVersionLabelExact model = false \/
    systemsVersionChoiceVersionPayloadPresent model = false \/
    systemsVersionChoiceVersionSelectCount model <> 1 \/
    systemsVersionChoiceVersionDecisionExact model = false \/
    systemsVersionChoiceActualServerSelectedVersion model <>
      systemsVersionChoiceWitnessServerSelectedVersion model \/
    systemsVersionChoiceServerSelectedVersionIsUInt16 model = false ->
    ~ SystemsVersionSessionChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hul | [Hup | [Huc | [Hud | [Hvl | [Hvp | [Hvc | [Hvd | [Hid | Hu16]]]]]]]]].
  - rewrite (systems_version_choice_success_unsupported_label model H) in Hul. discriminate.
  - rewrite (systems_version_choice_success_unsupported_payload_absent model H) in Hup. discriminate.
  - apply Huc. exact (systems_version_choice_success_unsupported_select_count model H).
  - rewrite (systems_version_choice_success_unsupported_decision model H) in Hud. discriminate.
  - rewrite (systems_version_choice_success_version_label model H) in Hvl. discriminate.
  - rewrite (systems_version_choice_success_version_payload_present model H) in Hvp. discriminate.
  - apply Hvc. exact (systems_version_choice_success_version_select_count model H).
  - rewrite (systems_version_choice_success_version_decision model H) in Hvd. discriminate.
  - apply Hid. exact (systems_version_choice_success_server_payload_identity model H).
  - rewrite (systems_version_choice_success_server_payload_u16 model H) in Hu16. discriminate.
Qed.

Theorem systems_version_choice_client_or_representation_drift_is_rejected :
  forall model,
    systemsVersionChoiceClientOfferExact model = false \/
    systemsVersionChoiceClientUnsupportedPayloadPresent model = true \/
    systemsVersionChoiceClientVersionPayloadPresent model = false \/
    systemsVersionChoiceClientBinderSoleOfferPredecessor model = false \/
    systemsVersionChoiceEndpointPayloadIdentitiesDistinct model = false \/
    systemsVersionChoiceRefinementConsumesSelectedVersion model = false \/
    systemsVersionChoiceLegacyClientDiscriminatorPresent model = true \/
    systemsVersionChoiceLegacyClientReceivePresent model = true \/
    systemsVersionChoiceLoweringDecisionExact model = false \/
    systemsVersionChoicePhysicalDiscriminatorSelected model = true \/
    systemsVersionChoiceUInt16WireLayoutSelected model = true \/
    systemsVersionChoiceRuntimeABISelected model = true \/
    systemsVersionChoiceOuterFramingSelected model = true ->
    ~ SystemsVersionSessionChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hoffer | [Hup | [Hvp | [Hpred | [Hdistinct | [Href | [Hdisc | [Hrecv | [Hdec | [Hphys | [Hwire | [Habi | Hframe]]]]]]]]]]]].
  - rewrite (systems_version_choice_success_client_offer model H) in Hoffer. discriminate.
  - rewrite (systems_version_choice_success_client_unsupported_payload_absent model H) in Hup. discriminate.
  - rewrite (systems_version_choice_success_client_version_payload_present model H) in Hvp. discriminate.
  - rewrite (systems_version_choice_success_client_binder_predecessor model H) in Hpred. discriminate.
  - rewrite (systems_version_choice_success_endpoint_payload_distinct model H) in Hdistinct. discriminate.
  - rewrite (systems_version_choice_success_refinement_input model H) in Href. discriminate.
  - rewrite (systems_version_choice_success_no_legacy_discriminator model H) in Hdisc. discriminate.
  - rewrite (systems_version_choice_success_no_legacy_receive model H) in Hrecv. discriminate.
  - rewrite (systems_version_choice_success_lowering_exact model H) in Hdec. discriminate.
  - rewrite (systems_version_choice_success_no_physical_discriminator model H) in Hphys. discriminate.
  - rewrite (systems_version_choice_success_no_wire_layout model H) in Hwire. discriminate.
  - rewrite (systems_version_choice_success_no_runtime_abi model H) in Habi. discriminate.
  - rewrite (systems_version_choice_success_no_outer_framing model H) in Hframe. discriminate.
Qed.
