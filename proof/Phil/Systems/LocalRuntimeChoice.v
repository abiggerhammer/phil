From Phil.Systems Require Import ScalarDataflow PayloadCancelChoice.

(*
  PHIL-SYS-LOCAL-RUNTIME-CHOICE-001 — normalized proof model for the
  locally computed choose_supported none/some result introduced by PR #65.

  The model deliberately separates local runtime authority from peer/session
  authority.  It preserves the some-arm branch-local UInt16 selected version,
  requires the binder target to have the choice block as sole predecessor,
  keeps the none arm unable to observe the some payload, preserves the exact
  generic select-version consumer used by this slice, transfers the stable
  version-selection invariant to InvariantRuntimeChoice, eliminates the old
  has_version Bool and choose_supported output call, and reuses the already
  proof-bound payload/cancel semantic authority.

  No physical representation for choose_supported is selected here.
*)

Definition LocalRuntimeChoiceBlockId := nat.
Definition LocalRuntimeChoiceInvariantId := nat.
Definition LocalRuntimeChoiceDecisionId := nat.

Record SystemsLocalRuntimeChoiceModel : Type := mkSystemsLocalRuntimeChoiceModel {
  systemsLocalChoicePayloadCancelPredecessor : SystemsPayloadCancelChoiceModel;

  systemsLocalChoiceNameExact : bool;
  systemsLocalChoiceInputsEmpty : bool;
  systemsLocalChoiceSiteAbsent : bool;
  systemsLocalChoiceRepresentedAsSessionOffer : bool;

  systemsLocalChoiceNoneLabelExact : bool;
  systemsLocalChoiceSomeLabelExact : bool;
  systemsLocalChoiceNonePayloadPresent : bool;
  systemsLocalChoiceSomePayloadPresent : bool;

  systemsLocalChoiceWitnessNoneTarget : LocalRuntimeChoiceBlockId;
  systemsLocalChoiceActualNoneTarget : LocalRuntimeChoiceBlockId;
  systemsLocalChoiceWitnessSomeTarget : LocalRuntimeChoiceBlockId;
  systemsLocalChoiceActualSomeTarget : LocalRuntimeChoiceBlockId;

  systemsLocalChoiceWitnessSelectedVersion : ValueId;
  systemsLocalChoiceActualSelectedVersion : ValueId;
  systemsLocalChoiceSelectedVersionIsUInt16 : bool;
  systemsLocalChoiceBinderAtSomeTargetEntry : bool;
  systemsLocalChoiceSomeTargetHasSoleChoicePredecessor : bool;
  systemsLocalChoiceNoneArmUsesSelectedVersion : bool;

  systemsLocalChoiceVersionSelectConsumesExactPair : bool;
  systemsLocalChoiceVersionSelectTransportFirst : bool;
  systemsLocalChoiceVersionSelectIsSemanticSessionSelect : bool;

  systemsLocalChoiceLegacyDiscriminatorPresent : bool;
  systemsLocalChoiceLegacyChooseCallPresent : bool;

  systemsLocalChoiceWitnessInvariant : LocalRuntimeChoiceInvariantId;
  systemsLocalChoiceActualInvariant : LocalRuntimeChoiceInvariantId;
  systemsLocalChoiceInvariantRuntimeChoiceExact : bool;

  systemsLocalChoiceWitnessLoweringDecision : LocalRuntimeChoiceDecisionId;
  systemsLocalChoiceActualLoweringDecision : LocalRuntimeChoiceDecisionId;
  systemsLocalChoiceLoweringDecisionExact : bool
}.

Record SystemsLocalRuntimeChoiceVerificationSuccess
  (model : SystemsLocalRuntimeChoiceModel) : Prop :=
  mkSystemsLocalRuntimeChoiceVerificationSuccess {
    systems_local_choice_success_payload_cancel_authority :
      SystemsPayloadCancelChoiceVerificationSuccess
        (systemsLocalChoicePayloadCancelPredecessor model);

    systems_local_choice_success_name :
      systemsLocalChoiceNameExact model = true;
    systems_local_choice_success_inputs_empty :
      systemsLocalChoiceInputsEmpty model = true;
    systems_local_choice_success_site_absent :
      systemsLocalChoiceSiteAbsent model = true;
    systems_local_choice_success_not_session_offer :
      systemsLocalChoiceRepresentedAsSessionOffer model = false;

    systems_local_choice_success_none_label :
      systemsLocalChoiceNoneLabelExact model = true;
    systems_local_choice_success_some_label :
      systemsLocalChoiceSomeLabelExact model = true;
    systems_local_choice_success_none_payload_absent :
      systemsLocalChoiceNonePayloadPresent model = false;
    systems_local_choice_success_some_payload_present :
      systemsLocalChoiceSomePayloadPresent model = true;

    systems_local_choice_success_none_target :
      systemsLocalChoiceActualNoneTarget model =
        systemsLocalChoiceWitnessNoneTarget model;
    systems_local_choice_success_some_target :
      systemsLocalChoiceActualSomeTarget model =
        systemsLocalChoiceWitnessSomeTarget model;

    systems_local_choice_success_selected_version :
      systemsLocalChoiceActualSelectedVersion model =
        systemsLocalChoiceWitnessSelectedVersion model;
    systems_local_choice_success_selected_version_u16 :
      systemsLocalChoiceSelectedVersionIsUInt16 model = true;
    systems_local_choice_success_binder_entry :
      systemsLocalChoiceBinderAtSomeTargetEntry model = true;
    systems_local_choice_success_sole_predecessor :
      systemsLocalChoiceSomeTargetHasSoleChoicePredecessor model = true;
    systems_local_choice_success_no_none_arm_use :
      systemsLocalChoiceNoneArmUsesSelectedVersion model = false;

    systems_local_choice_success_version_select_pair :
      systemsLocalChoiceVersionSelectConsumesExactPair model = true;
    systems_local_choice_success_version_select_order :
      systemsLocalChoiceVersionSelectTransportFirst model = true;
    systems_local_choice_success_version_select_still_generic :
      systemsLocalChoiceVersionSelectIsSemanticSessionSelect model = false;

    systems_local_choice_success_no_legacy_discriminator :
      systemsLocalChoiceLegacyDiscriminatorPresent model = false;
    systems_local_choice_success_no_legacy_choose_call :
      systemsLocalChoiceLegacyChooseCallPresent model = false;

    systems_local_choice_success_invariant_identity :
      systemsLocalChoiceActualInvariant model =
        systemsLocalChoiceWitnessInvariant model;
    systems_local_choice_success_invariant_shape :
      systemsLocalChoiceInvariantRuntimeChoiceExact model = true;

    systems_local_choice_success_lowering_identity :
      systemsLocalChoiceActualLoweringDecision model =
        systemsLocalChoiceWitnessLoweringDecision model;
    systems_local_choice_success_lowering_exact :
      systemsLocalChoiceLoweringDecisionExact model = true
  }.

Theorem verified_systems_local_choice_reuses_payload_cancel_authority :
  forall model,
    SystemsLocalRuntimeChoiceVerificationSuccess model ->
    SystemsPayloadCancelChoiceVerificationSuccess
      (systemsLocalChoicePayloadCancelPredecessor model).
Proof.
  intros model H.
  exact (systems_local_choice_success_payload_cancel_authority model H).
Qed.

Theorem verified_systems_local_choice_preserves_local_choice_authority :
  forall model,
    SystemsLocalRuntimeChoiceVerificationSuccess model ->
    systemsLocalChoiceNameExact model = true /\
    systemsLocalChoiceInputsEmpty model = true /\
    systemsLocalChoiceSiteAbsent model = true /\
    systemsLocalChoiceRepresentedAsSessionOffer model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_local_choice_success_name model H).
  - exact (systems_local_choice_success_inputs_empty model H).
  - exact (systems_local_choice_success_site_absent model H).
  - exact (systems_local_choice_success_not_session_offer model H).
Qed.

Theorem verified_systems_local_choice_preserves_exact_none_some_arms :
  forall model,
    SystemsLocalRuntimeChoiceVerificationSuccess model ->
    systemsLocalChoiceNoneLabelExact model = true /\
    systemsLocalChoiceSomeLabelExact model = true /\
    systemsLocalChoiceNonePayloadPresent model = false /\
    systemsLocalChoiceSomePayloadPresent model = true /\
    systemsLocalChoiceActualNoneTarget model =
      systemsLocalChoiceWitnessNoneTarget model /\
    systemsLocalChoiceActualSomeTarget model =
      systemsLocalChoiceWitnessSomeTarget model.
Proof.
  intros model H; repeat split.
  - exact (systems_local_choice_success_none_label model H).
  - exact (systems_local_choice_success_some_label model H).
  - exact (systems_local_choice_success_none_payload_absent model H).
  - exact (systems_local_choice_success_some_payload_present model H).
  - exact (systems_local_choice_success_none_target model H).
  - exact (systems_local_choice_success_some_target model H).
Qed.

Theorem verified_systems_local_choice_preserves_branch_local_selected_version :
  forall model,
    SystemsLocalRuntimeChoiceVerificationSuccess model ->
    systemsLocalChoiceActualSelectedVersion model =
      systemsLocalChoiceWitnessSelectedVersion model /\
    systemsLocalChoiceSelectedVersionIsUInt16 model = true /\
    systemsLocalChoiceBinderAtSomeTargetEntry model = true /\
    systemsLocalChoiceSomeTargetHasSoleChoicePredecessor model = true /\
    systemsLocalChoiceNoneArmUsesSelectedVersion model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_local_choice_success_selected_version model H).
  - exact (systems_local_choice_success_selected_version_u16 model H).
  - exact (systems_local_choice_success_binder_entry model H).
  - exact (systems_local_choice_success_sole_predecessor model H).
  - exact (systems_local_choice_success_no_none_arm_use model H).
Qed.

Theorem verified_systems_local_choice_preserves_exact_version_consumer :
  forall model,
    SystemsLocalRuntimeChoiceVerificationSuccess model ->
    systemsLocalChoiceVersionSelectConsumesExactPair model = true /\
    systemsLocalChoiceVersionSelectTransportFirst model = true /\
    systemsLocalChoiceVersionSelectIsSemanticSessionSelect model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_local_choice_success_version_select_pair model H).
  - exact (systems_local_choice_success_version_select_order model H).
  - exact (systems_local_choice_success_version_select_still_generic model H).
Qed.

Theorem verified_systems_local_choice_eliminates_legacy_boolean_projection :
  forall model,
    SystemsLocalRuntimeChoiceVerificationSuccess model ->
    systemsLocalChoiceLegacyDiscriminatorPresent model = false /\
    systemsLocalChoiceLegacyChooseCallPresent model = false.
Proof.
  intros model H; split.
  - exact (systems_local_choice_success_no_legacy_discriminator model H).
  - exact (systems_local_choice_success_no_legacy_choose_call model H).
Qed.

Theorem verified_systems_local_choice_transfers_invariant_and_lowering_authority :
  forall model,
    SystemsLocalRuntimeChoiceVerificationSuccess model ->
    systemsLocalChoiceActualInvariant model =
      systemsLocalChoiceWitnessInvariant model /\
    systemsLocalChoiceInvariantRuntimeChoiceExact model = true /\
    systemsLocalChoiceActualLoweringDecision model =
      systemsLocalChoiceWitnessLoweringDecision model /\
    systemsLocalChoiceLoweringDecisionExact model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_local_choice_success_invariant_identity model H).
  - exact (systems_local_choice_success_invariant_shape model H).
  - exact (systems_local_choice_success_lowering_identity model H).
  - exact (systems_local_choice_success_lowering_exact model H).
Qed.

Theorem systems_local_choice_authority_or_arm_drift_is_rejected :
  forall model,
    systemsLocalChoiceNameExact model = false \/
    systemsLocalChoiceInputsEmpty model = false \/
    systemsLocalChoiceSiteAbsent model = false \/
    systemsLocalChoiceRepresentedAsSessionOffer model = true \/
    systemsLocalChoiceNoneLabelExact model = false \/
    systemsLocalChoiceSomeLabelExact model = false \/
    systemsLocalChoiceNonePayloadPresent model = true \/
    systemsLocalChoiceSomePayloadPresent model = false ->
    ~ SystemsLocalRuntimeChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hn | [Hi | [Hs | [Hoffer | [Hnone | [Hsome | [Hnp | Hsp]]]]]]].
  - rewrite (systems_local_choice_success_name model H) in Hn. discriminate.
  - rewrite (systems_local_choice_success_inputs_empty model H) in Hi. discriminate.
  - rewrite (systems_local_choice_success_site_absent model H) in Hs. discriminate.
  - rewrite (systems_local_choice_success_not_session_offer model H) in Hoffer. discriminate.
  - rewrite (systems_local_choice_success_none_label model H) in Hnone. discriminate.
  - rewrite (systems_local_choice_success_some_label model H) in Hsome. discriminate.
  - rewrite (systems_local_choice_success_none_payload_absent model H) in Hnp. discriminate.
  - rewrite (systems_local_choice_success_some_payload_present model H) in Hsp. discriminate.
Qed.

Theorem systems_local_choice_payload_or_predecessor_drift_is_rejected :
  forall model,
    systemsLocalChoiceActualSelectedVersion model <>
      systemsLocalChoiceWitnessSelectedVersion model \/
    systemsLocalChoiceSelectedVersionIsUInt16 model = false \/
    systemsLocalChoiceBinderAtSomeTargetEntry model = false \/
    systemsLocalChoiceSomeTargetHasSoleChoicePredecessor model = false \/
    systemsLocalChoiceNoneArmUsesSelectedVersion model = true ->
    ~ SystemsLocalRuntimeChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hid | [Hu16 | [Hentry | [Hpred | Hnone]]]].
  - apply Hid. exact (systems_local_choice_success_selected_version model H).
  - rewrite (systems_local_choice_success_selected_version_u16 model H) in Hu16. discriminate.
  - rewrite (systems_local_choice_success_binder_entry model H) in Hentry. discriminate.
  - rewrite (systems_local_choice_success_sole_predecessor model H) in Hpred. discriminate.
  - rewrite (systems_local_choice_success_no_none_arm_use model H) in Hnone. discriminate.
Qed.

Theorem systems_local_choice_consumer_legacy_or_invariant_drift_is_rejected :
  forall model,
    systemsLocalChoiceVersionSelectConsumesExactPair model = false \/
    systemsLocalChoiceVersionSelectTransportFirst model = false \/
    systemsLocalChoiceVersionSelectIsSemanticSessionSelect model = true \/
    systemsLocalChoiceLegacyDiscriminatorPresent model = true \/
    systemsLocalChoiceLegacyChooseCallPresent model = true \/
    systemsLocalChoiceActualInvariant model <>
      systemsLocalChoiceWitnessInvariant model \/
    systemsLocalChoiceInvariantRuntimeChoiceExact model = false \/
    systemsLocalChoiceActualLoweringDecision model <>
      systemsLocalChoiceWitnessLoweringDecision model \/
    systemsLocalChoiceLoweringDecisionExact model = false ->
    ~ SystemsLocalRuntimeChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hpair | [Horder | [Hsemantic | [Hdisc | [Hcall | [Hinv | [Hshape | [Hdec | Hexact]]]]]]]].
  - rewrite (systems_local_choice_success_version_select_pair model H) in Hpair. discriminate.
  - rewrite (systems_local_choice_success_version_select_order model H) in Horder. discriminate.
  - rewrite (systems_local_choice_success_version_select_still_generic model H) in Hsemantic. discriminate.
  - rewrite (systems_local_choice_success_no_legacy_discriminator model H) in Hdisc. discriminate.
  - rewrite (systems_local_choice_success_no_legacy_choose_call model H) in Hcall. discriminate.
  - apply Hinv. exact (systems_local_choice_success_invariant_identity model H).
  - rewrite (systems_local_choice_success_invariant_shape model H) in Hshape. discriminate.
  - apply Hdec. exact (systems_local_choice_success_lowering_identity model H).
  - rewrite (systems_local_choice_success_lowering_exact model H) in Hexact. discriminate.
Qed.
