From Phil.Systems Require Import ScalarDataflow FinalResponse.

(*
  PHIL-SYS-PAYLOAD-CANCEL-001 — normalized proof model for the Phase 0
  payload/cancel semantic session choice introduced by PR #62 and physically
  lowered by PR #64.

  The model keeps the client-local should_cancel decision distinct from the
  peer-visible session labels, preserves exact client/server transport identity
  and payload/cancel continuation duality, records that both protocol arms have
  no payload value, eliminates the historical server Bool discriminator and
  generic label receive/select calls, and reuses proof-bound final-response
  authority for the later accepted/rejected boundary.

  This proof does not choose the physical one-octet encoding.
*)

Definition PayloadCancelBlockId := nat.

Record SystemsPayloadCancelChoiceModel : Type := mkSystemsPayloadCancelChoiceModel {
  systemsPayloadCancelFinalPredecessor : SystemsFinalResponseModel;

  systemsPayloadCancelWitnessClientTransport : ValueId;
  systemsPayloadCancelActualClientTransport : ValueId;
  systemsPayloadCancelClientTransportIsHandle : bool;
  systemsPayloadCancelWitnessServerTransport : ValueId;
  systemsPayloadCancelActualServerTransport : ValueId;
  systemsPayloadCancelServerTransportIsHandle : bool;

  systemsPayloadCancelPayloadLabelExact : bool;
  systemsPayloadCancelCancelLabelExact : bool;
  systemsPayloadCancelClientPayloadHasNoPayload : bool;
  systemsPayloadCancelClientCancelHasNoPayload : bool;
  systemsPayloadCancelServerPayloadHasNoPayload : bool;
  systemsPayloadCancelServerCancelHasNoPayload : bool;

  systemsPayloadCancelWitnessPayloadTarget : PayloadCancelBlockId;
  systemsPayloadCancelActualPayloadTarget : PayloadCancelBlockId;
  systemsPayloadCancelWitnessCancelTarget : PayloadCancelBlockId;
  systemsPayloadCancelActualCancelTarget : PayloadCancelBlockId;
  systemsPayloadCancelPayloadSelectCount : nat;
  systemsPayloadCancelCancelSelectCount : nat;
  systemsPayloadCancelServerOfferCount : nat;

  systemsPayloadCancelWitnessLocalDecision : ValueId;
  systemsPayloadCancelActualLocalDecision : ValueId;
  systemsPayloadCancelLocalDecisionIsBool : bool;
  systemsPayloadCancelLocalDecisionBranchExact : bool;
  systemsPayloadCancelLocalDecisionIsSessionState : bool;

  systemsPayloadCancelLegacyServerDiscriminatorPresent : bool;
  systemsPayloadCancelLegacyServerReceivePresent : bool;
  systemsPayloadCancelLegacyClientSelectPresent : bool
}.

Record SystemsPayloadCancelChoiceVerificationSuccess
  (model : SystemsPayloadCancelChoiceModel) : Prop :=
  mkSystemsPayloadCancelChoiceVerificationSuccess {
    systems_payload_cancel_success_final_authority :
      SystemsFinalResponseVerificationSuccess
        (systemsPayloadCancelFinalPredecessor model);

    systems_payload_cancel_success_client_transport :
      systemsPayloadCancelActualClientTransport model =
        systemsPayloadCancelWitnessClientTransport model;
    systems_payload_cancel_success_client_transport_role :
      systemsPayloadCancelClientTransportIsHandle model = true;
    systems_payload_cancel_success_server_transport :
      systemsPayloadCancelActualServerTransport model =
        systemsPayloadCancelWitnessServerTransport model;
    systems_payload_cancel_success_server_transport_role :
      systemsPayloadCancelServerTransportIsHandle model = true;

    systems_payload_cancel_success_payload_label :
      systemsPayloadCancelPayloadLabelExact model = true;
    systems_payload_cancel_success_cancel_label :
      systemsPayloadCancelCancelLabelExact model = true;
    systems_payload_cancel_success_client_payload_no_payload :
      systemsPayloadCancelClientPayloadHasNoPayload model = true;
    systems_payload_cancel_success_client_cancel_no_payload :
      systemsPayloadCancelClientCancelHasNoPayload model = true;
    systems_payload_cancel_success_server_payload_no_payload :
      systemsPayloadCancelServerPayloadHasNoPayload model = true;
    systems_payload_cancel_success_server_cancel_no_payload :
      systemsPayloadCancelServerCancelHasNoPayload model = true;

    systems_payload_cancel_success_payload_target :
      systemsPayloadCancelActualPayloadTarget model =
        systemsPayloadCancelWitnessPayloadTarget model;
    systems_payload_cancel_success_cancel_target :
      systemsPayloadCancelActualCancelTarget model =
        systemsPayloadCancelWitnessCancelTarget model;
    systems_payload_cancel_success_payload_select_once :
      systemsPayloadCancelPayloadSelectCount model = 1;
    systems_payload_cancel_success_cancel_select_once :
      systemsPayloadCancelCancelSelectCount model = 1;
    systems_payload_cancel_success_server_offer_once :
      systemsPayloadCancelServerOfferCount model = 1;

    systems_payload_cancel_success_local_decision :
      systemsPayloadCancelActualLocalDecision model =
        systemsPayloadCancelWitnessLocalDecision model;
    systems_payload_cancel_success_local_decision_role :
      systemsPayloadCancelLocalDecisionIsBool model = true;
    systems_payload_cancel_success_local_branch :
      systemsPayloadCancelLocalDecisionBranchExact model = true;
    systems_payload_cancel_success_local_not_session :
      systemsPayloadCancelLocalDecisionIsSessionState model = false;

    systems_payload_cancel_success_no_legacy_discriminator :
      systemsPayloadCancelLegacyServerDiscriminatorPresent model = false;
    systems_payload_cancel_success_no_legacy_receive :
      systemsPayloadCancelLegacyServerReceivePresent model = false;
    systems_payload_cancel_success_no_legacy_select :
      systemsPayloadCancelLegacyClientSelectPresent model = false
  }.

Theorem verified_systems_payload_cancel_reuses_final_response_authority :
  forall model,
    SystemsPayloadCancelChoiceVerificationSuccess model ->
    SystemsFinalResponseVerificationSuccess
      (systemsPayloadCancelFinalPredecessor model).
Proof.
  intros model H.
  exact (systems_payload_cancel_success_final_authority model H).
Qed.

Theorem verified_systems_payload_cancel_preserves_exact_transports :
  forall model,
    SystemsPayloadCancelChoiceVerificationSuccess model ->
    systemsPayloadCancelActualClientTransport model =
      systemsPayloadCancelWitnessClientTransport model /\
    systemsPayloadCancelClientTransportIsHandle model = true /\
    systemsPayloadCancelActualServerTransport model =
      systemsPayloadCancelWitnessServerTransport model /\
    systemsPayloadCancelServerTransportIsHandle model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_payload_cancel_success_client_transport model H).
  - exact (systems_payload_cancel_success_client_transport_role model H).
  - exact (systems_payload_cancel_success_server_transport model H).
  - exact (systems_payload_cancel_success_server_transport_role model H).
Qed.

Theorem verified_systems_payload_cancel_preserves_dual_labels_targets_and_no_payloads :
  forall model,
    SystemsPayloadCancelChoiceVerificationSuccess model ->
    systemsPayloadCancelPayloadLabelExact model = true /\
    systemsPayloadCancelCancelLabelExact model = true /\
    systemsPayloadCancelActualPayloadTarget model =
      systemsPayloadCancelWitnessPayloadTarget model /\
    systemsPayloadCancelActualCancelTarget model =
      systemsPayloadCancelWitnessCancelTarget model /\
    systemsPayloadCancelClientPayloadHasNoPayload model = true /\
    systemsPayloadCancelClientCancelHasNoPayload model = true /\
    systemsPayloadCancelServerPayloadHasNoPayload model = true /\
    systemsPayloadCancelServerCancelHasNoPayload model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_payload_cancel_success_payload_label model H).
  - exact (systems_payload_cancel_success_cancel_label model H).
  - exact (systems_payload_cancel_success_payload_target model H).
  - exact (systems_payload_cancel_success_cancel_target model H).
  - exact (systems_payload_cancel_success_client_payload_no_payload model H).
  - exact (systems_payload_cancel_success_client_cancel_no_payload model H).
  - exact (systems_payload_cancel_success_server_payload_no_payload model H).
  - exact (systems_payload_cancel_success_server_cancel_no_payload model H).
Qed.

Theorem verified_systems_payload_cancel_has_exact_choice_multiplicity :
  forall model,
    SystemsPayloadCancelChoiceVerificationSuccess model ->
    systemsPayloadCancelPayloadSelectCount model = 1 /\
    systemsPayloadCancelCancelSelectCount model = 1 /\
    systemsPayloadCancelServerOfferCount model = 1.
Proof.
  intros model H; repeat split.
  - exact (systems_payload_cancel_success_payload_select_once model H).
  - exact (systems_payload_cancel_success_cancel_select_once model H).
  - exact (systems_payload_cancel_success_server_offer_once model H).
Qed.

Theorem verified_systems_payload_cancel_keeps_should_cancel_local :
  forall model,
    SystemsPayloadCancelChoiceVerificationSuccess model ->
    systemsPayloadCancelActualLocalDecision model =
      systemsPayloadCancelWitnessLocalDecision model /\
    systemsPayloadCancelLocalDecisionIsBool model = true /\
    systemsPayloadCancelLocalDecisionBranchExact model = true /\
    systemsPayloadCancelLocalDecisionIsSessionState model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_payload_cancel_success_local_decision model H).
  - exact (systems_payload_cancel_success_local_decision_role model H).
  - exact (systems_payload_cancel_success_local_branch model H).
  - exact (systems_payload_cancel_success_local_not_session model H).
Qed.

Theorem verified_systems_payload_cancel_eliminates_legacy_protocol_state :
  forall model,
    SystemsPayloadCancelChoiceVerificationSuccess model ->
    systemsPayloadCancelLegacyServerDiscriminatorPresent model = false /\
    systemsPayloadCancelLegacyServerReceivePresent model = false /\
    systemsPayloadCancelLegacyClientSelectPresent model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_payload_cancel_success_no_legacy_discriminator model H).
  - exact (systems_payload_cancel_success_no_legacy_receive model H).
  - exact (systems_payload_cancel_success_no_legacy_select model H).
Qed.

Theorem systems_payload_cancel_transport_or_label_drift_is_rejected :
  forall model,
    systemsPayloadCancelActualClientTransport model <>
      systemsPayloadCancelWitnessClientTransport model \/
    systemsPayloadCancelClientTransportIsHandle model = false \/
    systemsPayloadCancelActualServerTransport model <>
      systemsPayloadCancelWitnessServerTransport model \/
    systemsPayloadCancelServerTransportIsHandle model = false \/
    systemsPayloadCancelPayloadLabelExact model = false \/
    systemsPayloadCancelCancelLabelExact model = false ->
    ~ SystemsPayloadCancelChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hct | [Hcr | [Hst | [Hsr | [Hp | Hc]]]]].
  - apply Hct. exact (systems_payload_cancel_success_client_transport model H).
  - rewrite (systems_payload_cancel_success_client_transport_role model H) in Hcr. discriminate.
  - apply Hst. exact (systems_payload_cancel_success_server_transport model H).
  - rewrite (systems_payload_cancel_success_server_transport_role model H) in Hsr. discriminate.
  - rewrite (systems_payload_cancel_success_payload_label model H) in Hp. discriminate.
  - rewrite (systems_payload_cancel_success_cancel_label model H) in Hc. discriminate.
Qed.

Theorem systems_payload_cancel_target_payload_or_multiplicity_drift_is_rejected :
  forall model,
    systemsPayloadCancelActualPayloadTarget model <>
      systemsPayloadCancelWitnessPayloadTarget model \/
    systemsPayloadCancelActualCancelTarget model <>
      systemsPayloadCancelWitnessCancelTarget model \/
    systemsPayloadCancelClientPayloadHasNoPayload model = false \/
    systemsPayloadCancelClientCancelHasNoPayload model = false \/
    systemsPayloadCancelServerPayloadHasNoPayload model = false \/
    systemsPayloadCancelServerCancelHasNoPayload model = false \/
    systemsPayloadCancelPayloadSelectCount model <> 1 \/
    systemsPayloadCancelCancelSelectCount model <> 1 \/
    systemsPayloadCancelServerOfferCount model <> 1 ->
    ~ SystemsPayloadCancelChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hpt | [Hct | [Hcp | [Hcc | [Hsp | [Hsc | [Hps | [Hcs | Hso]]]]]]]].
  - apply Hpt. exact (systems_payload_cancel_success_payload_target model H).
  - apply Hct. exact (systems_payload_cancel_success_cancel_target model H).
  - rewrite (systems_payload_cancel_success_client_payload_no_payload model H) in Hcp. discriminate.
  - rewrite (systems_payload_cancel_success_client_cancel_no_payload model H) in Hcc. discriminate.
  - rewrite (systems_payload_cancel_success_server_payload_no_payload model H) in Hsp. discriminate.
  - rewrite (systems_payload_cancel_success_server_cancel_no_payload model H) in Hsc. discriminate.
  - apply Hps. exact (systems_payload_cancel_success_payload_select_once model H).
  - apply Hcs. exact (systems_payload_cancel_success_cancel_select_once model H).
  - apply Hso. exact (systems_payload_cancel_success_server_offer_once model H).
Qed.

Theorem systems_payload_cancel_local_or_legacy_conflation_is_rejected :
  forall model,
    systemsPayloadCancelActualLocalDecision model <>
      systemsPayloadCancelWitnessLocalDecision model \/
    systemsPayloadCancelLocalDecisionIsBool model = false \/
    systemsPayloadCancelLocalDecisionBranchExact model = false \/
    systemsPayloadCancelLocalDecisionIsSessionState model = true \/
    systemsPayloadCancelLegacyServerDiscriminatorPresent model = true \/
    systemsPayloadCancelLegacyServerReceivePresent model = true \/
    systemsPayloadCancelLegacyClientSelectPresent model = true ->
    ~ SystemsPayloadCancelChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hd | [Hr | [Hb | [Hs | [Hld | [Hlr | Hls]]]]]].
  - apply Hd. exact (systems_payload_cancel_success_local_decision model H).
  - rewrite (systems_payload_cancel_success_local_decision_role model H) in Hr. discriminate.
  - rewrite (systems_payload_cancel_success_local_branch model H) in Hb. discriminate.
  - rewrite (systems_payload_cancel_success_local_not_session model H) in Hs. discriminate.
  - rewrite (systems_payload_cancel_success_no_legacy_discriminator model H) in Hld. discriminate.
  - rewrite (systems_payload_cancel_success_no_legacy_receive model H) in Hlr. discriminate.
  - rewrite (systems_payload_cancel_success_no_legacy_select model H) in Hls. discriminate.
Qed.
