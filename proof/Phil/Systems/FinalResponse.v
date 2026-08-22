From Phil.Systems Require Import ScalarDataflow RejectedResponse.

(*
  PHIL-SYS-FINAL-RESPONSE-001 — normalized proof model for the Phase 0
  client-side final accepted(id) / rejected(reason) session offer introduced by
  PR #57 and physically lowered by PR #59.

  The model preserves the exact client transport, exact accepted/rejected label
  to payload/continuation relation, branch-local UploadId and DigestFailure
  bindings, exact accepted record_upload_id use, exact-program non-use of the
  rejected DigestFailure, and removal of the legacy anonymous Boolean/generic
  receive-label representation.

  This proof does not choose the physical decoder ABI or wire encoding.
*)

Record SystemsFinalResponseModel : Type := mkSystemsFinalResponseModel {
  systemsFinalRejectedPredecessor : SystemsRejectedResponseModel;

  systemsFinalWitnessTransport : ValueId;
  systemsFinalActualTransport : ValueId;
  systemsFinalTransportIsHandle : bool;

  systemsFinalOfferIdentityExact : bool;
  systemsFinalAcceptedLabelExact : bool;
  systemsFinalRejectedLabelExact : bool;

  systemsFinalWitnessAcceptedPayload : ValueId;
  systemsFinalActualAcceptedPayload : ValueId;
  systemsFinalAcceptedPayloadIsUploadId : bool;
  systemsFinalWitnessRejectedPayload : ValueId;
  systemsFinalActualRejectedPayload : ValueId;
  systemsFinalRejectedPayloadIsDigestFailure : bool;

  systemsFinalWitnessAcceptedTarget : DigestBlockId;
  systemsFinalActualAcceptedTarget : DigestBlockId;
  systemsFinalWitnessRejectedTarget : DigestBlockId;
  systemsFinalActualRejectedTarget : DigestBlockId;

  systemsFinalAcceptedDedicatedBinder : bool;
  systemsFinalAcceptedSoleOfferPredecessor : bool;
  systemsFinalRejectedDedicatedBinder : bool;
  systemsFinalRejectedSoleOfferPredecessor : bool;

  systemsFinalRecordUploadIdPayload : ValueId;
  systemsFinalAcceptedRecordUseCount : nat;
  systemsFinalRejectedPayloadUseCount : nat;
  systemsFinalAcceptedPayloadEscapesRejected : bool;
  systemsFinalRejectedPayloadEscapesAccepted : bool;

  systemsFinalLegacyBooleanPresent : bool;
  systemsFinalLegacyReceiveCallPresent : bool;
  systemsFinalAcceptedTerminatesSuccess : bool;
  systemsFinalRejectedTerminatesFailure : bool
}.

Record SystemsFinalResponseVerificationSuccess
  (model : SystemsFinalResponseModel) : Prop :=
  mkSystemsFinalResponseVerificationSuccess {
    systems_final_success_rejected_authority :
      SystemsRejectedResponseVerificationSuccess
        (systemsFinalRejectedPredecessor model);

    systems_final_success_transport :
      systemsFinalActualTransport model = systemsFinalWitnessTransport model;
    systems_final_success_transport_role :
      systemsFinalTransportIsHandle model = true;

    systems_final_success_offer_identity :
      systemsFinalOfferIdentityExact model = true;
    systems_final_success_accepted_label :
      systemsFinalAcceptedLabelExact model = true;
    systems_final_success_rejected_label :
      systemsFinalRejectedLabelExact model = true;

    systems_final_success_accepted_payload :
      systemsFinalActualAcceptedPayload model =
        systemsFinalWitnessAcceptedPayload model;
    systems_final_success_accepted_payload_role :
      systemsFinalAcceptedPayloadIsUploadId model = true;
    systems_final_success_rejected_payload :
      systemsFinalActualRejectedPayload model =
        systemsFinalWitnessRejectedPayload model;
    systems_final_success_rejected_payload_role :
      systemsFinalRejectedPayloadIsDigestFailure model = true;

    systems_final_success_accepted_target :
      systemsFinalActualAcceptedTarget model =
        systemsFinalWitnessAcceptedTarget model;
    systems_final_success_rejected_target :
      systemsFinalActualRejectedTarget model =
        systemsFinalWitnessRejectedTarget model;

    systems_final_success_accepted_binder :
      systemsFinalAcceptedDedicatedBinder model = true;
    systems_final_success_accepted_predecessor :
      systemsFinalAcceptedSoleOfferPredecessor model = true;
    systems_final_success_rejected_binder :
      systemsFinalRejectedDedicatedBinder model = true;
    systems_final_success_rejected_binder_predecessor :
      systemsFinalRejectedSoleOfferPredecessor model = true;

    systems_final_success_record_exact :
      systemsFinalRecordUploadIdPayload model =
        systemsFinalActualAcceptedPayload model;
    systems_final_success_record_once :
      systemsFinalAcceptedRecordUseCount model = 1;
    systems_final_success_rejected_unused :
      systemsFinalRejectedPayloadUseCount model = 0;
    systems_final_success_no_accepted_escape :
      systemsFinalAcceptedPayloadEscapesRejected model = false;
    systems_final_success_no_rejected_escape :
      systemsFinalRejectedPayloadEscapesAccepted model = false;

    systems_final_success_no_legacy_boolean :
      systemsFinalLegacyBooleanPresent model = false;
    systems_final_success_no_legacy_receive :
      systemsFinalLegacyReceiveCallPresent model = false;
    systems_final_success_accepted_termination :
      systemsFinalAcceptedTerminatesSuccess model = true;
    systems_final_success_rejected_termination :
      systemsFinalRejectedTerminatesFailure model = true
  }.

Theorem verified_systems_final_response_reuses_rejected_authority :
  forall model,
    SystemsFinalResponseVerificationSuccess model ->
    SystemsRejectedResponseVerificationSuccess
      (systemsFinalRejectedPredecessor model).
Proof.
  intros model H.
  exact (systems_final_success_rejected_authority model H).
Qed.

Theorem verified_systems_final_response_preserves_exact_offer :
  forall model,
    SystemsFinalResponseVerificationSuccess model ->
    systemsFinalActualTransport model = systemsFinalWitnessTransport model /\
    systemsFinalTransportIsHandle model = true /\
    systemsFinalOfferIdentityExact model = true /\
    systemsFinalAcceptedLabelExact model = true /\
    systemsFinalRejectedLabelExact model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_final_success_transport model H).
  - exact (systems_final_success_transport_role model H).
  - exact (systems_final_success_offer_identity model H).
  - exact (systems_final_success_accepted_label model H).
  - exact (systems_final_success_rejected_label model H).
Qed.

Theorem verified_systems_final_response_preserves_branch_payloads_and_targets :
  forall model,
    SystemsFinalResponseVerificationSuccess model ->
    systemsFinalActualAcceptedPayload model =
      systemsFinalWitnessAcceptedPayload model /\
    systemsFinalAcceptedPayloadIsUploadId model = true /\
    systemsFinalActualAcceptedTarget model =
      systemsFinalWitnessAcceptedTarget model /\
    systemsFinalActualRejectedPayload model =
      systemsFinalWitnessRejectedPayload model /\
    systemsFinalRejectedPayloadIsDigestFailure model = true /\
    systemsFinalActualRejectedTarget model =
      systemsFinalWitnessRejectedTarget model.
Proof.
  intros model H; repeat split.
  - exact (systems_final_success_accepted_payload model H).
  - exact (systems_final_success_accepted_payload_role model H).
  - exact (systems_final_success_accepted_target model H).
  - exact (systems_final_success_rejected_payload model H).
  - exact (systems_final_success_rejected_payload_role model H).
  - exact (systems_final_success_rejected_target model H).
Qed.

Theorem verified_systems_final_response_preserves_branch_locality :
  forall model,
    SystemsFinalResponseVerificationSuccess model ->
    systemsFinalAcceptedDedicatedBinder model = true /\
    systemsFinalAcceptedSoleOfferPredecessor model = true /\
    systemsFinalRejectedDedicatedBinder model = true /\
    systemsFinalRejectedSoleOfferPredecessor model = true /\
    systemsFinalAcceptedPayloadEscapesRejected model = false /\
    systemsFinalRejectedPayloadEscapesAccepted model = false.
Proof.
  intros model H; repeat split.
  - exact (systems_final_success_accepted_binder model H).
  - exact (systems_final_success_accepted_predecessor model H).
  - exact (systems_final_success_rejected_binder model H).
  - exact (systems_final_success_rejected_binder_predecessor model H).
  - exact (systems_final_success_no_accepted_escape model H).
  - exact (systems_final_success_no_rejected_escape model H).
Qed.

Theorem verified_systems_final_response_records_accepted_id_and_erases_no_semantics :
  forall model,
    SystemsFinalResponseVerificationSuccess model ->
    systemsFinalRecordUploadIdPayload model =
      systemsFinalWitnessAcceptedPayload model /\
    systemsFinalAcceptedRecordUseCount model = 1 /\
    systemsFinalRejectedPayloadUseCount model = 0.
Proof.
  intros model H; repeat split.
  - rewrite (systems_final_success_record_exact model H).
    exact (systems_final_success_accepted_payload model H).
  - exact (systems_final_success_record_once model H).
  - exact (systems_final_success_rejected_unused model H).
Qed.

Theorem verified_systems_final_response_eliminates_legacy_boolean_and_preserves_outcomes :
  forall model,
    SystemsFinalResponseVerificationSuccess model ->
    systemsFinalLegacyBooleanPresent model = false /\
    systemsFinalLegacyReceiveCallPresent model = false /\
    systemsFinalAcceptedTerminatesSuccess model = true /\
    systemsFinalRejectedTerminatesFailure model = true.
Proof.
  intros model H; repeat split.
  - exact (systems_final_success_no_legacy_boolean model H).
  - exact (systems_final_success_no_legacy_receive model H).
  - exact (systems_final_success_accepted_termination model H).
  - exact (systems_final_success_rejected_termination model H).
Qed.

Theorem systems_final_response_offer_or_transport_drift_is_rejected :
  forall model,
    systemsFinalActualTransport model <> systemsFinalWitnessTransport model \/
    systemsFinalTransportIsHandle model = false \/
    systemsFinalOfferIdentityExact model = false \/
    systemsFinalAcceptedLabelExact model = false \/
    systemsFinalRejectedLabelExact model = false ->
    ~ SystemsFinalResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Ht | [Hr | [Ho | [Ha | Hrej]]]].
  - apply Ht. exact (systems_final_success_transport model H).
  - rewrite (systems_final_success_transport_role model H) in Hr. discriminate.
  - rewrite (systems_final_success_offer_identity model H) in Ho. discriminate.
  - rewrite (systems_final_success_accepted_label model H) in Ha. discriminate.
  - rewrite (systems_final_success_rejected_label model H) in Hrej. discriminate.
Qed.

Theorem systems_final_response_payload_target_or_binder_drift_is_rejected :
  forall model,
    systemsFinalActualAcceptedPayload model <>
      systemsFinalWitnessAcceptedPayload model \/
    systemsFinalAcceptedPayloadIsUploadId model = false \/
    systemsFinalActualRejectedPayload model <>
      systemsFinalWitnessRejectedPayload model \/
    systemsFinalRejectedPayloadIsDigestFailure model = false \/
    systemsFinalActualAcceptedTarget model <>
      systemsFinalWitnessAcceptedTarget model \/
    systemsFinalActualRejectedTarget model <>
      systemsFinalWitnessRejectedTarget model \/
    systemsFinalAcceptedDedicatedBinder model = false \/
    systemsFinalRejectedDedicatedBinder model = false ->
    ~ SystemsFinalResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hap | [Har | [Hrp | [Hrr | [Hat | [Hrt | [Hab | Hrb]]]]]]].
  - apply Hap. exact (systems_final_success_accepted_payload model H).
  - rewrite (systems_final_success_accepted_payload_role model H) in Har. discriminate.
  - apply Hrp. exact (systems_final_success_rejected_payload model H).
  - rewrite (systems_final_success_rejected_payload_role model H) in Hrr. discriminate.
  - apply Hat. exact (systems_final_success_accepted_target model H).
  - apply Hrt. exact (systems_final_success_rejected_target model H).
  - rewrite (systems_final_success_accepted_binder model H) in Hab. discriminate.
  - rewrite (systems_final_success_rejected_binder model H) in Hrb. discriminate.
Qed.

Theorem systems_final_response_use_escape_or_legacy_drift_is_rejected :
  forall model,
    systemsFinalRecordUploadIdPayload model <>
      systemsFinalActualAcceptedPayload model \/
    systemsFinalAcceptedRecordUseCount model <> 1 \/
    systemsFinalRejectedPayloadUseCount model <> 0 \/
    systemsFinalAcceptedPayloadEscapesRejected model = true \/
    systemsFinalRejectedPayloadEscapesAccepted model = true \/
    systemsFinalLegacyBooleanPresent model = true \/
    systemsFinalLegacyReceiveCallPresent model = true ->
    ~ SystemsFinalResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hr | [Hrc | [Hu | [Hae | [Hre | [Hb | Hrecv]]]]]].
  - apply Hr. exact (systems_final_success_record_exact model H).
  - apply Hrc. exact (systems_final_success_record_once model H).
  - apply Hu. exact (systems_final_success_rejected_unused model H).
  - rewrite (systems_final_success_no_accepted_escape model H) in Hae. discriminate.
  - rewrite (systems_final_success_no_rejected_escape model H) in Hre. discriminate.
  - rewrite (systems_final_success_no_legacy_boolean model H) in Hb. discriminate.
  - rewrite (systems_final_success_no_legacy_receive model H) in Hrecv. discriminate.
Qed.
