From Phil.Systems Require Import ScalarDataflow DigestValidation Storage.

(*
  PHIL-SYS-ACCEPTED-001 — normalized proof model for the Phase 0
  select accepted(id) boundary materialized by PR #54.

  Storage success reaches the exact accepted block.  That block performs
  exactly one select accepted operation with the exact component transport and
  exact semantic UploadId produced by storage, in source order, with no
  outputs or runtime-site/ambient authority.  The UploadId has exactly one
  semantic operation use in the current artifact and the block terminates with
  the exact source success outcome.

  This proof does not choose or validate the concrete 17-octet wire encoding.
  That remains an external runtime gate.
*)

Record SystemsAcceptedResponseModel : Type := mkSystemsAcceptedResponseModel {
  systemsAcceptedStorage : SystemsStorageModel;

  systemsAcceptedWitnessTransport : ValueId;
  systemsAcceptedActualTransport : ValueId;
  systemsAcceptedTransportIsHandle : bool;

  systemsAcceptedWitnessUploadId : ValueId;
  systemsAcceptedActualUploadId : ValueId;
  systemsAcceptedUploadIdIsRuntimeScalar : bool;

  systemsAcceptedWitnessBlock : DigestBlockId;
  systemsAcceptedActualBlock : DigestBlockId;

  systemsAcceptedOperationIsSelectAccepted : bool;
  systemsAcceptedOperationCount : nat;
  systemsAcceptedInputArity : nat;
  systemsAcceptedInput0 : ValueId;
  systemsAcceptedInput1 : ValueId;
  systemsAcceptedOutputArity : nat;
  systemsAcceptedRuntimeSiteAbsent : bool;

  systemsAcceptedUploadIdUseCount : nat;
  systemsAcceptedTerminatesSuccess : bool
}.

Record SystemsAcceptedResponseVerificationSuccess
  (model : SystemsAcceptedResponseModel) : Prop :=
  mkSystemsAcceptedResponseVerificationSuccess {
    systems_accepted_success_storage :
      SystemsStorageVerificationSuccess (systemsAcceptedStorage model);
    systems_accepted_success_storage_result :
      systemsAcceptedWitnessUploadId model =
        systemsStorageWitnessResult (systemsAcceptedStorage model);
    systems_accepted_success_storage_predecessor :
      systemsStorageWitnessSuccess (systemsAcceptedStorage model) =
        systemsAcceptedWitnessBlock model;

    systems_accepted_success_block :
      systemsAcceptedActualBlock model = systemsAcceptedWitnessBlock model;
    systems_accepted_success_transport :
      systemsAcceptedActualTransport model = systemsAcceptedWitnessTransport model;
    systems_accepted_success_transport_role :
      systemsAcceptedTransportIsHandle model = true;
    systems_accepted_success_upload_id :
      systemsAcceptedActualUploadId model = systemsAcceptedWitnessUploadId model;
    systems_accepted_success_upload_id_role :
      systemsAcceptedUploadIdIsRuntimeScalar model = true;

    systems_accepted_success_operation :
      systemsAcceptedOperationIsSelectAccepted model = true;
    systems_accepted_success_single_operation :
      systemsAcceptedOperationCount model = 1;
    systems_accepted_success_input_arity :
      systemsAcceptedInputArity model = 2;
    systems_accepted_success_input0 :
      systemsAcceptedInput0 model = systemsAcceptedActualTransport model;
    systems_accepted_success_input1 :
      systemsAcceptedInput1 model = systemsAcceptedActualUploadId model;
    systems_accepted_success_no_outputs :
      systemsAcceptedOutputArity model = 0;
    systems_accepted_success_no_runtime_site :
      systemsAcceptedRuntimeSiteAbsent model = true;

    systems_accepted_success_unique_upload_use :
      systemsAcceptedUploadIdUseCount model = 1;
    systems_accepted_success_termination :
      systemsAcceptedTerminatesSuccess model = true
  }.

Theorem verified_systems_accepted_reuses_storage_authority :
  forall model,
    SystemsAcceptedResponseVerificationSuccess model ->
    SystemsStorageVerificationSuccess (systemsAcceptedStorage model).
Proof.
  intros model H.
  exact (systems_accepted_success_storage model H).
Qed.

Theorem verified_systems_accepted_reaches_exact_block_from_storage_success :
  forall model,
    SystemsAcceptedResponseVerificationSuccess model ->
    systemsStorageWitnessSuccess (systemsAcceptedStorage model) =
      systemsAcceptedActualBlock model.
Proof.
  intros model H.
  rewrite (systems_accepted_success_block model H).
  exact (systems_accepted_success_storage_predecessor model H).
Qed.

Theorem verified_systems_accepted_uses_exact_transport_and_storage_upload_id :
  forall model,
    SystemsAcceptedResponseVerificationSuccess model ->
    systemsAcceptedActualTransport model = systemsAcceptedWitnessTransport model /\
    systemsAcceptedTransportIsHandle model = true /\
    systemsAcceptedActualUploadId model =
      systemsStorageWitnessResult (systemsAcceptedStorage model) /\
    systemsAcceptedUploadIdIsRuntimeScalar model = true.
Proof.
  intros model H.
  repeat split.
  - exact (systems_accepted_success_transport model H).
  - exact (systems_accepted_success_transport_role model H).
  - rewrite (systems_accepted_success_upload_id model H).
    exact (systems_accepted_success_storage_result model H).
  - exact (systems_accepted_success_upload_id_role model H).
Qed.

Theorem verified_systems_accepted_preserves_exact_ordered_operand_pair :
  forall model,
    SystemsAcceptedResponseVerificationSuccess model ->
    systemsAcceptedOperationIsSelectAccepted model = true /\
    systemsAcceptedOperationCount model = 1 /\
    systemsAcceptedInputArity model = 2 /\
    systemsAcceptedInput0 model = systemsAcceptedWitnessTransport model /\
    systemsAcceptedInput1 model = systemsAcceptedWitnessUploadId model.
Proof.
  intros model H.
  repeat split.
  - exact (systems_accepted_success_operation model H).
  - exact (systems_accepted_success_single_operation model H).
  - exact (systems_accepted_success_input_arity model H).
  - rewrite (systems_accepted_success_input0 model H).
    exact (systems_accepted_success_transport model H).
  - rewrite (systems_accepted_success_input1 model H).
    exact (systems_accepted_success_upload_id model H).
Qed.

Theorem verified_systems_accepted_has_no_outputs_or_runtime_site :
  forall model,
    SystemsAcceptedResponseVerificationSuccess model ->
    systemsAcceptedOutputArity model = 0 /\
    systemsAcceptedRuntimeSiteAbsent model = true.
Proof.
  intros model H.
  split.
  - exact (systems_accepted_success_no_outputs model H).
  - exact (systems_accepted_success_no_runtime_site model H).
Qed.

Theorem verified_systems_accepted_uses_upload_id_once_and_terminates_success :
  forall model,
    SystemsAcceptedResponseVerificationSuccess model ->
    systemsAcceptedUploadIdUseCount model = 1 /\
    systemsAcceptedTerminatesSuccess model = true.
Proof.
  intros model H.
  split.
  - exact (systems_accepted_success_unique_upload_use model H).
  - exact (systems_accepted_success_termination model H).
Qed.

Theorem systems_accepted_transport_drift_is_rejected :
  forall model,
    systemsAcceptedActualTransport model <> systemsAcceptedWitnessTransport model \/
    systemsAcceptedTransportIsHandle model = false ->
    ~ SystemsAcceptedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Htransport | Hrole].
  - apply Htransport. exact (systems_accepted_success_transport model H).
  - rewrite (systems_accepted_success_transport_role model H) in Hrole. discriminate.
Qed.

Theorem systems_accepted_upload_id_drift_is_rejected :
  forall model,
    systemsAcceptedActualUploadId model <> systemsAcceptedWitnessUploadId model \/
    systemsAcceptedUploadIdIsRuntimeScalar model = false \/
    systemsAcceptedWitnessUploadId model <>
      systemsStorageWitnessResult (systemsAcceptedStorage model) ->
    ~ SystemsAcceptedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hid | [Hrole | Hstorage]].
  - apply Hid. exact (systems_accepted_success_upload_id model H).
  - rewrite (systems_accepted_success_upload_id_role model H) in Hrole. discriminate.
  - apply Hstorage. exact (systems_accepted_success_storage_result model H).
Qed.

Theorem systems_accepted_block_or_predecessor_drift_is_rejected :
  forall model,
    systemsAcceptedActualBlock model <> systemsAcceptedWitnessBlock model \/
    systemsStorageWitnessSuccess (systemsAcceptedStorage model) <>
      systemsAcceptedWitnessBlock model ->
    ~ SystemsAcceptedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hblock | Hpred].
  - apply Hblock. exact (systems_accepted_success_block model H).
  - apply Hpred. exact (systems_accepted_success_storage_predecessor model H).
Qed.

Theorem systems_accepted_operation_or_multiplicity_drift_is_rejected :
  forall model,
    systemsAcceptedOperationIsSelectAccepted model = false \/
    systemsAcceptedOperationCount model <> 1 ->
    ~ SystemsAcceptedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hop | Hcount].
  - rewrite (systems_accepted_success_operation model H) in Hop. discriminate.
  - apply Hcount. exact (systems_accepted_success_single_operation model H).
Qed.

Theorem systems_accepted_operand_order_or_arity_drift_is_rejected :
  forall model,
    systemsAcceptedInputArity model <> 2 \/
    systemsAcceptedInput0 model <> systemsAcceptedActualTransport model \/
    systemsAcceptedInput1 model <> systemsAcceptedActualUploadId model ->
    ~ SystemsAcceptedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Harity | [H0 | H1]].
  - apply Harity. exact (systems_accepted_success_input_arity model H).
  - apply H0. exact (systems_accepted_success_input0 model H).
  - apply H1. exact (systems_accepted_success_input1 model H).
Qed.

Theorem systems_accepted_outputs_or_runtime_site_drift_is_rejected :
  forall model,
    systemsAcceptedOutputArity model <> 0 \/
    systemsAcceptedRuntimeSiteAbsent model = false ->
    ~ SystemsAcceptedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Houtputs | Hsite].
  - apply Houtputs. exact (systems_accepted_success_no_outputs model H).
  - rewrite (systems_accepted_success_no_runtime_site model H) in Hsite. discriminate.
Qed.

Theorem systems_accepted_use_count_or_termination_drift_is_rejected :
  forall model,
    systemsAcceptedUploadIdUseCount model <> 1 \/
    systemsAcceptedTerminatesSuccess model = false ->
    ~ SystemsAcceptedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Huses | Hend].
  - apply Huses. exact (systems_accepted_success_unique_upload_use model H).
  - rewrite (systems_accepted_success_termination model H) in Hend. discriminate.
Qed.
