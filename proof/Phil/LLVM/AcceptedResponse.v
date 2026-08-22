From Phil.Systems Require Import ScalarDataflow DigestValidation Storage AcceptedResponse.
From Phil.LLVM Require Import Storage RuntimeSymbolIdentity.

(*
  PHIL-LLVM-ACCEPTED-001 — normalized proof model for accepted-response-v1.

  The exact server transport and exact storage-produced opaque UploadId are
  passed, in source order, to the physical accepted selector.  The call is
  reachable only from storage success and preserves exact source success
  termination.  Generated code must not recover accepted state from ambient
  globals, use the old nullary/generic selector, inspect or release UploadId,
  strengthen its pointer without authority, or derive runtime symbol names from
  assurance evidence.

  The concrete 17-octet provider encoding remains an external runtime gate.
*)

Definition AcceptedOperandId := nat.
Definition AcceptedLLVMBlockId := nat.

Record AcceptedResponseLLVMModel : Type := mkAcceptedResponseLLVMModel {
  llvmAcceptedSystems : SystemsAcceptedResponseModel;
  llvmAcceptedStorage : StorageLLVMModel;
  llvmAcceptedRuntimeSymbols : RuntimeSymbolModel;

  llvmAcceptedTransportSSAFor : ValueId -> AcceptedOperandId;
  llvmAcceptedUploadIdSSAFor : ValueId -> AcceptedOperandId;
  llvmAcceptedBlockSSAFor : DigestBlockId -> AcceptedLLVMBlockId;

  llvmAcceptedExpectedTransportOperand : AcceptedOperandId;
  llvmAcceptedActualTransportOperand : AcceptedOperandId;
  llvmAcceptedExpectedUploadIdOperand : AcceptedOperandId;
  llvmAcceptedActualUploadIdOperand : AcceptedOperandId;

  llvmAcceptedActualBlock : AcceptedLLVMBlockId;
  llvmAcceptedOperandArity : nat;
  llvmAcceptedOperandsInSourceOrder : bool;
  llvmAcceptedUsesPhysicalSelector : bool;
  llvmAcceptedTerminatesSuccess : bool;

  llvmAcceptedGenericCallPresent : bool;
  llvmAcceptedNullarySelectorPresent : bool;
  llvmAcceptedAmbientTransportPresent : bool;
  llvmAcceptedAmbientUploadIdPresent : bool;
  llvmAcceptedAmbientAcceptedStatePresent : bool;
  llvmAcceptedUploadIdLayoutAccessPresent : bool;
  llvmAcceptedUploadIdReleasePresent : bool;
  llvmAcceptedUnauthorizedPointerStrengtheningPresent : bool;
  llvmAcceptedEvidenceDerivedSymbolPresent : bool;
  llvmAcceptedPostStoreReleasePresent : bool
}.

Record AcceptedResponseLLVMVerificationSuccess
  (model : AcceptedResponseLLVMModel) : Prop :=
  mkAcceptedResponseLLVMVerificationSuccess {
    llvm_accepted_success_systems :
      SystemsAcceptedResponseVerificationSuccess (llvmAcceptedSystems model);
    llvm_accepted_success_storage :
      StorageLLVMVerificationSuccess (llvmAcceptedStorage model);
    llvm_accepted_success_runtime_symbols :
      RuntimeSymbolVerificationSuccess (llvmAcceptedRuntimeSymbols model);
    llvm_accepted_success_storage_systems_align :
      llvmStorageSystems (llvmAcceptedStorage model) =
        systemsAcceptedStorage (llvmAcceptedSystems model);

    llvm_accepted_success_expected_transport :
      llvmAcceptedExpectedTransportOperand model =
        llvmAcceptedTransportSSAFor model
          (systemsAcceptedWitnessTransport (llvmAcceptedSystems model));
    llvm_accepted_success_transport_operand :
      llvmAcceptedActualTransportOperand model =
        llvmAcceptedExpectedTransportOperand model;

    llvm_accepted_success_expected_upload_id :
      llvmAcceptedExpectedUploadIdOperand model =
        llvmAcceptedUploadIdSSAFor model
          (systemsAcceptedWitnessUploadId (llvmAcceptedSystems model));
    llvm_accepted_success_storage_upload_id_correspondence :
      llvmStorageActualUploadIdResult (llvmAcceptedStorage model) =
        llvmAcceptedExpectedUploadIdOperand model;
    llvm_accepted_success_upload_id_operand :
      llvmAcceptedActualUploadIdOperand model =
        llvmAcceptedExpectedUploadIdOperand model;

    llvm_accepted_success_block :
      llvmAcceptedActualBlock model =
        llvmAcceptedBlockSSAFor model
          (systemsAcceptedWitnessBlock (llvmAcceptedSystems model));
    llvm_accepted_success_storage_edge :
      llvmStorageActualSuccessBlock (llvmAcceptedStorage model) =
        llvmAcceptedActualBlock model;

    llvm_accepted_success_operand_arity :
      llvmAcceptedOperandArity model = 2;
    llvm_accepted_success_operand_order :
      llvmAcceptedOperandsInSourceOrder model = true;
    llvm_accepted_success_physical_selector :
      llvmAcceptedUsesPhysicalSelector model = true;
    llvm_accepted_success_termination :
      llvmAcceptedTerminatesSuccess model = true;

    llvm_accepted_success_no_generic_call :
      llvmAcceptedGenericCallPresent model = false;
    llvm_accepted_success_no_nullary_selector :
      llvmAcceptedNullarySelectorPresent model = false;
    llvm_accepted_success_no_ambient_transport :
      llvmAcceptedAmbientTransportPresent model = false;
    llvm_accepted_success_no_ambient_upload_id :
      llvmAcceptedAmbientUploadIdPresent model = false;
    llvm_accepted_success_no_ambient_accepted_state :
      llvmAcceptedAmbientAcceptedStatePresent model = false;
    llvm_accepted_success_no_upload_id_layout :
      llvmAcceptedUploadIdLayoutAccessPresent model = false;
    llvm_accepted_success_no_upload_id_release :
      llvmAcceptedUploadIdReleasePresent model = false;
    llvm_accepted_success_no_strengthening :
      llvmAcceptedUnauthorizedPointerStrengtheningPresent model = false;
    llvm_accepted_success_no_evidence_symbol :
      llvmAcceptedEvidenceDerivedSymbolPresent model = false;
    llvm_accepted_success_no_post_store_release :
      llvmAcceptedPostStoreReleasePresent model = false
  }.

Theorem verified_llvm_accepted_reuses_systems_accepted_authority :
  forall model,
    AcceptedResponseLLVMVerificationSuccess model ->
    SystemsAcceptedResponseVerificationSuccess (llvmAcceptedSystems model).
Proof.
  intros model H.
  exact (llvm_accepted_success_systems model H).
Qed.

Theorem verified_llvm_accepted_reuses_storage_authority :
  forall model,
    AcceptedResponseLLVMVerificationSuccess model ->
    StorageLLVMVerificationSuccess (llvmAcceptedStorage model) /\
    llvmStorageSystems (llvmAcceptedStorage model) =
      systemsAcceptedStorage (llvmAcceptedSystems model).
Proof.
  intros model H.
  split.
  - exact (llvm_accepted_success_storage model H).
  - exact (llvm_accepted_success_storage_systems_align model H).
Qed.

Theorem verified_llvm_accepted_reuses_runtime_symbol_authority :
  forall model,
    AcceptedResponseLLVMVerificationSuccess model ->
    RuntimeSymbolVerificationSuccess (llvmAcceptedRuntimeSymbols model).
Proof.
  intros model H.
  exact (llvm_accepted_success_runtime_symbols model H).
Qed.

Theorem verified_llvm_accepted_preserves_exact_transport_operand :
  forall model,
    AcceptedResponseLLVMVerificationSuccess model ->
    llvmAcceptedActualTransportOperand model =
      llvmAcceptedTransportSSAFor model
        (systemsAcceptedWitnessTransport (llvmAcceptedSystems model)).
Proof.
  intros model H.
  rewrite (llvm_accepted_success_transport_operand model H).
  exact (llvm_accepted_success_expected_transport model H).
Qed.

Theorem verified_llvm_accepted_preserves_exact_storage_upload_id_operand :
  forall model,
    AcceptedResponseLLVMVerificationSuccess model ->
    llvmAcceptedActualUploadIdOperand model =
      llvmAcceptedUploadIdSSAFor model
        (systemsAcceptedWitnessUploadId (llvmAcceptedSystems model)) /\
    llvmStorageActualUploadIdResult (llvmAcceptedStorage model) =
      llvmAcceptedActualUploadIdOperand model.
Proof.
  intros model H.
  split.
  - rewrite (llvm_accepted_success_upload_id_operand model H).
    exact (llvm_accepted_success_expected_upload_id model H).
  - rewrite (llvm_accepted_success_upload_id_operand model H).
    exact (llvm_accepted_success_storage_upload_id_correspondence model H).
Qed.

Theorem verified_llvm_accepted_reaches_only_from_storage_success :
  forall model,
    AcceptedResponseLLVMVerificationSuccess model ->
    llvmAcceptedActualBlock model =
      llvmAcceptedBlockSSAFor model
        (systemsAcceptedWitnessBlock (llvmAcceptedSystems model)) /\
    llvmStorageActualSuccessBlock (llvmAcceptedStorage model) =
      llvmAcceptedActualBlock model.
Proof.
  intros model H.
  split.
  - exact (llvm_accepted_success_block model H).
  - exact (llvm_accepted_success_storage_edge model H).
Qed.

Theorem verified_llvm_accepted_preserves_exact_ordered_pair_and_success :
  forall model,
    AcceptedResponseLLVMVerificationSuccess model ->
    llvmAcceptedOperandArity model = 2 /\
    llvmAcceptedOperandsInSourceOrder model = true /\
    llvmAcceptedUsesPhysicalSelector model = true /\
    llvmAcceptedTerminatesSuccess model = true.
Proof.
  intros model H.
  repeat split.
  - exact (llvm_accepted_success_operand_arity model H).
  - exact (llvm_accepted_success_operand_order model H).
  - exact (llvm_accepted_success_physical_selector model H).
  - exact (llvm_accepted_success_termination model H).
Qed.

Theorem verified_llvm_accepted_preserves_upload_id_opacity :
  forall model,
    AcceptedResponseLLVMVerificationSuccess model ->
    llvmAcceptedUploadIdLayoutAccessPresent model = false /\
    llvmAcceptedUploadIdReleasePresent model = false /\
    llvmAcceptedUnauthorizedPointerStrengtheningPresent model = false /\
    llvmAcceptedPostStoreReleasePresent model = false.
Proof.
  intros model H.
  repeat split.
  - exact (llvm_accepted_success_no_upload_id_layout model H).
  - exact (llvm_accepted_success_no_upload_id_release model H).
  - exact (llvm_accepted_success_no_strengthening model H).
  - exact (llvm_accepted_success_no_post_store_release model H).
Qed.

Theorem verified_llvm_accepted_forbids_ambient_nullary_generic_and_evidence_symbols :
  forall model,
    AcceptedResponseLLVMVerificationSuccess model ->
    llvmAcceptedGenericCallPresent model = false /\
    llvmAcceptedNullarySelectorPresent model = false /\
    llvmAcceptedAmbientTransportPresent model = false /\
    llvmAcceptedAmbientUploadIdPresent model = false /\
    llvmAcceptedAmbientAcceptedStatePresent model = false /\
    llvmAcceptedEvidenceDerivedSymbolPresent model = false.
Proof.
  intros model H.
  repeat split.
  - exact (llvm_accepted_success_no_generic_call model H).
  - exact (llvm_accepted_success_no_nullary_selector model H).
  - exact (llvm_accepted_success_no_ambient_transport model H).
  - exact (llvm_accepted_success_no_ambient_upload_id model H).
  - exact (llvm_accepted_success_no_ambient_accepted_state model H).
  - exact (llvm_accepted_success_no_evidence_symbol model H).
Qed.

Theorem llvm_accepted_transport_operand_drift_is_rejected :
  forall model,
    llvmAcceptedActualTransportOperand model <>
      llvmAcceptedExpectedTransportOperand model ->
    ~ AcceptedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (llvm_accepted_success_transport_operand model H).
Qed.

Theorem llvm_accepted_upload_id_operand_drift_is_rejected :
  forall model,
    llvmAcceptedActualUploadIdOperand model <>
      llvmAcceptedExpectedUploadIdOperand model \/
    llvmStorageActualUploadIdResult (llvmAcceptedStorage model) <>
      llvmAcceptedExpectedUploadIdOperand model ->
    ~ AcceptedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hoperand | Hstorage].
  - apply Hoperand. exact (llvm_accepted_success_upload_id_operand model H).
  - apply Hstorage. exact (llvm_accepted_success_storage_upload_id_correspondence model H).
Qed.

Theorem llvm_accepted_block_or_storage_edge_drift_is_rejected :
  forall model,
    llvmAcceptedActualBlock model <>
      llvmAcceptedBlockSSAFor model
        (systemsAcceptedWitnessBlock (llvmAcceptedSystems model)) \/
    llvmStorageActualSuccessBlock (llvmAcceptedStorage model) <>
      llvmAcceptedActualBlock model ->
    ~ AcceptedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hblock | Hedge].
  - apply Hblock. exact (llvm_accepted_success_block model H).
  - apply Hedge. exact (llvm_accepted_success_storage_edge model H).
Qed.

Theorem llvm_accepted_operation_order_or_termination_drift_is_rejected :
  forall model,
    llvmAcceptedOperandArity model <> 2 \/
    llvmAcceptedOperandsInSourceOrder model = false \/
    llvmAcceptedUsesPhysicalSelector model = false \/
    llvmAcceptedTerminatesSuccess model = false ->
    ~ AcceptedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Harity | [Horder | [Hselector | Hend]]].
  - apply Harity. exact (llvm_accepted_success_operand_arity model H).
  - rewrite (llvm_accepted_success_operand_order model H) in Horder. discriminate.
  - rewrite (llvm_accepted_success_physical_selector model H) in Hselector. discriminate.
  - rewrite (llvm_accepted_success_termination model H) in Hend. discriminate.
Qed.

Theorem llvm_accepted_upload_id_representation_drift_is_rejected :
  forall model,
    llvmAcceptedUploadIdLayoutAccessPresent model = true \/
    llvmAcceptedUploadIdReleasePresent model = true \/
    llvmAcceptedUnauthorizedPointerStrengtheningPresent model = true \/
    llvmAcceptedPostStoreReleasePresent model = true ->
    ~ AcceptedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hlayout | [Hrelease | [Hstrengthen | Hpost]]].
  - rewrite (llvm_accepted_success_no_upload_id_layout model H) in Hlayout. discriminate.
  - rewrite (llvm_accepted_success_no_upload_id_release model H) in Hrelease. discriminate.
  - rewrite (llvm_accepted_success_no_strengthening model H) in Hstrengthen. discriminate.
  - rewrite (llvm_accepted_success_no_post_store_release model H) in Hpost. discriminate.
Qed.

Theorem llvm_accepted_ambient_or_symbol_drift_is_rejected :
  forall model,
    llvmAcceptedGenericCallPresent model = true \/
    llvmAcceptedNullarySelectorPresent model = true \/
    llvmAcceptedAmbientTransportPresent model = true \/
    llvmAcceptedAmbientUploadIdPresent model = true \/
    llvmAcceptedAmbientAcceptedStatePresent model = true \/
    llvmAcceptedEvidenceDerivedSymbolPresent model = true ->
    ~ AcceptedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hgeneric | [Hnullary | [Htransport | [Hupload | [Hambient | Hevidence]]]]].
  - rewrite (llvm_accepted_success_no_generic_call model H) in Hgeneric. discriminate.
  - rewrite (llvm_accepted_success_no_nullary_selector model H) in Hnullary. discriminate.
  - rewrite (llvm_accepted_success_no_ambient_transport model H) in Htransport. discriminate.
  - rewrite (llvm_accepted_success_no_ambient_upload_id model H) in Hupload. discriminate.
  - rewrite (llvm_accepted_success_no_ambient_accepted_state model H) in Hambient. discriminate.
  - rewrite (llvm_accepted_success_no_evidence_symbol model H) in Hevidence. discriminate.
Qed.
