From Phil.Systems Require Import ScalarDataflow DigestValidation FinalResponse.
From Phil.LLVM Require Import RejectedResponse RuntimeSymbolIdentity.

(*
  PHIL-LLVM-FINAL-RESPONSE-001 — normalized proof model for
  phil-runtime/phase0/final-response-receive-v1.

  The model preserves the exact client transport and accepted/rejected
  continuations, materializes the accepted UploadId through a caller-owned
  out-slot, loads that exact handle only in the accepted binder block, passes it
  explicitly to record_upload_id, erases the unobserved DigestFailure only for
  this exact program, preserves the already-materialized server responses, and
  invents no malformed-response CFG edge.
*)

Definition FinalOperandId := nat.
Definition FinalLLVMBlockId := nat.

Record FinalResponseReceiveLLVMModel : Type := mkFinalResponseReceiveLLVMModel {
  llvmFinalSystems : SystemsFinalResponseModel;
  llvmFinalRejectedPredecessor : RejectedResponseLLVMModel;
  llvmFinalRuntimeSymbols : RuntimeSymbolModel;

  llvmFinalTransportSSAFor : ValueId -> FinalOperandId;
  llvmFinalUploadIdSSAFor : ValueId -> FinalOperandId;
  llvmFinalBlockSSAFor : DigestBlockId -> FinalLLVMBlockId;

  llvmFinalExpectedTransport : FinalOperandId;
  llvmFinalActualTransport : FinalOperandId;
  llvmFinalExpectedUploadId : FinalOperandId;
  llvmFinalActualLoadedUploadId : FinalOperandId;
  llvmFinalRecordUploadIdOperand : FinalOperandId;

  llvmFinalExpectedAcceptedTarget : FinalLLVMBlockId;
  llvmFinalActualAcceptedTarget : FinalLLVMBlockId;
  llvmFinalExpectedRejectedTarget : FinalLLVMBlockId;
  llvmFinalActualRejectedTarget : FinalLLVMBlockId;

  llvmFinalAcceptedOutSlotPresent : bool;
  llvmFinalAcceptedOutSlotCallerOwned : bool;
  llvmFinalDecoderArity : nat;
  llvmFinalUsesPhysicalDecoder : bool;
  llvmFinalDecoderReturnsChoiceI1 : bool;

  llvmFinalAcceptedPayloadLoadedOnlyInBinder : bool;
  llvmFinalRecordUploadIdCount : nat;
  llvmFinalUploadIdOpaque : bool;
  llvmFinalUploadIdReleasedByGeneratedCode : bool;
  llvmFinalUploadIdRetainedByGeneratedCode : bool;
  llvmFinalUploadIdLayoutAccessPresent : bool;
  llvmFinalUnauthorizedPointerStrengtheningPresent : bool;
  llvmFinalUploadIdLifetimeThroughRecord : bool;

  llvmFinalDigestFailurePhysicalRepresentationPresent : bool;
  llvmFinalDigestFailureErasureJustifiedByNoUse : bool;
  llvmFinalGenericReceiveCallPresent : bool;
  llvmFinalGenericRecordCallPresent : bool;
  llvmFinalAmbientFinalResponseStatePresent : bool;
  llvmFinalAmbientUploadIdStatePresent : bool;
  llvmFinalMalformedCFGBranchPresent : bool;
  llvmFinalServerAcceptedPreserved : bool;
  llvmFinalServerRejectedPreserved : bool
}.

Record FinalResponseReceiveLLVMVerificationSuccess
  (model : FinalResponseReceiveLLVMModel) : Prop :=
  mkFinalResponseReceiveLLVMVerificationSuccess {
    llvm_final_success_systems :
      SystemsFinalResponseVerificationSuccess (llvmFinalSystems model);
    llvm_final_success_rejected_predecessor :
      RejectedResponseLLVMVerificationSuccess
        (llvmFinalRejectedPredecessor model);
    llvm_final_success_runtime_symbols :
      RuntimeSymbolVerificationSuccess (llvmFinalRuntimeSymbols model);
    llvm_final_success_rejected_systems_align :
      llvmRejectedSystems (llvmFinalRejectedPredecessor model) =
        systemsFinalRejectedPredecessor (llvmFinalSystems model);

    llvm_final_success_expected_transport :
      llvmFinalExpectedTransport model =
        llvmFinalTransportSSAFor model
          (systemsFinalWitnessTransport (llvmFinalSystems model));
    llvm_final_success_transport :
      llvmFinalActualTransport model = llvmFinalExpectedTransport model;

    llvm_final_success_expected_upload_id :
      llvmFinalExpectedUploadId model =
        llvmFinalUploadIdSSAFor model
          (systemsFinalWitnessAcceptedPayload (llvmFinalSystems model));
    llvm_final_success_loaded_upload_id :
      llvmFinalActualLoadedUploadId model = llvmFinalExpectedUploadId model;
    llvm_final_success_record_operand :
      llvmFinalRecordUploadIdOperand model =
        llvmFinalActualLoadedUploadId model;

    llvm_final_success_expected_accepted_target :
      llvmFinalExpectedAcceptedTarget model =
        llvmFinalBlockSSAFor model
          (systemsFinalWitnessAcceptedTarget (llvmFinalSystems model));
    llvm_final_success_accepted_target :
      llvmFinalActualAcceptedTarget model =
        llvmFinalExpectedAcceptedTarget model;
    llvm_final_success_expected_rejected_target :
      llvmFinalExpectedRejectedTarget model =
        llvmFinalBlockSSAFor model
          (systemsFinalWitnessRejectedTarget (llvmFinalSystems model));
    llvm_final_success_rejected_target :
      llvmFinalActualRejectedTarget model =
        llvmFinalExpectedRejectedTarget model;

    llvm_final_success_out_slot :
      llvmFinalAcceptedOutSlotPresent model = true;
    llvm_final_success_out_slot_owner :
      llvmFinalAcceptedOutSlotCallerOwned model = true;
    llvm_final_success_decoder_arity :
      llvmFinalDecoderArity model = 2;
    llvm_final_success_physical_decoder :
      llvmFinalUsesPhysicalDecoder model = true;
    llvm_final_success_choice_i1 :
      llvmFinalDecoderReturnsChoiceI1 model = true;

    llvm_final_success_load_local :
      llvmFinalAcceptedPayloadLoadedOnlyInBinder model = true;
    llvm_final_success_record_once :
      llvmFinalRecordUploadIdCount model = 1;
    llvm_final_success_upload_id_opaque :
      llvmFinalUploadIdOpaque model = true;
    llvm_final_success_no_release :
      llvmFinalUploadIdReleasedByGeneratedCode model = false;
    llvm_final_success_no_retain :
      llvmFinalUploadIdRetainedByGeneratedCode model = false;
    llvm_final_success_no_layout :
      llvmFinalUploadIdLayoutAccessPresent model = false;
    llvm_final_success_no_strengthening :
      llvmFinalUnauthorizedPointerStrengtheningPresent model = false;
    llvm_final_success_lifetime :
      llvmFinalUploadIdLifetimeThroughRecord model = true;

    llvm_final_success_no_digest_rep :
      llvmFinalDigestFailurePhysicalRepresentationPresent model = false;
    llvm_final_success_digest_erasure_witness :
      llvmFinalDigestFailureErasureJustifiedByNoUse model = true;
    llvm_final_success_no_generic_receive :
      llvmFinalGenericReceiveCallPresent model = false;
    llvm_final_success_no_generic_record :
      llvmFinalGenericRecordCallPresent model = false;
    llvm_final_success_no_ambient_response :
      llvmFinalAmbientFinalResponseStatePresent model = false;
    llvm_final_success_no_ambient_upload :
      llvmFinalAmbientUploadIdStatePresent model = false;
    llvm_final_success_no_malformed_branch :
      llvmFinalMalformedCFGBranchPresent model = false;
    llvm_final_success_server_accepted :
      llvmFinalServerAcceptedPreserved model = true;
    llvm_final_success_server_rejected :
      llvmFinalServerRejectedPreserved model = true
  }.

Theorem verified_llvm_final_response_reuses_semantic_and_predecessor_authority :
  forall model,
    FinalResponseReceiveLLVMVerificationSuccess model ->
    SystemsFinalResponseVerificationSuccess (llvmFinalSystems model) /\
    RejectedResponseLLVMVerificationSuccess
      (llvmFinalRejectedPredecessor model) /\
    RuntimeSymbolVerificationSuccess (llvmFinalRuntimeSymbols model) /\
    llvmRejectedSystems (llvmFinalRejectedPredecessor model) =
      systemsFinalRejectedPredecessor (llvmFinalSystems model).
Proof.
  intros model H; repeat split.
  - exact (llvm_final_success_systems model H).
  - exact (llvm_final_success_rejected_predecessor model H).
  - exact (llvm_final_success_runtime_symbols model H).
  - exact (llvm_final_success_rejected_systems_align model H).
Qed.

Theorem verified_llvm_final_response_preserves_decoder_boundary :
  forall model,
    FinalResponseReceiveLLVMVerificationSuccess model ->
    llvmFinalActualTransport model =
      llvmFinalTransportSSAFor model
        (systemsFinalWitnessTransport (llvmFinalSystems model)) /\
    llvmFinalActualAcceptedTarget model =
      llvmFinalBlockSSAFor model
        (systemsFinalWitnessAcceptedTarget (llvmFinalSystems model)) /\
    llvmFinalActualRejectedTarget model =
      llvmFinalBlockSSAFor model
        (systemsFinalWitnessRejectedTarget (llvmFinalSystems model)) /\
    llvmFinalAcceptedOutSlotPresent model = true /\
    llvmFinalAcceptedOutSlotCallerOwned model = true /\
    llvmFinalDecoderArity model = 2 /\
    llvmFinalUsesPhysicalDecoder model = true /\
    llvmFinalDecoderReturnsChoiceI1 model = true.
Proof.
  intros model H; repeat split.
  - rewrite (llvm_final_success_transport model H).
    exact (llvm_final_success_expected_transport model H).
  - rewrite (llvm_final_success_accepted_target model H).
    exact (llvm_final_success_expected_accepted_target model H).
  - rewrite (llvm_final_success_rejected_target model H).
    exact (llvm_final_success_expected_rejected_target model H).
  - exact (llvm_final_success_out_slot model H).
  - exact (llvm_final_success_out_slot_owner model H).
  - exact (llvm_final_success_decoder_arity model H).
  - exact (llvm_final_success_physical_decoder model H).
  - exact (llvm_final_success_choice_i1 model H).
Qed.

Theorem verified_llvm_final_response_binds_and_records_accepted_upload_id :
  forall model,
    FinalResponseReceiveLLVMVerificationSuccess model ->
    llvmFinalActualLoadedUploadId model =
      llvmFinalUploadIdSSAFor model
        (systemsFinalWitnessAcceptedPayload (llvmFinalSystems model)) /\
    llvmFinalRecordUploadIdOperand model =
      llvmFinalActualLoadedUploadId model /\
    llvmFinalAcceptedPayloadLoadedOnlyInBinder model = true /\
    llvmFinalRecordUploadIdCount model = 1 /\
    llvmFinalUploadIdLifetimeThroughRecord model = true.
Proof.
  intros model H; repeat split.
  - rewrite (llvm_final_success_loaded_upload_id model H).
    exact (llvm_final_success_expected_upload_id model H).
  - exact (llvm_final_success_record_operand model H).
  - exact (llvm_final_success_load_local model H).
  - exact (llvm_final_success_record_once model H).
  - exact (llvm_final_success_lifetime model H).
Qed.

Theorem verified_llvm_final_response_preserves_upload_id_opacity :
  forall model,
    FinalResponseReceiveLLVMVerificationSuccess model ->
    llvmFinalUploadIdOpaque model = true /\
    llvmFinalUploadIdReleasedByGeneratedCode model = false /\
    llvmFinalUploadIdRetainedByGeneratedCode model = false /\
    llvmFinalUploadIdLayoutAccessPresent model = false /\
    llvmFinalUnauthorizedPointerStrengtheningPresent model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_final_success_upload_id_opaque model H).
  - exact (llvm_final_success_no_release model H).
  - exact (llvm_final_success_no_retain model H).
  - exact (llvm_final_success_no_layout model H).
  - exact (llvm_final_success_no_strengthening model H).
Qed.

Theorem verified_llvm_final_response_erases_only_unobserved_digest_failure :
  forall model,
    FinalResponseReceiveLLVMVerificationSuccess model ->
    llvmFinalDigestFailurePhysicalRepresentationPresent model = false /\
    llvmFinalDigestFailureErasureJustifiedByNoUse model = true /\
    systemsFinalRejectedPayloadUseCount (llvmFinalSystems model) = 0.
Proof.
  intros model H; repeat split.
  - exact (llvm_final_success_no_digest_rep model H).
  - exact (llvm_final_success_digest_erasure_witness model H).
  - exact (systems_final_success_rejected_unused
      (llvmFinalSystems model) (llvm_final_success_systems model H)).
Qed.

Theorem verified_llvm_final_response_forbids_ambient_generic_and_malformed_edges :
  forall model,
    FinalResponseReceiveLLVMVerificationSuccess model ->
    llvmFinalGenericReceiveCallPresent model = false /\
    llvmFinalGenericRecordCallPresent model = false /\
    llvmFinalAmbientFinalResponseStatePresent model = false /\
    llvmFinalAmbientUploadIdStatePresent model = false /\
    llvmFinalMalformedCFGBranchPresent model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_final_success_no_generic_receive model H).
  - exact (llvm_final_success_no_generic_record model H).
  - exact (llvm_final_success_no_ambient_response model H).
  - exact (llvm_final_success_no_ambient_upload model H).
  - exact (llvm_final_success_no_malformed_branch model H).
Qed.

Theorem verified_llvm_final_response_preserves_server_response_operations :
  forall model,
    FinalResponseReceiveLLVMVerificationSuccess model ->
    llvmFinalServerAcceptedPreserved model = true /\
    llvmFinalServerRejectedPreserved model = true.
Proof.
  intros model H; split.
  - exact (llvm_final_success_server_accepted model H).
  - exact (llvm_final_success_server_rejected model H).
Qed.

Theorem llvm_final_response_decoder_or_target_drift_is_rejected :
  forall model,
    llvmFinalActualTransport model <> llvmFinalExpectedTransport model \/
    llvmFinalActualAcceptedTarget model <>
      llvmFinalExpectedAcceptedTarget model \/
    llvmFinalActualRejectedTarget model <>
      llvmFinalExpectedRejectedTarget model \/
    llvmFinalAcceptedOutSlotPresent model = false \/
    llvmFinalAcceptedOutSlotCallerOwned model = false \/
    llvmFinalDecoderArity model <> 2 \/
    llvmFinalUsesPhysicalDecoder model = false \/
    llvmFinalDecoderReturnsChoiceI1 model = false ->
    ~ FinalResponseReceiveLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Ht | [Hat | [Hrt | [Hs | [Hso | [Ha | [Hp | Hi1]]]]]]].
  - apply Ht. exact (llvm_final_success_transport model H).
  - apply Hat. exact (llvm_final_success_accepted_target model H).
  - apply Hrt. exact (llvm_final_success_rejected_target model H).
  - rewrite (llvm_final_success_out_slot model H) in Hs. discriminate.
  - rewrite (llvm_final_success_out_slot_owner model H) in Hso. discriminate.
  - apply Ha. exact (llvm_final_success_decoder_arity model H).
  - rewrite (llvm_final_success_physical_decoder model H) in Hp. discriminate.
  - rewrite (llvm_final_success_choice_i1 model H) in Hi1. discriminate.
Qed.

Theorem llvm_final_response_upload_id_dataflow_drift_is_rejected :
  forall model,
    llvmFinalActualLoadedUploadId model <> llvmFinalExpectedUploadId model \/
    llvmFinalRecordUploadIdOperand model <>
      llvmFinalActualLoadedUploadId model \/
    llvmFinalAcceptedPayloadLoadedOnlyInBinder model = false \/
    llvmFinalRecordUploadIdCount model <> 1 \/
    llvmFinalUploadIdLifetimeThroughRecord model = false ->
    ~ FinalResponseReceiveLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hl | [Hr | [Hlocal | [Hc | Hlife]]]].
  - apply Hl. exact (llvm_final_success_loaded_upload_id model H).
  - apply Hr. exact (llvm_final_success_record_operand model H).
  - rewrite (llvm_final_success_load_local model H) in Hlocal. discriminate.
  - apply Hc. exact (llvm_final_success_record_once model H).
  - rewrite (llvm_final_success_lifetime model H) in Hlife. discriminate.
Qed.

Theorem llvm_final_response_erasure_ambient_or_malformed_drift_is_rejected :
  forall model,
    llvmFinalDigestFailurePhysicalRepresentationPresent model = true \/
    llvmFinalDigestFailureErasureJustifiedByNoUse model = false \/
    llvmFinalGenericReceiveCallPresent model = true \/
    llvmFinalGenericRecordCallPresent model = true \/
    llvmFinalAmbientFinalResponseStatePresent model = true \/
    llvmFinalAmbientUploadIdStatePresent model = true \/
    llvmFinalMalformedCFGBranchPresent model = true \/
    llvmFinalUploadIdReleasedByGeneratedCode model = true \/
    llvmFinalUploadIdRetainedByGeneratedCode model = true \/
    llvmFinalUploadIdLayoutAccessPresent model = true \/
    llvmFinalUnauthorizedPointerStrengtheningPresent model = true ->
    ~ FinalResponseReceiveLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as
    [Hd | [Hw | [Hgr | [Hgc | [Har | [Hau | [Hm | [Hrel | [Hret | [Hlay | Hstr]]]]]]]]]].
  - rewrite (llvm_final_success_no_digest_rep model H) in Hd. discriminate.
  - rewrite (llvm_final_success_digest_erasure_witness model H) in Hw. discriminate.
  - rewrite (llvm_final_success_no_generic_receive model H) in Hgr. discriminate.
  - rewrite (llvm_final_success_no_generic_record model H) in Hgc. discriminate.
  - rewrite (llvm_final_success_no_ambient_response model H) in Har. discriminate.
  - rewrite (llvm_final_success_no_ambient_upload model H) in Hau. discriminate.
  - rewrite (llvm_final_success_no_malformed_branch model H) in Hm. discriminate.
  - rewrite (llvm_final_success_no_release model H) in Hrel. discriminate.
  - rewrite (llvm_final_success_no_retain model H) in Hret. discriminate.
  - rewrite (llvm_final_success_no_layout model H) in Hlay. discriminate.
  - rewrite (llvm_final_success_no_strengthening model H) in Hstr. discriminate.
Qed.
