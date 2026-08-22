From Phil.Systems Require Import FinalResponse.
From Phil.LLVM Require Import RejectedResponse RuntimeSymbolIdentity.

(*
  PHIL-LLVM-FINAL-RESPONSE-001 — normalized proof model for
  phil-runtime/phase0/final-response-receive-v1.

  The model preserves the exact client transport and accepted/rejected
  continuations, materializes the accepted UploadId through a caller-owned
  out-slot, loads that handle only in the accepted binder block, passes it
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

  llvmFinalExpectedTransport : FinalOperandId;
  llvmFinalActualTransport : FinalOperandId;
  llvmFinalAcceptedOutSlotPresent : bool;
  llvmFinalAcceptedOutSlotCallerOwned : bool;
  llvmFinalDecoderArity : nat;
  llvmFinalUsesPhysicalDecoder : bool;
  llvmFinalDecoderReturnsChoiceI1 : bool;
  llvmFinalAcceptedTargetExact : bool;
  llvmFinalRejectedTargetExact : bool;

  llvmFinalAcceptedPayloadLoadedOnlyInBinder : bool;
  llvmFinalAcceptedLoadedHandleExact : bool;
  llvmFinalRecordUploadIdUsesExactHandle : bool;
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
      RejectedResponseLLVMVerificationSuccess (llvmFinalRejectedPredecessor model);
    llvm_final_success_runtime_symbols :
      RuntimeSymbolVerificationSuccess (llvmFinalRuntimeSymbols model);
    llvm_final_success_transport : llvmFinalActualTransport model = llvmFinalExpectedTransport model;
    llvm_final_success_out_slot : llvmFinalAcceptedOutSlotPresent model = true;
    llvm_final_success_out_slot_owner : llvmFinalAcceptedOutSlotCallerOwned model = true;
    llvm_final_success_decoder_arity : llvmFinalDecoderArity model = 2;
    llvm_final_success_physical_decoder : llvmFinalUsesPhysicalDecoder model = true;
    llvm_final_success_choice_i1 : llvmFinalDecoderReturnsChoiceI1 model = true;
    llvm_final_success_accepted_target : llvmFinalAcceptedTargetExact model = true;
    llvm_final_success_rejected_target : llvmFinalRejectedTargetExact model = true;
    llvm_final_success_load_local : llvmFinalAcceptedPayloadLoadedOnlyInBinder model = true;
    llvm_final_success_loaded_handle : llvmFinalAcceptedLoadedHandleExact model = true;
    llvm_final_success_record_exact : llvmFinalRecordUploadIdUsesExactHandle model = true;
    llvm_final_success_record_once : llvmFinalRecordUploadIdCount model = 1;
    llvm_final_success_upload_id_opaque : llvmFinalUploadIdOpaque model = true;
    llvm_final_success_no_release : llvmFinalUploadIdReleasedByGeneratedCode model = false;
    llvm_final_success_no_retain : llvmFinalUploadIdRetainedByGeneratedCode model = false;
    llvm_final_success_no_layout : llvmFinalUploadIdLayoutAccessPresent model = false;
    llvm_final_success_no_strengthening : llvmFinalUnauthorizedPointerStrengtheningPresent model = false;
    llvm_final_success_lifetime : llvmFinalUploadIdLifetimeThroughRecord model = true;
    llvm_final_success_no_digest_rep : llvmFinalDigestFailurePhysicalRepresentationPresent model = false;
    llvm_final_success_digest_erasure_witness : llvmFinalDigestFailureErasureJustifiedByNoUse model = true;
    llvm_final_success_no_generic_receive : llvmFinalGenericReceiveCallPresent model = false;
    llvm_final_success_no_generic_record : llvmFinalGenericRecordCallPresent model = false;
    llvm_final_success_no_ambient_response : llvmFinalAmbientFinalResponseStatePresent model = false;
    llvm_final_success_no_ambient_upload : llvmFinalAmbientUploadIdStatePresent model = false;
    llvm_final_success_no_malformed_branch : llvmFinalMalformedCFGBranchPresent model = false;
    llvm_final_success_server_accepted : llvmFinalServerAcceptedPreserved model = true;
    llvm_final_success_server_rejected : llvmFinalServerRejectedPreserved model = true
  }.

Theorem verified_llvm_final_response_reuses_semantic_and_predecessor_authority :
  forall model, FinalResponseReceiveLLVMVerificationSuccess model ->
  SystemsFinalResponseVerificationSuccess (llvmFinalSystems model) /\
  RejectedResponseLLVMVerificationSuccess (llvmFinalRejectedPredecessor model) /\
  RuntimeSymbolVerificationSuccess (llvmFinalRuntimeSymbols model).
Proof.
  intros model H; repeat split.
  - exact (llvm_final_success_systems model H).
  - exact (llvm_final_success_rejected_predecessor model H).
  - exact (llvm_final_success_runtime_symbols model H).
Qed.

Theorem verified_llvm_final_response_preserves_decoder_boundary :
  forall model, FinalResponseReceiveLLVMVerificationSuccess model ->
  llvmFinalActualTransport model = llvmFinalExpectedTransport model /\
  llvmFinalAcceptedOutSlotPresent model = true /\
  llvmFinalAcceptedOutSlotCallerOwned model = true /\
  llvmFinalDecoderArity model = 2 /\
  llvmFinalUsesPhysicalDecoder model = true /\
  llvmFinalDecoderReturnsChoiceI1 model = true /\
  llvmFinalAcceptedTargetExact model = true /\
  llvmFinalRejectedTargetExact model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_final_success_transport model H).
  - exact (llvm_final_success_out_slot model H).
  - exact (llvm_final_success_out_slot_owner model H).
  - exact (llvm_final_success_decoder_arity model H).
  - exact (llvm_final_success_physical_decoder model H).
  - exact (llvm_final_success_choice_i1 model H).
  - exact (llvm_final_success_accepted_target model H).
  - exact (llvm_final_success_rejected_target model H).
Qed.

Theorem verified_llvm_final_response_binds_and_records_accepted_upload_id :
  forall model, FinalResponseReceiveLLVMVerificationSuccess model ->
  llvmFinalAcceptedPayloadLoadedOnlyInBinder model = true /\
  llvmFinalAcceptedLoadedHandleExact model = true /\
  llvmFinalRecordUploadIdUsesExactHandle model = true /\
  llvmFinalRecordUploadIdCount model = 1 /\
  llvmFinalUploadIdLifetimeThroughRecord model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_final_success_load_local model H).
  - exact (llvm_final_success_loaded_handle model H).
  - exact (llvm_final_success_record_exact model H).
  - exact (llvm_final_success_record_once model H).
  - exact (llvm_final_success_lifetime model H).
Qed.

Theorem verified_llvm_final_response_preserves_upload_id_opacity :
  forall model, FinalResponseReceiveLLVMVerificationSuccess model ->
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
  forall model, FinalResponseReceiveLLVMVerificationSuccess model ->
  llvmFinalDigestFailurePhysicalRepresentationPresent model = false /\
  llvmFinalDigestFailureErasureJustifiedByNoUse model = true.
Proof.
  intros model H; split.
  - exact (llvm_final_success_no_digest_rep model H).
  - exact (llvm_final_success_digest_erasure_witness model H).
Qed.

Theorem verified_llvm_final_response_forbids_ambient_generic_and_malformed_edges :
  forall model, FinalResponseReceiveLLVMVerificationSuccess model ->
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
  forall model, FinalResponseReceiveLLVMVerificationSuccess model ->
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
  llvmFinalAcceptedOutSlotPresent model = false \/
  llvmFinalDecoderArity model <> 2 \/
  llvmFinalUsesPhysicalDecoder model = false \/
  llvmFinalAcceptedTargetExact model = false \/
  llvmFinalRejectedTargetExact model = false ->
  ~ FinalResponseReceiveLLVMVerificationSuccess model.
Proof.
  intros model Hbad H; destruct Hbad as [Ht | [Hs | [Ha | [Hp | [Hat | Hrt]]]]].
  - apply Ht; exact (llvm_final_success_transport model H).
  - rewrite (llvm_final_success_out_slot model H) in Hs; discriminate.
  - apply Ha; exact (llvm_final_success_decoder_arity model H).
  - rewrite (llvm_final_success_physical_decoder model H) in Hp; discriminate.
  - rewrite (llvm_final_success_accepted_target model H) in Hat; discriminate.
  - rewrite (llvm_final_success_rejected_target model H) in Hrt; discriminate.
Qed.

Theorem llvm_final_response_upload_id_dataflow_drift_is_rejected :
  forall model,
  llvmFinalAcceptedPayloadLoadedOnlyInBinder model = false \/
  llvmFinalAcceptedLoadedHandleExact model = false \/
  llvmFinalRecordUploadIdUsesExactHandle model = false \/
  llvmFinalRecordUploadIdCount model <> 1 \/
  llvmFinalUploadIdLifetimeThroughRecord model = false ->
  ~ FinalResponseReceiveLLVMVerificationSuccess model.
Proof.
  intros model Hbad H; destruct Hbad as [Hl | [Hh | [Hr | [Hc | Hlife]]]].
  - rewrite (llvm_final_success_load_local model H) in Hl; discriminate.
  - rewrite (llvm_final_success_loaded_handle model H) in Hh; discriminate.
  - rewrite (llvm_final_success_record_exact model H) in Hr; discriminate.
  - apply Hc; exact (llvm_final_success_record_once model H).
  - rewrite (llvm_final_success_lifetime model H) in Hlife; discriminate.
Qed.

Theorem llvm_final_response_erasure_ambient_or_malformed_drift_is_rejected :
  forall model,
  llvmFinalDigestFailurePhysicalRepresentationPresent model = true \/
  llvmFinalDigestFailureErasureJustifiedByNoUse model = false \/
  llvmFinalGenericReceiveCallPresent model = true \/
  llvmFinalGenericRecordCallPresent model = true \/
  llvmFinalAmbientFinalResponseStatePresent model = true \/
  llvmFinalAmbientUploadIdStatePresent model = true \/
  llvmFinalMalformedCFGBranchPresent model = true ->
  ~ FinalResponseReceiveLLVMVerificationSuccess model.
Proof.
  intros model Hbad H;
  destruct Hbad as [Hd | [Hw | [Hgr | [Hgc | [Har | [Hau | Hm]]]]]].
  - rewrite (llvm_final_success_no_digest_rep model H) in Hd; discriminate.
  - rewrite (llvm_final_success_digest_erasure_witness model H) in Hw; discriminate.
  - rewrite (llvm_final_success_no_generic_receive model H) in Hgr; discriminate.
  - rewrite (llvm_final_success_no_generic_record model H) in Hgc; discriminate.
  - rewrite (llvm_final_success_no_ambient_response model H) in Har; discriminate.
  - rewrite (llvm_final_success_no_ambient_upload model H) in Hau; discriminate.
  - rewrite (llvm_final_success_no_malformed_branch model H) in Hm; discriminate.
Qed.
