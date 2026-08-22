From Phil.LLVM Require Import Preservation Strengthening.

(*
  PHIL-LLVM-REC-ABI-001 — normalized proof model for the concrete
  recognized-record ABI v1 lowering.

  The target-level claim is deliberately narrower than proving LLVM itself or
  a concrete runtime implementation.  A successful verification binds one
  source recognition site to one target recognition call, uses the exact
  fail-closed status == 1 test, obtains the record handle from that same result,
  preserves the exact grammar/field/scalar-width accessor, passes the exact
  projected scalar to receive_exact_u64, and admits neither concrete record
  layout access nor unauthorized pointer strengthening.
*)

Definition ABIGrammarId := nat.
Definition ABIFieldId := nat.
Definition ABIScalarWidth := nat.
Definition ABIRecordSSAId := nat.
Definition ABIScalarSSAId := nat.

Record RecognizedRecordABIModel : Type := mkRecognizedRecordABIModel {
  abiPreservation : LLVMPreservationModel;
  abiStrengthening : StrengtheningEnvironment;
  abiRecognitionSite : RuntimeSiteId;
  abiRecognitionResultCount : nat;
  abiRecognitionStatusConstant : nat;
  abiRecordExtractedFromRecognitionResult : bool;
  abiExpectedRecordSSA : ABIRecordSSAId;
  abiActualRecordSSA : ABIRecordSSAId;
  abiExpectedGrammar : ABIGrammarId;
  abiActualGrammar : ABIGrammarId;
  abiExpectedField : ABIFieldId;
  abiActualField : ABIFieldId;
  abiExpectedWidth : ABIScalarWidth;
  abiActualWidth : ABIScalarWidth;
  abiProjectedScalar : ABIScalarSSAId;
  abiExactReceiveScalar : ABIScalarSSAId;
  abiConcreteRecordLayoutAccessPresent : bool;
  abiUnauthorizedPointerStrengtheningPresent : bool
}.

Record RecognizedRecordABIVerificationSuccess
  (model : RecognizedRecordABIModel) : Prop := mkRecognizedRecordABIVerificationSuccess {
  abi_success_preservation :
    LLVMPreservationVerificationSuccess (abiPreservation model);
  abi_success_strengthening :
    StrengtheningVerificationSuccess (abiStrengthening model);
  abi_success_source_recognition_count :
    preservationSourceRuntimeCount
      (abiPreservation model)
      (abiRecognitionSite model) = 1;
  abi_success_one_recognition_result :
    abiRecognitionResultCount model = 1;
  abi_success_fail_closed_status :
    abiRecognitionStatusConstant model = 1;
  abi_success_same_result_handle :
    abiRecordExtractedFromRecognitionResult model = true;
  abi_success_record_identity :
    abiActualRecordSSA model = abiExpectedRecordSSA model;
  abi_success_grammar_identity :
    abiActualGrammar model = abiExpectedGrammar model;
  abi_success_field_identity :
    abiActualField model = abiExpectedField model;
  abi_success_expected_u64 :
    abiExpectedWidth model = 64;
  abi_success_width_identity :
    abiActualWidth model = abiExpectedWidth model;
  abi_success_exact_receive_scalar :
    abiExactReceiveScalar model = abiProjectedScalar model;
  abi_success_no_layout_access :
    abiConcreteRecordLayoutAccessPresent model = false;
  abi_success_no_unauthorized_pointer_strengthening :
    abiUnauthorizedPointerStrengtheningPresent model = false
}.

Theorem verified_recognized_record_abi_rechecks_systems_source :
  forall model,
    RecognizedRecordABIVerificationSuccess model ->
    preservationSystemsSourceReverified (abiPreservation model) = true.
Proof.
  intros model H.
  exact
    (verified_llvm_rechecks_source_systems_artifact
      (abiPreservation model)
      (abi_success_preservation model H)).
Qed.

Theorem verified_recognized_record_abi_preserves_single_recognition_call :
  forall model,
    RecognizedRecordABIVerificationSuccess model ->
    preservationTargetRuntimeCount
      (abiPreservation model)
      (abiRecognitionSite model) = 1.
Proof.
  intros model H.
  pose proof
    (verified_llvm_preserves_runtime_site_multiplicity
      (abiPreservation model)
      (abiRecognitionSite model)
      (abi_success_preservation model H)) as Hcount.
  rewrite <- Hcount.
  exact (abi_success_source_recognition_count model H).
Qed.

Theorem verified_recognized_record_abi_uses_exact_fail_closed_status :
  forall model,
    RecognizedRecordABIVerificationSuccess model ->
    abiRecognitionResultCount model = 1 /\
    abiRecognitionStatusConstant model = 1.
Proof.
  intros model H.
  split.
  - exact (abi_success_one_recognition_result model H).
  - exact (abi_success_fail_closed_status model H).
Qed.

Theorem verified_recognized_record_abi_binds_handle_from_same_result :
  forall model,
    RecognizedRecordABIVerificationSuccess model ->
    abiRecordExtractedFromRecognitionResult model = true /\
    abiActualRecordSSA model = abiExpectedRecordSSA model.
Proof.
  intros model H.
  split.
  - exact (abi_success_same_result_handle model H).
  - exact (abi_success_record_identity model H).
Qed.

Theorem verified_recognized_record_abi_preserves_typed_accessor :
  forall model,
    RecognizedRecordABIVerificationSuccess model ->
    abiActualGrammar model = abiExpectedGrammar model /\
    abiActualField model = abiExpectedField model /\
    abiExpectedWidth model = 64 /\
    abiActualWidth model = 64.
Proof.
  intros model H.
  repeat split.
  - exact (abi_success_grammar_identity model H).
  - exact (abi_success_field_identity model H).
  - exact (abi_success_expected_u64 model H).
  - rewrite (abi_success_width_identity model H).
    exact (abi_success_expected_u64 model H).
Qed.

Theorem verified_recognized_record_abi_feeds_exact_receive :
  forall model,
    RecognizedRecordABIVerificationSuccess model ->
    abiExactReceiveScalar model = abiProjectedScalar model.
Proof.
  intros model H.
  exact (abi_success_exact_receive_scalar model H).
Qed.

Theorem verified_recognized_record_abi_forbids_layout_access_and_unauthorized_strengthening :
  forall model,
    RecognizedRecordABIVerificationSuccess model ->
    abiConcreteRecordLayoutAccessPresent model = false /\
    abiUnauthorizedPointerStrengtheningPresent model = false.
Proof.
  intros model H.
  split.
  - exact (abi_success_no_layout_access model H).
  - exact (abi_success_no_unauthorized_pointer_strengthening model H).
Qed.

Theorem recognized_record_abi_status_drift_is_rejected :
  forall model,
    abiRecognitionStatusConstant model <> 1 ->
    ~ RecognizedRecordABIVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (abi_success_fail_closed_status model H).
Qed.

Theorem recognized_record_abi_record_drift_is_rejected :
  forall model,
    abiActualRecordSSA model <> abiExpectedRecordSSA model ->
    ~ RecognizedRecordABIVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (abi_success_record_identity model H).
Qed.

Theorem recognized_record_abi_width_drift_is_rejected :
  forall model,
    abiActualWidth model <> 64 ->
    ~ RecognizedRecordABIVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  rewrite (abi_success_width_identity model H).
  exact (abi_success_expected_u64 model H).
Qed.

Theorem recognized_record_abi_consumer_drift_is_rejected :
  forall model,
    abiExactReceiveScalar model <> abiProjectedScalar model ->
    ~ RecognizedRecordABIVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (abi_success_exact_receive_scalar model H).
Qed.

Theorem recognized_record_abi_layout_access_is_rejected :
  forall model,
    abiConcreteRecordLayoutAccessPresent model = true ->
    ~ RecognizedRecordABIVerificationSuccess model.
Proof.
  intros model Hlayout H.
  rewrite (abi_success_no_layout_access model H) in Hlayout.
  discriminate.
Qed.

Theorem recognized_record_abi_unauthorized_pointer_strengthening_is_rejected :
  forall model,
    abiUnauthorizedPointerStrengtheningPresent model = true ->
    ~ RecognizedRecordABIVerificationSuccess model.
Proof.
  intros model Hstrengthening H.
  rewrite (abi_success_no_unauthorized_pointer_strengthening model H) in Hstrengthening.
  discriminate.
Qed.
