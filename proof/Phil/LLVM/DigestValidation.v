From Phil.Systems Require Import ScalarDataflow DigestValidation.
From Phil.LLVM Require Import ExactReceive RuntimeSymbolIdentity.

(*
  PHIL-LLVM-DIGEST-001 — normalized proof model for the concrete
  digest-validation-v1 lowering introduced by PR #50.

  This theorem family composes the Systems DigestMatches subject/borrow proof,
  the certified exact-receive authority, and the runtime-symbol discipline.
  It proves that the target digest primitive receives the exact recognized
  Begin handle and the exact payload-owner handle underlying the verified
  source borrow, in source order, with exact source-derived success/failure
  edges.  The no-copy borrow representation is explicit and SHA-256 is bound as
  the selected runtime mechanism in ABI identity.

  It does not prove SHA-256 cryptographic correctness, libcrypto, LLVM, or the C
  runtime provider.  Those remain explicit external gates.
*)

Definition DigestOperandId := nat.
Definition DigestLLVMBlockId := nat.
Definition DigestMechanismId := nat.
Definition sha256Mechanism : DigestMechanismId := 256.

Record DigestValidationLLVMModel : Type := mkDigestValidationLLVMModel {
  llvmDigestSystems : SystemsDigestValidationModel;
  llvmDigestExactReceive : ExactReceiveModel;
  llvmDigestRuntimeSymbols : RuntimeSymbolModel;

  llvmDigestRecordSSAFor : ValueId -> DigestOperandId;
  llvmDigestPayloadSSAFor : ValueId -> DigestOperandId;
  llvmDigestBlockSSAFor : DigestBlockId -> DigestLLVMBlockId;

  llvmDigestExpectedRecordOperand : DigestOperandId;
  llvmDigestActualRecordOperand : DigestOperandId;
  llvmDigestExpectedPayloadOperand : DigestOperandId;
  llvmDigestActualPayloadOperand : DigestOperandId;
  llvmDigestBorrowErasedToOwner : bool;

  llvmDigestOperandCount : nat;
  llvmDigestFirstOperand : DigestOperandId;
  llvmDigestSecondOperand : DigestOperandId;

  llvmDigestActualMechanism : DigestMechanismId;
  llvmDigestABIIdentityBindsMechanism : bool;

  llvmDigestActualSuccessBlock : DigestLLVMBlockId;
  llvmDigestActualFailureBlock : DigestLLVMBlockId;

  llvmDigestAmbientRecordPresent : bool;
  llvmDigestAmbientPayloadPresent : bool;
  llvmDigestAmbientDigestPresent : bool;
  llvmDigestNullarySignaturePresent : bool;
  llvmDigestRecordLayoutAccessPresent : bool;
  llvmDigestPayloadLayoutAccessPresent : bool;
  llvmDigestUnauthorizedPointerStrengtheningPresent : bool
}.

Record DigestValidationLLVMVerificationSuccess
  (model : DigestValidationLLVMModel) : Prop :=
  mkDigestValidationLLVMVerificationSuccess {
    llvm_digest_success_systems :
      SystemsDigestValidationVerificationSuccess (llvmDigestSystems model);
    llvm_digest_success_exact_receive :
      ExactReceiveVerificationSuccess (llvmDigestExactReceive model);
    llvm_digest_success_runtime_symbols :
      RuntimeSymbolVerificationSuccess (llvmDigestRuntimeSymbols model);

    llvm_digest_success_expected_record :
      llvmDigestExpectedRecordOperand model =
        llvmDigestRecordSSAFor model
          (systemsDigestActualRecordSubject (llvmDigestSystems model));
    llvm_digest_success_recognized_record_correspondence :
      abiActualRecordSSA
        (exactRecognizedRecordABI (llvmDigestExactReceive model)) =
        llvmDigestExpectedRecordOperand model;
    llvm_digest_success_record_operand :
      llvmDigestActualRecordOperand model =
        llvmDigestExpectedRecordOperand model;

    llvm_digest_success_expected_payload :
      llvmDigestExpectedPayloadOperand model =
        llvmDigestPayloadSSAFor model
          (systemsDigestPayloadOwner (llvmDigestSystems model));
    llvm_digest_success_exact_receive_payload_correspondence :
      exactActualPayload (llvmDigestExactReceive model) =
        llvmDigestExpectedPayloadOperand model;
    llvm_digest_success_payload_operand :
      llvmDigestActualPayloadOperand model =
        llvmDigestExpectedPayloadOperand model;
    llvm_digest_success_borrow_erasure :
      llvmDigestBorrowErasedToOwner model = true;

    llvm_digest_success_operand_count :
      llvmDigestOperandCount model = 2;
    llvm_digest_success_first_operand :
      llvmDigestFirstOperand model = llvmDigestActualRecordOperand model;
    llvm_digest_success_second_operand :
      llvmDigestSecondOperand model = llvmDigestActualPayloadOperand model;

    llvm_digest_success_sha256 :
      llvmDigestActualMechanism model = sha256Mechanism;
    llvm_digest_success_abi_binds_mechanism :
      llvmDigestABIIdentityBindsMechanism model = true;

    llvm_digest_success_success_edge :
      llvmDigestActualSuccessBlock model =
        llvmDigestBlockSSAFor model
          (systemsDigestSuccessBlock (llvmDigestSystems model));
    llvm_digest_success_failure_edge :
      llvmDigestActualFailureBlock model =
        llvmDigestBlockSSAFor model
          (systemsDigestFailureBlock (llvmDigestSystems model));

    llvm_digest_success_no_ambient_record :
      llvmDigestAmbientRecordPresent model = false;
    llvm_digest_success_no_ambient_payload :
      llvmDigestAmbientPayloadPresent model = false;
    llvm_digest_success_no_ambient_digest :
      llvmDigestAmbientDigestPresent model = false;
    llvm_digest_success_no_nullary_signature :
      llvmDigestNullarySignaturePresent model = false;
    llvm_digest_success_no_record_layout_access :
      llvmDigestRecordLayoutAccessPresent model = false;
    llvm_digest_success_no_payload_layout_access :
      llvmDigestPayloadLayoutAccessPresent model = false;
    llvm_digest_success_no_unauthorized_strengthening :
      llvmDigestUnauthorizedPointerStrengtheningPresent model = false
  }.

Theorem verified_llvm_digest_reuses_systems_subject_and_borrow_authority :
  forall model,
    DigestValidationLLVMVerificationSuccess model ->
    SystemsDigestValidationVerificationSuccess (llvmDigestSystems model).
Proof.
  intros model H.
  exact (llvm_digest_success_systems model H).
Qed.

Theorem verified_llvm_digest_reuses_exact_receive_authority :
  forall model,
    DigestValidationLLVMVerificationSuccess model ->
    ExactReceiveVerificationSuccess (llvmDigestExactReceive model).
Proof.
  intros model H.
  exact (llvm_digest_success_exact_receive model H).
Qed.

Theorem verified_llvm_digest_reuses_runtime_symbol_authority :
  forall model,
    DigestValidationLLVMVerificationSuccess model ->
    RuntimeSymbolVerificationSuccess (llvmDigestRuntimeSymbols model).
Proof.
  intros model H.
  exact (llvm_digest_success_runtime_symbols model H).
Qed.

Theorem verified_llvm_digest_preserves_exact_recognized_record_operand :
  forall model,
    DigestValidationLLVMVerificationSuccess model ->
    llvmDigestActualRecordOperand model =
      llvmDigestRecordSSAFor model
        (systemsDigestActualRecordSubject (llvmDigestSystems model)) /\
    abiActualRecordSSA
      (exactRecognizedRecordABI (llvmDigestExactReceive model)) =
      llvmDigestActualRecordOperand model.
Proof.
  intros model H.
  split.
  - rewrite (llvm_digest_success_record_operand model H).
    exact (llvm_digest_success_expected_record model H).
  - rewrite (llvm_digest_success_record_operand model H).
    exact (llvm_digest_success_recognized_record_correspondence model H).
Qed.

Theorem verified_llvm_digest_preserves_exact_payload_owner_and_erases_only_view_representation :
  forall model,
    DigestValidationLLVMVerificationSuccess model ->
    llvmDigestActualPayloadOperand model =
      llvmDigestPayloadSSAFor model
        (systemsDigestPayloadOwner (llvmDigestSystems model)) /\
    exactActualPayload (llvmDigestExactReceive model) =
      llvmDigestActualPayloadOperand model /\
    llvmDigestBorrowErasedToOwner model = true.
Proof.
  intros model H.
  repeat split.
  - rewrite (llvm_digest_success_payload_operand model H).
    exact (llvm_digest_success_expected_payload model H).
  - rewrite (llvm_digest_success_payload_operand model H).
    exact (llvm_digest_success_exact_receive_payload_correspondence model H).
  - exact (llvm_digest_success_borrow_erasure model H).
Qed.

Theorem verified_llvm_digest_preserves_exact_ordered_operand_pair :
  forall model,
    DigestValidationLLVMVerificationSuccess model ->
    llvmDigestOperandCount model = 2 /\
    llvmDigestFirstOperand model = llvmDigestActualRecordOperand model /\
    llvmDigestSecondOperand model = llvmDigestActualPayloadOperand model.
Proof.
  intros model H.
  repeat split.
  - exact (llvm_digest_success_operand_count model H).
  - exact (llvm_digest_success_first_operand model H).
  - exact (llvm_digest_success_second_operand model H).
Qed.

Theorem verified_llvm_digest_preserves_source_success_and_failure_edges :
  forall model,
    DigestValidationLLVMVerificationSuccess model ->
    llvmDigestActualSuccessBlock model =
      llvmDigestBlockSSAFor model
        (systemsDigestSuccessBlock (llvmDigestSystems model)) /\
    llvmDigestActualFailureBlock model =
      llvmDigestBlockSSAFor model
        (systemsDigestFailureBlock (llvmDigestSystems model)).
Proof.
  intros model H.
  split.
  - exact (llvm_digest_success_success_edge model H).
  - exact (llvm_digest_success_failure_edge model H).
Qed.

Theorem verified_llvm_digest_binds_sha256_as_abi_mechanism :
  forall model,
    DigestValidationLLVMVerificationSuccess model ->
    llvmDigestActualMechanism model = sha256Mechanism /\
    llvmDigestABIIdentityBindsMechanism model = true.
Proof.
  intros model H.
  split.
  - exact (llvm_digest_success_sha256 model H).
  - exact (llvm_digest_success_abi_binds_mechanism model H).
Qed.

Theorem verified_llvm_digest_forbids_ambient_state_layout_access_and_unauthorized_strengthening :
  forall model,
    DigestValidationLLVMVerificationSuccess model ->
    llvmDigestAmbientRecordPresent model = false /\
    llvmDigestAmbientPayloadPresent model = false /\
    llvmDigestAmbientDigestPresent model = false /\
    llvmDigestNullarySignaturePresent model = false /\
    llvmDigestRecordLayoutAccessPresent model = false /\
    llvmDigestPayloadLayoutAccessPresent model = false /\
    llvmDigestUnauthorizedPointerStrengtheningPresent model = false.
Proof.
  intros model H.
  repeat split.
  - exact (llvm_digest_success_no_ambient_record model H).
  - exact (llvm_digest_success_no_ambient_payload model H).
  - exact (llvm_digest_success_no_ambient_digest model H).
  - exact (llvm_digest_success_no_nullary_signature model H).
  - exact (llvm_digest_success_no_record_layout_access model H).
  - exact (llvm_digest_success_no_payload_layout_access model H).
  - exact (llvm_digest_success_no_unauthorized_strengthening model H).
Qed.

Theorem llvm_digest_record_operand_drift_is_rejected :
  forall model,
    llvmDigestActualRecordOperand model <>
      llvmDigestExpectedRecordOperand model ->
    ~ DigestValidationLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (llvm_digest_success_record_operand model H).
Qed.

Theorem llvm_digest_payload_operand_drift_is_rejected :
  forall model,
    llvmDigestActualPayloadOperand model <>
      llvmDigestExpectedPayloadOperand model ->
    ~ DigestValidationLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (llvm_digest_success_payload_operand model H).
Qed.

Theorem llvm_digest_operand_order_or_arity_drift_is_rejected :
  forall model,
    llvmDigestOperandCount model <> 2 \/
    llvmDigestFirstOperand model <> llvmDigestActualRecordOperand model \/
    llvmDigestSecondOperand model <> llvmDigestActualPayloadOperand model ->
    ~ DigestValidationLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Harity | [Hfirst | Hsecond]].
  - apply Harity. exact (llvm_digest_success_operand_count model H).
  - apply Hfirst. exact (llvm_digest_success_first_operand model H).
  - apply Hsecond. exact (llvm_digest_success_second_operand model H).
Qed.

Theorem llvm_digest_borrow_representation_drift_is_rejected :
  forall model,
    llvmDigestBorrowErasedToOwner model = false ->
    ~ DigestValidationLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  rewrite (llvm_digest_success_borrow_erasure model H) in Hdrift.
  discriminate.
Qed.

Theorem llvm_digest_mechanism_or_abi_binding_drift_is_rejected :
  forall model,
    llvmDigestActualMechanism model <> sha256Mechanism \/
    llvmDigestABIIdentityBindsMechanism model = false ->
    ~ DigestValidationLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Hmechanism | Hbinding].
  - apply Hmechanism. exact (llvm_digest_success_sha256 model H).
  - rewrite (llvm_digest_success_abi_binds_mechanism model H) in Hbinding.
    discriminate.
Qed.

Theorem llvm_digest_edge_drift_is_rejected :
  forall model,
    llvmDigestActualSuccessBlock model <>
      llvmDigestBlockSSAFor model
        (systemsDigestSuccessBlock (llvmDigestSystems model)) \/
    llvmDigestActualFailureBlock model <>
      llvmDigestBlockSSAFor model
        (systemsDigestFailureBlock (llvmDigestSystems model)) ->
    ~ DigestValidationLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Hsuccess | Hfailure].
  - apply Hsuccess. exact (llvm_digest_success_success_edge model H).
  - apply Hfailure. exact (llvm_digest_success_failure_edge model H).
Qed.

Theorem llvm_digest_ambient_or_nullary_state_is_rejected :
  forall model,
    llvmDigestAmbientRecordPresent model = true \/
    llvmDigestAmbientPayloadPresent model = true \/
    llvmDigestAmbientDigestPresent model = true \/
    llvmDigestNullarySignaturePresent model = true ->
    ~ DigestValidationLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hrecord | [Hpayload | [Hdigest | Hnullary]]].
  - rewrite (llvm_digest_success_no_ambient_record model H) in Hrecord.
    discriminate.
  - rewrite (llvm_digest_success_no_ambient_payload model H) in Hpayload.
    discriminate.
  - rewrite (llvm_digest_success_no_ambient_digest model H) in Hdigest.
    discriminate.
  - rewrite (llvm_digest_success_no_nullary_signature model H) in Hnullary.
    discriminate.
Qed.

Theorem llvm_digest_layout_access_or_strengthening_is_rejected :
  forall model,
    llvmDigestRecordLayoutAccessPresent model = true \/
    llvmDigestPayloadLayoutAccessPresent model = true \/
    llvmDigestUnauthorizedPointerStrengtheningPresent model = true ->
    ~ DigestValidationLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hrecord | [Hpayload | Hstrengthening]].
  - rewrite (llvm_digest_success_no_record_layout_access model H) in Hrecord.
    discriminate.
  - rewrite (llvm_digest_success_no_payload_layout_access model H) in Hpayload.
    discriminate.
  - rewrite (llvm_digest_success_no_unauthorized_strengthening model H) in Hstrengthening.
    discriminate.
Qed.
