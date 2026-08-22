From Phil.Systems Require Import ScalarDataflow DigestValidation Storage AcceptedResponse RejectedResponse.
From Phil.LLVM Require Import DigestValidation Storage AcceptedResponse RuntimeSymbolIdentity.

(*
  PHIL-LLVM-REJECTED-001 — normalized proof model for rejected-response-v1.

  The digest mismatch edge reaches the exact rejected block.  The exact payload
  owner that fed DigestMatches is released before the physical rejected
  selector, and the exact component transport is passed explicitly.  For this
  frozen program's single peer-observable DigestFailure equivalence class,
  DigestMismatch, the target representation is the canonical one-octet reason
  code 0x01.

  This does not assert that DigestFailure has one inhabitant.  Nor does it prove
  the concrete two-octet provider encoding 00 01.  Provider behavior, LLVM 18,
  native execution, outer framing, and physical write success remain external
  gates.
*)

Definition RejectedOperandId := nat.
Definition RejectedLLVMBlockId := nat.
Definition RejectedReasonCode := nat.
Definition digestMismatchReasonCode : RejectedReasonCode := 1.

Record RejectedResponseLLVMModel : Type := mkRejectedResponseLLVMModel {
  llvmRejectedSystems : SystemsRejectedResponseModel;
  llvmRejectedAccepted : AcceptedResponseLLVMModel;
  llvmRejectedRuntimeSymbols : RuntimeSymbolModel;

  llvmRejectedTransportSSAFor : ValueId -> RejectedOperandId;
  llvmRejectedPayloadSSAFor : ValueId -> RejectedOperandId;
  llvmRejectedBlockSSAFor : DigestBlockId -> RejectedLLVMBlockId;

  llvmRejectedExpectedTransportOperand : RejectedOperandId;
  llvmRejectedActualTransportOperand : RejectedOperandId;
  llvmRejectedExpectedReleasedOwner : RejectedOperandId;
  llvmRejectedActualReleasedOwner : RejectedOperandId;
  llvmRejectedExpectedBlock : RejectedLLVMBlockId;
  llvmRejectedActualBlock : RejectedLLVMBlockId;

  llvmRejectedActualReasonCode : RejectedReasonCode;
  llvmRejectedReasonIsOneOctet : bool;
  llvmRejectedUsesPhysicalSelector : bool;
  llvmRejectedReleasePrecedesSelector : bool;
  llvmRejectedTerminatesFailure : bool;

  llvmRejectedGenericCallPresent : bool;
  llvmRejectedNullarySelectorPresent : bool;
  llvmRejectedAmbientTransportPresent : bool;
  llvmRejectedAmbientReasonPresent : bool;
  llvmRejectedAmbientRejectedStatePresent : bool;
  llvmRejectedAmbientDigestErrorPresent : bool;
  llvmRejectedUnauthorizedPointerStrengtheningPresent : bool;
  llvmRejectedEvidenceDerivedSymbolPresent : bool
}.

Record RejectedResponseLLVMVerificationSuccess
  (model : RejectedResponseLLVMModel) : Prop :=
  mkRejectedResponseLLVMVerificationSuccess {
    llvm_rejected_success_systems :
      SystemsRejectedResponseVerificationSuccess (llvmRejectedSystems model);
    llvm_rejected_success_accepted :
      AcceptedResponseLLVMVerificationSuccess (llvmRejectedAccepted model);
    llvm_rejected_success_runtime_symbols :
      RuntimeSymbolVerificationSuccess (llvmRejectedRuntimeSymbols model);
    llvm_rejected_success_accepted_systems_align :
      llvmAcceptedSystems (llvmRejectedAccepted model) =
        systemsRejectedAccepted (llvmRejectedSystems model);

    llvm_rejected_success_expected_transport :
      llvmRejectedExpectedTransportOperand model =
        llvmRejectedTransportSSAFor model
          (systemsRejectedWitnessTransport (llvmRejectedSystems model));
    llvm_rejected_success_transport_operand :
      llvmRejectedActualTransportOperand model =
        llvmRejectedExpectedTransportOperand model;

    llvm_rejected_success_expected_release_owner :
      llvmRejectedExpectedReleasedOwner model =
        llvmRejectedPayloadSSAFor model
          (systemsRejectedWitnessPayloadOwner (llvmRejectedSystems model));
    llvm_rejected_success_digest_payload_correspondence :
      llvmDigestActualPayloadOperand
        (llvmStorageDigest (llvmAcceptedStorage (llvmRejectedAccepted model))) =
        llvmRejectedExpectedReleasedOwner model;
    llvm_rejected_success_release_owner :
      llvmRejectedActualReleasedOwner model =
        llvmRejectedExpectedReleasedOwner model;

    llvm_rejected_success_expected_block :
      llvmRejectedExpectedBlock model =
        llvmRejectedBlockSSAFor model
          (systemsRejectedWitnessBlock (llvmRejectedSystems model));
    llvm_rejected_success_block :
      llvmRejectedActualBlock model = llvmRejectedExpectedBlock model;
    llvm_rejected_success_digest_failure_edge :
      llvmDigestActualFailureBlock
        (llvmStorageDigest (llvmAcceptedStorage (llvmRejectedAccepted model))) =
        llvmRejectedActualBlock model;

    llvm_rejected_success_reason_code :
      llvmRejectedActualReasonCode model = digestMismatchReasonCode;
    llvm_rejected_success_reason_width :
      llvmRejectedReasonIsOneOctet model = true;
    llvm_rejected_success_physical_selector :
      llvmRejectedUsesPhysicalSelector model = true;
    llvm_rejected_success_release_order :
      llvmRejectedReleasePrecedesSelector model = true;
    llvm_rejected_success_termination :
      llvmRejectedTerminatesFailure model = true;

    llvm_rejected_success_no_generic_call :
      llvmRejectedGenericCallPresent model = false;
    llvm_rejected_success_no_nullary_selector :
      llvmRejectedNullarySelectorPresent model = false;
    llvm_rejected_success_no_ambient_transport :
      llvmRejectedAmbientTransportPresent model = false;
    llvm_rejected_success_no_ambient_reason :
      llvmRejectedAmbientReasonPresent model = false;
    llvm_rejected_success_no_ambient_rejected_state :
      llvmRejectedAmbientRejectedStatePresent model = false;
    llvm_rejected_success_no_ambient_digest_error :
      llvmRejectedAmbientDigestErrorPresent model = false;
    llvm_rejected_success_no_strengthening :
      llvmRejectedUnauthorizedPointerStrengtheningPresent model = false;
    llvm_rejected_success_no_evidence_symbol :
      llvmRejectedEvidenceDerivedSymbolPresent model = false
  }.

Theorem verified_llvm_rejected_reuses_systems_rejected_authority :
  forall model,
    RejectedResponseLLVMVerificationSuccess model ->
    SystemsRejectedResponseVerificationSuccess (llvmRejectedSystems model).
Proof.
  intros model H.
  exact (llvm_rejected_success_systems model H).
Qed.

Theorem verified_llvm_rejected_reuses_accepted_response_authority :
  forall model,
    RejectedResponseLLVMVerificationSuccess model ->
    AcceptedResponseLLVMVerificationSuccess (llvmRejectedAccepted model) /\
    llvmAcceptedSystems (llvmRejectedAccepted model) =
      systemsRejectedAccepted (llvmRejectedSystems model).
Proof.
  intros model H.
  split.
  - exact (llvm_rejected_success_accepted model H).
  - exact (llvm_rejected_success_accepted_systems_align model H).
Qed.

Theorem verified_llvm_rejected_reuses_runtime_symbol_authority :
  forall model,
    RejectedResponseLLVMVerificationSuccess model ->
    RuntimeSymbolVerificationSuccess (llvmRejectedRuntimeSymbols model).
Proof.
  intros model H.
  exact (llvm_rejected_success_runtime_symbols model H).
Qed.

Theorem verified_llvm_rejected_preserves_exact_digest_failure_edge :
  forall model,
    RejectedResponseLLVMVerificationSuccess model ->
    llvmRejectedActualBlock model =
      llvmRejectedBlockSSAFor model
        (systemsRejectedWitnessBlock (llvmRejectedSystems model)) /\
    llvmDigestActualFailureBlock
      (llvmStorageDigest (llvmAcceptedStorage (llvmRejectedAccepted model))) =
      llvmRejectedActualBlock model.
Proof.
  intros model H.
  split.
  - rewrite (llvm_rejected_success_block model H).
    exact (llvm_rejected_success_expected_block model H).
  - exact (llvm_rejected_success_digest_failure_edge model H).
Qed.

Theorem verified_llvm_rejected_releases_exact_digest_payload_before_selector :
  forall model,
    RejectedResponseLLVMVerificationSuccess model ->
    llvmRejectedActualReleasedOwner model =
      llvmRejectedPayloadSSAFor model
        (systemsRejectedWitnessPayloadOwner (llvmRejectedSystems model)) /\
    llvmDigestActualPayloadOperand
      (llvmStorageDigest (llvmAcceptedStorage (llvmRejectedAccepted model))) =
      llvmRejectedActualReleasedOwner model /\
    llvmRejectedReleasePrecedesSelector model = true.
Proof.
  intros model H.
  repeat split.
  - rewrite (llvm_rejected_success_release_owner model H).
    exact (llvm_rejected_success_expected_release_owner model H).
  - rewrite (llvm_rejected_success_release_owner model H).
    exact (llvm_rejected_success_digest_payload_correspondence model H).
  - exact (llvm_rejected_success_release_order model H).
Qed.

Theorem verified_llvm_rejected_preserves_exact_transport_operand :
  forall model,
    RejectedResponseLLVMVerificationSuccess model ->
    llvmRejectedActualTransportOperand model =
      llvmRejectedTransportSSAFor model
        (systemsRejectedWitnessTransport (llvmRejectedSystems model)).
Proof.
  intros model H.
  rewrite (llvm_rejected_success_transport_operand model H).
  exact (llvm_rejected_success_expected_transport model H).
Qed.

Theorem verified_llvm_rejected_maps_single_observable_digest_mismatch_to_reason_0x01 :
  forall model,
    RejectedResponseLLVMVerificationSuccess model ->
    systemsRejectedObservableClassIsDigestMismatch
      (llvmRejectedSystems model) = true /\
    systemsRejectedObservableClassCount (llvmRejectedSystems model) = 1 /\
    llvmRejectedActualReasonCode model = 1 /\
    llvmRejectedReasonIsOneOctet model = true.
Proof.
  intros model H.
  pose proof (llvm_rejected_success_systems model H) as Hsystems.
  repeat split.
  - exact (systems_rejected_success_observable_digest_mismatch _ Hsystems).
  - exact (systems_rejected_success_single_observable_class _ Hsystems).
  - exact (llvm_rejected_success_reason_code model H).
  - exact (llvm_rejected_success_reason_width model H).
Qed.

Theorem verified_llvm_rejected_uses_physical_selector_and_preserves_failure :
  forall model,
    RejectedResponseLLVMVerificationSuccess model ->
    llvmRejectedUsesPhysicalSelector model = true /\
    llvmRejectedTerminatesFailure model = true.
Proof.
  intros model H.
  split.
  - exact (llvm_rejected_success_physical_selector model H).
  - exact (llvm_rejected_success_termination model H).
Qed.

Theorem verified_llvm_rejected_forbids_ambient_nullary_generic_strengthening_and_evidence_symbols :
  forall model,
    RejectedResponseLLVMVerificationSuccess model ->
    llvmRejectedGenericCallPresent model = false /\
    llvmRejectedNullarySelectorPresent model = false /\
    llvmRejectedAmbientTransportPresent model = false /\
    llvmRejectedAmbientReasonPresent model = false /\
    llvmRejectedAmbientRejectedStatePresent model = false /\
    llvmRejectedAmbientDigestErrorPresent model = false /\
    llvmRejectedUnauthorizedPointerStrengtheningPresent model = false /\
    llvmRejectedEvidenceDerivedSymbolPresent model = false.
Proof.
  intros model H.
  repeat split.
  - exact (llvm_rejected_success_no_generic_call model H).
  - exact (llvm_rejected_success_no_nullary_selector model H).
  - exact (llvm_rejected_success_no_ambient_transport model H).
  - exact (llvm_rejected_success_no_ambient_reason model H).
  - exact (llvm_rejected_success_no_ambient_rejected_state model H).
  - exact (llvm_rejected_success_no_ambient_digest_error model H).
  - exact (llvm_rejected_success_no_strengthening model H).
  - exact (llvm_rejected_success_no_evidence_symbol model H).
Qed.

Theorem llvm_rejected_transport_drift_is_rejected :
  forall model,
    llvmRejectedActualTransportOperand model <>
      llvmRejectedExpectedTransportOperand model ->
    ~ RejectedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (llvm_rejected_success_transport_operand model H).
Qed.

Theorem llvm_rejected_release_owner_or_order_drift_is_rejected :
  forall model,
    llvmRejectedActualReleasedOwner model <>
      llvmRejectedExpectedReleasedOwner model \/
    llvmDigestActualPayloadOperand
      (llvmStorageDigest (llvmAcceptedStorage (llvmRejectedAccepted model))) <>
      llvmRejectedExpectedReleasedOwner model \/
    llvmRejectedReleasePrecedesSelector model = false ->
    ~ RejectedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Howner | [Hdigest | Horder]].
  - apply Howner. exact (llvm_rejected_success_release_owner model H).
  - apply Hdigest. exact (llvm_rejected_success_digest_payload_correspondence model H).
  - rewrite (llvm_rejected_success_release_order model H) in Horder. discriminate.
Qed.

Theorem llvm_rejected_block_or_digest_edge_drift_is_rejected :
  forall model,
    llvmRejectedActualBlock model <> llvmRejectedExpectedBlock model \/
    llvmRejectedExpectedBlock model <>
      llvmRejectedBlockSSAFor model
        (systemsRejectedWitnessBlock (llvmRejectedSystems model)) \/
    llvmDigestActualFailureBlock
      (llvmStorageDigest (llvmAcceptedStorage (llvmRejectedAccepted model))) <>
      llvmRejectedActualBlock model ->
    ~ RejectedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hblock | [Hexpected | Hedge]].
  - apply Hblock. exact (llvm_rejected_success_block model H).
  - apply Hexpected. exact (llvm_rejected_success_expected_block model H).
  - apply Hedge. exact (llvm_rejected_success_digest_failure_edge model H).
Qed.

Theorem llvm_rejected_reason_representation_drift_is_rejected :
  forall model,
    llvmRejectedActualReasonCode model <> digestMismatchReasonCode \/
    llvmRejectedReasonIsOneOctet model = false \/
    systemsRejectedObservableClassIsDigestMismatch (llvmRejectedSystems model) = false \/
    systemsRejectedObservableClassCount (llvmRejectedSystems model) <> 1 ->
    ~ RejectedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hcode | [Hwidth | [Hclass | Hcount]]].
  - apply Hcode. exact (llvm_rejected_success_reason_code model H).
  - rewrite (llvm_rejected_success_reason_width model H) in Hwidth. discriminate.
  - pose proof (llvm_rejected_success_systems model H) as Hsystems.
    rewrite (systems_rejected_success_observable_digest_mismatch _ Hsystems) in Hclass. discriminate.
  - pose proof (llvm_rejected_success_systems model H) as Hsystems.
    apply Hcount. exact (systems_rejected_success_single_observable_class _ Hsystems).
Qed.

Theorem llvm_rejected_selector_or_termination_drift_is_rejected :
  forall model,
    llvmRejectedUsesPhysicalSelector model = false \/
    llvmRejectedTerminatesFailure model = false ->
    ~ RejectedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hselector | Hend].
  - rewrite (llvm_rejected_success_physical_selector model H) in Hselector. discriminate.
  - rewrite (llvm_rejected_success_termination model H) in Hend. discriminate.
Qed.

Theorem llvm_rejected_ambient_or_symbol_drift_is_rejected :
  forall model,
    llvmRejectedGenericCallPresent model = true \/
    llvmRejectedNullarySelectorPresent model = true \/
    llvmRejectedAmbientTransportPresent model = true \/
    llvmRejectedAmbientReasonPresent model = true \/
    llvmRejectedAmbientRejectedStatePresent model = true \/
    llvmRejectedAmbientDigestErrorPresent model = true \/
    llvmRejectedUnauthorizedPointerStrengtheningPresent model = true \/
    llvmRejectedEvidenceDerivedSymbolPresent model = true ->
    ~ RejectedResponseLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hgeneric | [Hnullary | [Htransport | [Hreason | [Hrejected | [Hdigest | [Hstrengthen | Hevidence]]]]]]].
  - rewrite (llvm_rejected_success_no_generic_call model H) in Hgeneric. discriminate.
  - rewrite (llvm_rejected_success_no_nullary_selector model H) in Hnullary. discriminate.
  - rewrite (llvm_rejected_success_no_ambient_transport model H) in Htransport. discriminate.
  - rewrite (llvm_rejected_success_no_ambient_reason model H) in Hreason. discriminate.
  - rewrite (llvm_rejected_success_no_ambient_rejected_state model H) in Hrejected. discriminate.
  - rewrite (llvm_rejected_success_no_ambient_digest_error model H) in Hdigest. discriminate.
  - rewrite (llvm_rejected_success_no_strengthening model H) in Hstrengthen. discriminate.
  - rewrite (llvm_rejected_success_no_evidence_symbol model H) in Hevidence. discriminate.
Qed.
