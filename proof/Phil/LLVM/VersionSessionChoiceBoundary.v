From Phil.Systems Require Import VersionSessionChoice.
From Phil.LLVM Require Import LocalRuntimeChoiceBoundary.

(*
  PHIL-LLVM-VERSION-SESSION-CHOICE-BOUNDARY-001 — generic LLVM competence
  boundary for PR #67 before a physical unsupported/version(selected) lowering
  exists.

  The target preserves the already-proved local-choice fail-closed boundary and
  payload/cancel predecessor authority.  The new server OpSessionSelect nodes
  remain explicit LLVMPoison markers, while the client TermSessionOffer remains
  LLVMUnreachable None.  No discriminator dispatch, UInt16 wire layout,
  selected-version physical materialization, runtime ABI, outer framing, or
  TranslationValidated claim is invented.
*)

Definition VersionSessionChoiceLLVMBlockId := nat.

Record VersionSessionChoiceLLVMBoundaryModel : Type :=
  mkVersionSessionChoiceLLVMBoundaryModel {
    llvmVersionChoiceSystems : SystemsVersionSessionChoiceModel;
    llvmVersionChoiceLocalBoundaryPredecessor : LocalRuntimeChoiceLLVMBoundaryModel;

    llvmVersionChoiceWitnessUnsupportedBlock : VersionSessionChoiceLLVMBlockId;
    llvmVersionChoiceActualUnsupportedBlock : VersionSessionChoiceLLVMBlockId;
    llvmVersionChoiceUnsupportedPoisonExact : bool;
    llvmVersionChoiceUnsupportedPoisonCount : nat;

    llvmVersionChoiceWitnessVersionBlock : VersionSessionChoiceLLVMBlockId;
    llvmVersionChoiceActualVersionBlock : VersionSessionChoiceLLVMBlockId;
    llvmVersionChoiceVersionPoisonExact : bool;
    llvmVersionChoiceVersionPoisonCount : nat;

    llvmVersionChoiceWitnessClientOfferBlock : VersionSessionChoiceLLVMBlockId;
    llvmVersionChoiceActualClientOfferBlock : VersionSessionChoiceLLVMBlockId;
    llvmVersionChoiceClientOfferUnreachableNone : bool;

    llvmVersionChoiceLocalChoiceBoundaryPreserved : bool;
    llvmVersionChoicePayloadCancelLoweringPreserved : bool;

    llvmVersionChoiceSyntheticConditionalBranchPresent : bool;
    llvmVersionChoiceSyntheticSwitchPresent : bool;
    llvmVersionChoicePhysicalSelectedVersionMaterialized : bool;
    llvmVersionChoiceRuntimeABISelected : bool;
    llvmVersionChoiceWireDiscriminatorSelected : bool;
    llvmVersionChoiceUInt16WireLayoutSelected : bool;
    llvmVersionChoiceOuterFramingSelected : bool;
    llvmVersionChoiceTranslationValidatedClaimed : bool
  }.

Record VersionSessionChoiceLLVMBoundaryVerificationSuccess
  (model : VersionSessionChoiceLLVMBoundaryModel) : Prop :=
  mkVersionSessionChoiceLLVMBoundaryVerificationSuccess {
    llvm_version_choice_boundary_success_systems :
      SystemsVersionSessionChoiceVerificationSuccess
        (llvmVersionChoiceSystems model);
    llvm_version_choice_boundary_success_local_predecessor :
      LocalRuntimeChoiceLLVMBoundaryVerificationSuccess
        (llvmVersionChoiceLocalBoundaryPredecessor model);
    llvm_version_choice_boundary_success_local_alignment :
      llvmLocalChoiceSystems (llvmVersionChoiceLocalBoundaryPredecessor model) =
        systemsVersionChoiceLocalPredecessor (llvmVersionChoiceSystems model);

    llvm_version_choice_boundary_success_unsupported_block :
      llvmVersionChoiceActualUnsupportedBlock model =
        llvmVersionChoiceWitnessUnsupportedBlock model;
    llvm_version_choice_boundary_success_unsupported_poison :
      llvmVersionChoiceUnsupportedPoisonExact model = true;
    llvm_version_choice_boundary_success_unsupported_count :
      llvmVersionChoiceUnsupportedPoisonCount model = 1;

    llvm_version_choice_boundary_success_version_block :
      llvmVersionChoiceActualVersionBlock model =
        llvmVersionChoiceWitnessVersionBlock model;
    llvm_version_choice_boundary_success_version_poison :
      llvmVersionChoiceVersionPoisonExact model = true;
    llvm_version_choice_boundary_success_version_count :
      llvmVersionChoiceVersionPoisonCount model = 1;

    llvm_version_choice_boundary_success_client_offer_block :
      llvmVersionChoiceActualClientOfferBlock model =
        llvmVersionChoiceWitnessClientOfferBlock model;
    llvm_version_choice_boundary_success_client_offer_unreachable :
      llvmVersionChoiceClientOfferUnreachableNone model = true;

    llvm_version_choice_boundary_success_local_boundary_preserved :
      llvmVersionChoiceLocalChoiceBoundaryPreserved model = true;
    llvm_version_choice_boundary_success_payload_cancel_preserved :
      llvmVersionChoicePayloadCancelLoweringPreserved model = true;

    llvm_version_choice_boundary_success_no_synthetic_branch :
      llvmVersionChoiceSyntheticConditionalBranchPresent model = false;
    llvm_version_choice_boundary_success_no_synthetic_switch :
      llvmVersionChoiceSyntheticSwitchPresent model = false;
    llvm_version_choice_boundary_success_no_payload_materialization :
      llvmVersionChoicePhysicalSelectedVersionMaterialized model = false;
    llvm_version_choice_boundary_success_no_runtime_abi :
      llvmVersionChoiceRuntimeABISelected model = false;
    llvm_version_choice_boundary_success_no_wire_discriminator :
      llvmVersionChoiceWireDiscriminatorSelected model = false;
    llvm_version_choice_boundary_success_no_wire_layout :
      llvmVersionChoiceUInt16WireLayoutSelected model = false;
    llvm_version_choice_boundary_success_no_outer_framing :
      llvmVersionChoiceOuterFramingSelected model = false;
    llvm_version_choice_boundary_success_no_translation_claim :
      llvmVersionChoiceTranslationValidatedClaimed model = false
  }.

Theorem verified_llvm_version_choice_boundary_reuses_semantic_and_local_authority :
  forall model,
    VersionSessionChoiceLLVMBoundaryVerificationSuccess model ->
    SystemsVersionSessionChoiceVerificationSuccess
      (llvmVersionChoiceSystems model) /\
    LocalRuntimeChoiceLLVMBoundaryVerificationSuccess
      (llvmVersionChoiceLocalBoundaryPredecessor model) /\
    llvmLocalChoiceSystems (llvmVersionChoiceLocalBoundaryPredecessor model) =
      systemsVersionChoiceLocalPredecessor (llvmVersionChoiceSystems model).
Proof.
  intros model H.
  split.
  - exact (llvm_version_choice_boundary_success_systems model H).
  - split.
    + exact (llvm_version_choice_boundary_success_local_predecessor model H).
    + exact (llvm_version_choice_boundary_success_local_alignment model H).
Qed.

Theorem verified_llvm_version_choice_boundary_marks_exact_server_selects_unlowered :
  forall model,
    VersionSessionChoiceLLVMBoundaryVerificationSuccess model ->
    llvmVersionChoiceActualUnsupportedBlock model =
      llvmVersionChoiceWitnessUnsupportedBlock model /\
    llvmVersionChoiceUnsupportedPoisonExact model = true /\
    llvmVersionChoiceUnsupportedPoisonCount model = 1 /\
    llvmVersionChoiceActualVersionBlock model =
      llvmVersionChoiceWitnessVersionBlock model /\
    llvmVersionChoiceVersionPoisonExact model = true /\
    llvmVersionChoiceVersionPoisonCount model = 1.
Proof.
  intros model H; repeat split.
  - exact (llvm_version_choice_boundary_success_unsupported_block model H).
  - exact (llvm_version_choice_boundary_success_unsupported_poison model H).
  - exact (llvm_version_choice_boundary_success_unsupported_count model H).
  - exact (llvm_version_choice_boundary_success_version_block model H).
  - exact (llvm_version_choice_boundary_success_version_poison model H).
  - exact (llvm_version_choice_boundary_success_version_count model H).
Qed.

Theorem verified_llvm_version_choice_boundary_fails_closed_at_client_offer :
  forall model,
    VersionSessionChoiceLLVMBoundaryVerificationSuccess model ->
    llvmVersionChoiceActualClientOfferBlock model =
      llvmVersionChoiceWitnessClientOfferBlock model /\
    llvmVersionChoiceClientOfferUnreachableNone model = true.
Proof.
  intros model H; split.
  - exact (llvm_version_choice_boundary_success_client_offer_block model H).
  - exact (llvm_version_choice_boundary_success_client_offer_unreachable model H).
Qed.

Theorem verified_llvm_version_choice_boundary_preserves_predecessor_boundaries :
  forall model,
    VersionSessionChoiceLLVMBoundaryVerificationSuccess model ->
    llvmVersionChoiceLocalChoiceBoundaryPreserved model = true /\
    llvmVersionChoicePayloadCancelLoweringPreserved model = true.
Proof.
  intros model H; split.
  - exact (llvm_version_choice_boundary_success_local_boundary_preserved model H).
  - exact (llvm_version_choice_boundary_success_payload_cancel_preserved model H).
Qed.

Theorem verified_llvm_version_choice_boundary_invents_no_physical_representation :
  forall model,
    VersionSessionChoiceLLVMBoundaryVerificationSuccess model ->
    llvmVersionChoiceSyntheticConditionalBranchPresent model = false /\
    llvmVersionChoiceSyntheticSwitchPresent model = false /\
    llvmVersionChoicePhysicalSelectedVersionMaterialized model = false /\
    llvmVersionChoiceRuntimeABISelected model = false /\
    llvmVersionChoiceWireDiscriminatorSelected model = false /\
    llvmVersionChoiceUInt16WireLayoutSelected model = false /\
    llvmVersionChoiceOuterFramingSelected model = false /\
    llvmVersionChoiceTranslationValidatedClaimed model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_version_choice_boundary_success_no_synthetic_branch model H).
  - exact (llvm_version_choice_boundary_success_no_synthetic_switch model H).
  - exact (llvm_version_choice_boundary_success_no_payload_materialization model H).
  - exact (llvm_version_choice_boundary_success_no_runtime_abi model H).
  - exact (llvm_version_choice_boundary_success_no_wire_discriminator model H).
  - exact (llvm_version_choice_boundary_success_no_wire_layout model H).
  - exact (llvm_version_choice_boundary_success_no_outer_framing model H).
  - exact (llvm_version_choice_boundary_success_no_translation_claim model H).
Qed.

Theorem llvm_version_choice_non_fail_closed_server_lowering_is_rejected :
  forall model,
    llvmVersionChoiceActualUnsupportedBlock model <>
      llvmVersionChoiceWitnessUnsupportedBlock model \/
    llvmVersionChoiceUnsupportedPoisonExact model = false \/
    llvmVersionChoiceUnsupportedPoisonCount model <> 1 \/
    llvmVersionChoiceActualVersionBlock model <>
      llvmVersionChoiceWitnessVersionBlock model \/
    llvmVersionChoiceVersionPoisonExact model = false \/
    llvmVersionChoiceVersionPoisonCount model <> 1 ->
    ~ VersionSessionChoiceLLVMBoundaryVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hub | [Hup | [Huc | [Hvb | [Hvp | Hvc]]]]].
  - apply Hub. exact (llvm_version_choice_boundary_success_unsupported_block model H).
  - rewrite (llvm_version_choice_boundary_success_unsupported_poison model H) in Hup. discriminate.
  - apply Huc. exact (llvm_version_choice_boundary_success_unsupported_count model H).
  - apply Hvb. exact (llvm_version_choice_boundary_success_version_block model H).
  - rewrite (llvm_version_choice_boundary_success_version_poison model H) in Hvp. discriminate.
  - apply Hvc. exact (llvm_version_choice_boundary_success_version_count model H).
Qed.

Theorem llvm_version_choice_invented_representation_or_translation_is_rejected :
  forall model,
    llvmVersionChoiceClientOfferUnreachableNone model = false \/
    llvmVersionChoiceLocalChoiceBoundaryPreserved model = false \/
    llvmVersionChoicePayloadCancelLoweringPreserved model = false \/
    llvmVersionChoiceSyntheticConditionalBranchPresent model = true \/
    llvmVersionChoiceSyntheticSwitchPresent model = true \/
    llvmVersionChoicePhysicalSelectedVersionMaterialized model = true \/
    llvmVersionChoiceRuntimeABISelected model = true \/
    llvmVersionChoiceWireDiscriminatorSelected model = true \/
    llvmVersionChoiceUInt16WireLayoutSelected model = true \/
    llvmVersionChoiceOuterFramingSelected model = true \/
    llvmVersionChoiceTranslationValidatedClaimed model = true ->
    ~ VersionSessionChoiceLLVMBoundaryVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hoffer | [Hlocal | [Hpayload | [Hbranch | [Hswitch | [Hmat | [Habi | [Hdisc | [Hwire | [Hframe | Hclaim]]]]]]]]]].
  - rewrite (llvm_version_choice_boundary_success_client_offer_unreachable model H) in Hoffer. discriminate.
  - rewrite (llvm_version_choice_boundary_success_local_boundary_preserved model H) in Hlocal. discriminate.
  - rewrite (llvm_version_choice_boundary_success_payload_cancel_preserved model H) in Hpayload. discriminate.
  - rewrite (llvm_version_choice_boundary_success_no_synthetic_branch model H) in Hbranch. discriminate.
  - rewrite (llvm_version_choice_boundary_success_no_synthetic_switch model H) in Hswitch. discriminate.
  - rewrite (llvm_version_choice_boundary_success_no_payload_materialization model H) in Hmat. discriminate.
  - rewrite (llvm_version_choice_boundary_success_no_runtime_abi model H) in Habi. discriminate.
  - rewrite (llvm_version_choice_boundary_success_no_wire_discriminator model H) in Hdisc. discriminate.
  - rewrite (llvm_version_choice_boundary_success_no_wire_layout model H) in Hwire. discriminate.
  - rewrite (llvm_version_choice_boundary_success_no_outer_framing model H) in Hframe. discriminate.
  - rewrite (llvm_version_choice_boundary_success_no_translation_claim model H) in Hclaim. discriminate.
Qed.
