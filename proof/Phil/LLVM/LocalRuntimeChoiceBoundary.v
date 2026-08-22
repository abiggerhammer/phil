From Phil.Systems Require Import LocalRuntimeChoice.
From Phil.LLVM Require Import PayloadCancelChoice.

(*
  PHIL-LLVM-LOCAL-RUNTIME-CHOICE-BOUNDARY-001 — backend competence boundary
  for PR #65.

  PR #65 deliberately selects no physical representation for choose_supported
  or its branch-local UInt16 payload.  Generic LLVM lowering must therefore
  fail closed at the local-choice block with LLVMUnreachable None.  This proof
  records that boundary: prior payload/cancel lowering authority remains
  available, but no branch, switch, runtime primitive, payload materialization,
  runtime-ABI extension, version wire encoding, or TranslationValidated claim
  is invented for the unlowered local choice.

  This is intentionally not a PHIL-LLVM-CERT successor.  There is no concrete
  local-choice target to certify yet.
*)

Definition LocalRuntimeChoiceLLVMBlockId := nat.

Record LocalRuntimeChoiceLLVMBoundaryModel : Type :=
  mkLocalRuntimeChoiceLLVMBoundaryModel {
    llvmLocalChoiceSystems : SystemsLocalRuntimeChoiceModel;
    llvmLocalChoicePayloadCancelPredecessor : PayloadCancelChoiceLLVMModel;

    llvmLocalChoiceWitnessChoiceBlock : LocalRuntimeChoiceLLVMBlockId;
    llvmLocalChoiceActualChoiceBlock : LocalRuntimeChoiceLLVMBlockId;
    llvmLocalChoiceTerminatorIsUnreachableNone : bool;

    llvmLocalChoiceSyntheticConditionalBranchPresent : bool;
    llvmLocalChoiceSyntheticSwitchPresent : bool;
    llvmLocalChoicePhysicalChooserCallPresent : bool;
    llvmLocalChoiceSelectedVersionMaterialized : bool;
    llvmLocalChoiceRuntimeABIExtendedForChooser : bool;
    llvmLocalChoiceVersionWireEncodingSelected : bool;

    llvmLocalChoicePayloadCancelABIPreserved : bool;
    llvmLocalChoicePayloadCancelLoweringAuthorityPreserved : bool;
    llvmLocalChoiceTranslationValidatedClaimed : bool
  }.

Record LocalRuntimeChoiceLLVMBoundaryVerificationSuccess
  (model : LocalRuntimeChoiceLLVMBoundaryModel) : Prop :=
  mkLocalRuntimeChoiceLLVMBoundaryVerificationSuccess {
    llvm_local_choice_boundary_success_systems :
      SystemsLocalRuntimeChoiceVerificationSuccess
        (llvmLocalChoiceSystems model);
    llvm_local_choice_boundary_success_payload_cancel :
      PayloadCancelChoiceLLVMVerificationSuccess
        (llvmLocalChoicePayloadCancelPredecessor model);
    llvm_local_choice_boundary_success_payload_cancel_systems_align :
      llvmPayloadCancelSystems (llvmLocalChoicePayloadCancelPredecessor model) =
        systemsLocalChoicePayloadCancelPredecessor
          (llvmLocalChoiceSystems model);

    llvm_local_choice_boundary_success_choice_block :
      llvmLocalChoiceActualChoiceBlock model =
        llvmLocalChoiceWitnessChoiceBlock model;
    llvm_local_choice_boundary_success_unreachable :
      llvmLocalChoiceTerminatorIsUnreachableNone model = true;

    llvm_local_choice_boundary_success_no_synthetic_branch :
      llvmLocalChoiceSyntheticConditionalBranchPresent model = false;
    llvm_local_choice_boundary_success_no_synthetic_switch :
      llvmLocalChoiceSyntheticSwitchPresent model = false;
    llvm_local_choice_boundary_success_no_chooser_call :
      llvmLocalChoicePhysicalChooserCallPresent model = false;
    llvm_local_choice_boundary_success_no_selected_version_materialization :
      llvmLocalChoiceSelectedVersionMaterialized model = false;
    llvm_local_choice_boundary_success_no_abi_extension :
      llvmLocalChoiceRuntimeABIExtendedForChooser model = false;
    llvm_local_choice_boundary_success_no_version_wire_encoding :
      llvmLocalChoiceVersionWireEncodingSelected model = false;

    llvm_local_choice_boundary_success_payload_cancel_abi :
      llvmLocalChoicePayloadCancelABIPreserved model = true;
    llvm_local_choice_boundary_success_payload_cancel_lowering :
      llvmLocalChoicePayloadCancelLoweringAuthorityPreserved model = true;
    llvm_local_choice_boundary_success_no_translation_claim :
      llvmLocalChoiceTranslationValidatedClaimed model = false
  }.

Theorem verified_llvm_local_choice_boundary_reuses_semantic_and_payload_cancel_authority :
  forall model,
    LocalRuntimeChoiceLLVMBoundaryVerificationSuccess model ->
    SystemsLocalRuntimeChoiceVerificationSuccess
      (llvmLocalChoiceSystems model) /\
    PayloadCancelChoiceLLVMVerificationSuccess
      (llvmLocalChoicePayloadCancelPredecessor model) /\
    llvmPayloadCancelSystems (llvmLocalChoicePayloadCancelPredecessor model) =
      systemsLocalChoicePayloadCancelPredecessor
        (llvmLocalChoiceSystems model).
Proof.
  intros model H.
  split.
  - exact (llvm_local_choice_boundary_success_systems model H).
  - split.
    + exact (llvm_local_choice_boundary_success_payload_cancel model H).
    + exact (llvm_local_choice_boundary_success_payload_cancel_systems_align model H).
Qed.

Theorem verified_llvm_local_choice_fails_closed_at_exact_choice_block :
  forall model,
    LocalRuntimeChoiceLLVMBoundaryVerificationSuccess model ->
    llvmLocalChoiceActualChoiceBlock model =
      llvmLocalChoiceWitnessChoiceBlock model /\
    llvmLocalChoiceTerminatorIsUnreachableNone model = true.
Proof.
  intros model H; split.
  - exact (llvm_local_choice_boundary_success_choice_block model H).
  - exact (llvm_local_choice_boundary_success_unreachable model H).
Qed.

Theorem verified_llvm_local_choice_invents_no_physical_representation :
  forall model,
    LocalRuntimeChoiceLLVMBoundaryVerificationSuccess model ->
    llvmLocalChoiceSyntheticConditionalBranchPresent model = false /\
    llvmLocalChoiceSyntheticSwitchPresent model = false /\
    llvmLocalChoicePhysicalChooserCallPresent model = false /\
    llvmLocalChoiceSelectedVersionMaterialized model = false /\
    llvmLocalChoiceRuntimeABIExtendedForChooser model = false /\
    llvmLocalChoiceVersionWireEncodingSelected model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_local_choice_boundary_success_no_synthetic_branch model H).
  - exact (llvm_local_choice_boundary_success_no_synthetic_switch model H).
  - exact (llvm_local_choice_boundary_success_no_chooser_call model H).
  - exact (llvm_local_choice_boundary_success_no_selected_version_materialization model H).
  - exact (llvm_local_choice_boundary_success_no_abi_extension model H).
  - exact (llvm_local_choice_boundary_success_no_version_wire_encoding model H).
Qed.

Theorem verified_llvm_local_choice_preserves_predecessor_target_without_claiming_translation :
  forall model,
    LocalRuntimeChoiceLLVMBoundaryVerificationSuccess model ->
    llvmLocalChoicePayloadCancelABIPreserved model = true /\
    llvmLocalChoicePayloadCancelLoweringAuthorityPreserved model = true /\
    llvmLocalChoiceTranslationValidatedClaimed model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_local_choice_boundary_success_payload_cancel_abi model H).
  - exact (llvm_local_choice_boundary_success_payload_cancel_lowering model H).
  - exact (llvm_local_choice_boundary_success_no_translation_claim model H).
Qed.

Theorem llvm_local_choice_non_fail_closed_lowering_is_rejected :
  forall model,
    llvmLocalChoiceActualChoiceBlock model <>
      llvmLocalChoiceWitnessChoiceBlock model \/
    llvmLocalChoiceTerminatorIsUnreachableNone model = false \/
    llvmLocalChoiceSyntheticConditionalBranchPresent model = true \/
    llvmLocalChoiceSyntheticSwitchPresent model = true ->
    ~ LocalRuntimeChoiceLLVMBoundaryVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hblock | [Hunreachable | [Hbranch | Hswitch]]].
  - apply Hblock. exact (llvm_local_choice_boundary_success_choice_block model H).
  - rewrite (llvm_local_choice_boundary_success_unreachable model H) in Hunreachable. discriminate.
  - rewrite (llvm_local_choice_boundary_success_no_synthetic_branch model H) in Hbranch. discriminate.
  - rewrite (llvm_local_choice_boundary_success_no_synthetic_switch model H) in Hswitch. discriminate.
Qed.

Theorem llvm_local_choice_invented_representation_or_certification_is_rejected :
  forall model,
    llvmLocalChoicePhysicalChooserCallPresent model = true \/
    llvmLocalChoiceSelectedVersionMaterialized model = true \/
    llvmLocalChoiceRuntimeABIExtendedForChooser model = true \/
    llvmLocalChoiceVersionWireEncodingSelected model = true \/
    llvmLocalChoicePayloadCancelABIPreserved model = false \/
    llvmLocalChoicePayloadCancelLoweringAuthorityPreserved model = false \/
    llvmLocalChoiceTranslationValidatedClaimed model = true ->
    ~ LocalRuntimeChoiceLLVMBoundaryVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hcall | [Hpayload | [Habi | [Hwire | [Hpabi | [Hplower | Hclaim]]]]]].
  - rewrite (llvm_local_choice_boundary_success_no_chooser_call model H) in Hcall. discriminate.
  - rewrite (llvm_local_choice_boundary_success_no_selected_version_materialization model H) in Hpayload. discriminate.
  - rewrite (llvm_local_choice_boundary_success_no_abi_extension model H) in Habi. discriminate.
  - rewrite (llvm_local_choice_boundary_success_no_version_wire_encoding model H) in Hwire. discriminate.
  - rewrite (llvm_local_choice_boundary_success_payload_cancel_abi model H) in Hpabi. discriminate.
  - rewrite (llvm_local_choice_boundary_success_payload_cancel_lowering model H) in Hplower. discriminate.
  - rewrite (llvm_local_choice_boundary_success_no_translation_claim model H) in Hclaim. discriminate.
Qed.
