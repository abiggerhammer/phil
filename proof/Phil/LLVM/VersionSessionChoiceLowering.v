From Phil.Systems Require Import VersionChoiceOperands.
From Phil.LLVM Require Import PayloadCancelChoice.

(*
  PHIL-LLVM-VERSION-SESSION-CHOICE-001 — normalized proof model for the
  concrete version-session-choice-v1 lowering introduced by PR #69.

  The theorem scope is target-shape and operand correspondence.  Concrete
  provider set semantics, transport-local offered-set association, byte I/O,
  malformed-input termination, write success, LLVM implementation correctness,
  linking, and native execution remain separately named gates.
*)

Definition VersionSessionChoiceLLVMBlockId := nat.

Record LLVMVersionSessionChoiceModel : Type :=
  mkLLVMVersionSessionChoiceModel {
    llvmVersionChoiceSystems : SystemsVersionChoiceOperandsModel;
    llvmVersionChoicePayloadCancelPredecessor : PayloadCancelChoiceLLVMModel;

    llvmVersionChoiceTargetExact : bool;
    llvmVersionChoiceDataLayoutExact : bool;
    llvmVersionChoiceABIProfileExact : bool;

    llvmVersionChoiceServerSupportedParameterExact : bool;
    llvmVersionChoiceHelloProjectionCount : nat;
    llvmVersionChoiceHelloProjectionExact : bool;

    llvmVersionChoiceChooserCount : nat;
    llvmVersionChoiceChooserServerSupportedExact : bool;
    llvmVersionChoiceChooserHelloVersionsExact : bool;
    llvmVersionChoiceChooserSelectedOutExact : bool;
    llvmVersionChoiceChooserTargetsExact : bool;

    llvmVersionChoiceUnsupportedSelectorCount : nat;
    llvmVersionChoiceUnsupportedTransportExact : bool;
    llvmVersionChoiceVersionPayloadBindingCount : nat;
    llvmVersionChoiceVersionSelectorCount : nat;
    llvmVersionChoiceVersionTransportExact : bool;
    llvmVersionChoiceVersionPayloadExact : bool;

    llvmVersionChoiceClientOfferExact : bool;
    llvmVersionChoiceClientPayloadBindingCount : nat;
    llvmVersionChoiceClientRefinementCount : nat;
    llvmVersionChoiceClientRefinementTransportExact : bool;
    llvmVersionChoiceClientRefinementPayloadExact : bool;
    llvmVersionChoiceClientRefinementTargetsExact : bool;

    llvmVersionChoiceWireUnsupported00 : bool;
    llvmVersionChoiceWireVersion01U16BE : bool;
    llvmVersionChoiceOuterFramingDefined : bool;

    llvmVersionChoiceUnloweredPoisonPresent : bool;
    llvmVersionChoiceGenericVersionCallPresent : bool;
    llvmVersionChoiceAmbientSupportedLookupPresent : bool;
    llvmVersionChoiceAmbientSelectedLookupPresent : bool;
    llvmVersionChoiceAmbientTransportLookupPresent : bool;

    llvmVersionChoiceProviderSetSemanticsProved : bool;
    llvmVersionChoiceTransportOfferedAssociationProved : bool;
    llvmVersionChoiceConcreteIOProved : bool;
    llvmVersionChoiceMalformedTerminationProved : bool;
    llvmVersionChoiceWriteSuccessProved : bool;
    llvmVersionChoiceLLVMImplementationCorrectnessProved : bool;
    llvmVersionChoiceNativeExecutionProved : bool
  }.

Record LLVMVersionSessionChoiceVerificationSuccess
  (model : LLVMVersionSessionChoiceModel) : Prop :=
  mkLLVMVersionSessionChoiceVerificationSuccess {
    llvm_version_choice_success_systems :
      SystemsVersionChoiceOperandsVerificationSuccess
        (llvmVersionChoiceSystems model);
    llvm_version_choice_success_payload_cancel :
      PayloadCancelChoiceLLVMVerificationSuccess
        (llvmVersionChoicePayloadCancelPredecessor model);

    llvm_version_choice_success_target :
      llvmVersionChoiceTargetExact model = true;
    llvm_version_choice_success_layout :
      llvmVersionChoiceDataLayoutExact model = true;
    llvm_version_choice_success_abi_profile :
      llvmVersionChoiceABIProfileExact model = true;

    llvm_version_choice_success_server_supported_parameter :
      llvmVersionChoiceServerSupportedParameterExact model = true;
    llvm_version_choice_success_projection_count :
      llvmVersionChoiceHelloProjectionCount model = 1;
    llvm_version_choice_success_projection_exact :
      llvmVersionChoiceHelloProjectionExact model = true;

    llvm_version_choice_success_chooser_count :
      llvmVersionChoiceChooserCount model = 1;
    llvm_version_choice_success_chooser_server_supported :
      llvmVersionChoiceChooserServerSupportedExact model = true;
    llvm_version_choice_success_chooser_hello_versions :
      llvmVersionChoiceChooserHelloVersionsExact model = true;
    llvm_version_choice_success_chooser_out :
      llvmVersionChoiceChooserSelectedOutExact model = true;
    llvm_version_choice_success_chooser_targets :
      llvmVersionChoiceChooserTargetsExact model = true;

    llvm_version_choice_success_unsupported_selector_count :
      llvmVersionChoiceUnsupportedSelectorCount model = 1;
    llvm_version_choice_success_unsupported_transport :
      llvmVersionChoiceUnsupportedTransportExact model = true;
    llvm_version_choice_success_version_binding_count :
      llvmVersionChoiceVersionPayloadBindingCount model = 1;
    llvm_version_choice_success_version_selector_count :
      llvmVersionChoiceVersionSelectorCount model = 1;
    llvm_version_choice_success_version_transport :
      llvmVersionChoiceVersionTransportExact model = true;
    llvm_version_choice_success_version_payload :
      llvmVersionChoiceVersionPayloadExact model = true;

    llvm_version_choice_success_client_offer :
      llvmVersionChoiceClientOfferExact model = true;
    llvm_version_choice_success_client_binding_count :
      llvmVersionChoiceClientPayloadBindingCount model = 1;
    llvm_version_choice_success_client_refinement_count :
      llvmVersionChoiceClientRefinementCount model = 1;
    llvm_version_choice_success_client_refinement_transport :
      llvmVersionChoiceClientRefinementTransportExact model = true;
    llvm_version_choice_success_client_refinement_payload :
      llvmVersionChoiceClientRefinementPayloadExact model = true;
    llvm_version_choice_success_client_refinement_targets :
      llvmVersionChoiceClientRefinementTargetsExact model = true;

    llvm_version_choice_success_wire_unsupported :
      llvmVersionChoiceWireUnsupported00 model = true;
    llvm_version_choice_success_wire_version :
      llvmVersionChoiceWireVersion01U16BE model = true;
    llvm_version_choice_success_outer_framing_undefined :
      llvmVersionChoiceOuterFramingDefined model = false;

    llvm_version_choice_success_no_poison :
      llvmVersionChoiceUnloweredPoisonPresent model = false;
    llvm_version_choice_success_no_generic_call :
      llvmVersionChoiceGenericVersionCallPresent model = false;
    llvm_version_choice_success_no_ambient_supported :
      llvmVersionChoiceAmbientSupportedLookupPresent model = false;
    llvm_version_choice_success_no_ambient_selected :
      llvmVersionChoiceAmbientSelectedLookupPresent model = false;
    llvm_version_choice_success_no_ambient_transport :
      llvmVersionChoiceAmbientTransportLookupPresent model = false;

    llvm_version_choice_success_provider_semantics_external :
      llvmVersionChoiceProviderSetSemanticsProved model = false;
    llvm_version_choice_success_transport_association_external :
      llvmVersionChoiceTransportOfferedAssociationProved model = false;
    llvm_version_choice_success_io_external :
      llvmVersionChoiceConcreteIOProved model = false;
    llvm_version_choice_success_malformed_external :
      llvmVersionChoiceMalformedTerminationProved model = false;
    llvm_version_choice_success_write_external :
      llvmVersionChoiceWriteSuccessProved model = false;
    llvm_version_choice_success_llvm_external :
      llvmVersionChoiceLLVMImplementationCorrectnessProved model = false;
    llvm_version_choice_success_native_external :
      llvmVersionChoiceNativeExecutionProved model = false
  }.

Theorem verified_llvm_version_choice_reuses_systems_and_payload_cancel_authority :
  forall model,
    LLVMVersionSessionChoiceVerificationSuccess model ->
    SystemsVersionChoiceOperandsVerificationSuccess
      (llvmVersionChoiceSystems model) /\
    PayloadCancelChoiceLLVMVerificationSuccess
      (llvmVersionChoicePayloadCancelPredecessor model).
Proof.
  intros model H; split.
  - exact (llvm_version_choice_success_systems model H).
  - exact (llvm_version_choice_success_payload_cancel model H).
Qed.

Theorem verified_llvm_version_choice_preserves_exact_target_and_projection :
  forall model,
    LLVMVersionSessionChoiceVerificationSuccess model ->
    llvmVersionChoiceTargetExact model = true /\
    llvmVersionChoiceDataLayoutExact model = true /\
    llvmVersionChoiceABIProfileExact model = true /\
    llvmVersionChoiceServerSupportedParameterExact model = true /\
    llvmVersionChoiceHelloProjectionCount model = 1 /\
    llvmVersionChoiceHelloProjectionExact model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_version_choice_success_target model H).
  - exact (llvm_version_choice_success_layout model H).
  - exact (llvm_version_choice_success_abi_profile model H).
  - exact (llvm_version_choice_success_server_supported_parameter model H).
  - exact (llvm_version_choice_success_projection_count model H).
  - exact (llvm_version_choice_success_projection_exact model H).
Qed.

Theorem verified_llvm_version_choice_lowers_exact_chooser :
  forall model,
    LLVMVersionSessionChoiceVerificationSuccess model ->
    llvmVersionChoiceChooserCount model = 1 /\
    llvmVersionChoiceChooserServerSupportedExact model = true /\
    llvmVersionChoiceChooserHelloVersionsExact model = true /\
    llvmVersionChoiceChooserSelectedOutExact model = true /\
    llvmVersionChoiceChooserTargetsExact model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_version_choice_success_chooser_count model H).
  - exact (llvm_version_choice_success_chooser_server_supported model H).
  - exact (llvm_version_choice_success_chooser_hello_versions model H).
  - exact (llvm_version_choice_success_chooser_out model H).
  - exact (llvm_version_choice_success_chooser_targets model H).
Qed.

Theorem verified_llvm_version_choice_lowers_exact_server_selectors :
  forall model,
    LLVMVersionSessionChoiceVerificationSuccess model ->
    llvmVersionChoiceUnsupportedSelectorCount model = 1 /\
    llvmVersionChoiceUnsupportedTransportExact model = true /\
    llvmVersionChoiceVersionPayloadBindingCount model = 1 /\
    llvmVersionChoiceVersionSelectorCount model = 1 /\
    llvmVersionChoiceVersionTransportExact model = true /\
    llvmVersionChoiceVersionPayloadExact model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_version_choice_success_unsupported_selector_count model H).
  - exact (llvm_version_choice_success_unsupported_transport model H).
  - exact (llvm_version_choice_success_version_binding_count model H).
  - exact (llvm_version_choice_success_version_selector_count model H).
  - exact (llvm_version_choice_success_version_transport model H).
  - exact (llvm_version_choice_success_version_payload model H).
Qed.

Theorem verified_llvm_version_choice_lowers_exact_client_offer_and_refinement :
  forall model,
    LLVMVersionSessionChoiceVerificationSuccess model ->
    llvmVersionChoiceClientOfferExact model = true /\
    llvmVersionChoiceClientPayloadBindingCount model = 1 /\
    llvmVersionChoiceClientRefinementCount model = 1 /\
    llvmVersionChoiceClientRefinementTransportExact model = true /\
    llvmVersionChoiceClientRefinementPayloadExact model = true /\
    llvmVersionChoiceClientRefinementTargetsExact model = true.
Proof.
  intros model H; repeat split.
  - exact (llvm_version_choice_success_client_offer model H).
  - exact (llvm_version_choice_success_client_binding_count model H).
  - exact (llvm_version_choice_success_client_refinement_count model H).
  - exact (llvm_version_choice_success_client_refinement_transport model H).
  - exact (llvm_version_choice_success_client_refinement_payload model H).
  - exact (llvm_version_choice_success_client_refinement_targets model H).
Qed.

Theorem verified_llvm_version_choice_binds_wire_profile_without_ambient_or_generic_state :
  forall model,
    LLVMVersionSessionChoiceVerificationSuccess model ->
    llvmVersionChoiceWireUnsupported00 model = true /\
    llvmVersionChoiceWireVersion01U16BE model = true /\
    llvmVersionChoiceOuterFramingDefined model = false /\
    llvmVersionChoiceUnloweredPoisonPresent model = false /\
    llvmVersionChoiceGenericVersionCallPresent model = false /\
    llvmVersionChoiceAmbientSupportedLookupPresent model = false /\
    llvmVersionChoiceAmbientSelectedLookupPresent model = false /\
    llvmVersionChoiceAmbientTransportLookupPresent model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_version_choice_success_wire_unsupported model H).
  - exact (llvm_version_choice_success_wire_version model H).
  - exact (llvm_version_choice_success_outer_framing_undefined model H).
  - exact (llvm_version_choice_success_no_poison model H).
  - exact (llvm_version_choice_success_no_generic_call model H).
  - exact (llvm_version_choice_success_no_ambient_supported model H).
  - exact (llvm_version_choice_success_no_ambient_selected model H).
  - exact (llvm_version_choice_success_no_ambient_transport model H).
Qed.

Theorem verified_llvm_version_choice_keeps_operational_gates_external :
  forall model,
    LLVMVersionSessionChoiceVerificationSuccess model ->
    llvmVersionChoiceProviderSetSemanticsProved model = false /\
    llvmVersionChoiceTransportOfferedAssociationProved model = false /\
    llvmVersionChoiceConcreteIOProved model = false /\
    llvmVersionChoiceMalformedTerminationProved model = false /\
    llvmVersionChoiceWriteSuccessProved model = false /\
    llvmVersionChoiceLLVMImplementationCorrectnessProved model = false /\
    llvmVersionChoiceNativeExecutionProved model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_version_choice_success_provider_semantics_external model H).
  - exact (llvm_version_choice_success_transport_association_external model H).
  - exact (llvm_version_choice_success_io_external model H).
  - exact (llvm_version_choice_success_malformed_external model H).
  - exact (llvm_version_choice_success_write_external model H).
  - exact (llvm_version_choice_success_llvm_external model H).
  - exact (llvm_version_choice_success_native_external model H).
Qed.

Theorem llvm_version_choice_chooser_or_selector_drift_is_rejected :
  forall model,
    llvmVersionChoiceChooserCount model <> 1 \/
    llvmVersionChoiceChooserServerSupportedExact model = false \/
    llvmVersionChoiceChooserHelloVersionsExact model = false \/
    llvmVersionChoiceChooserSelectedOutExact model = false \/
    llvmVersionChoiceUnsupportedSelectorCount model <> 1 \/
    llvmVersionChoiceVersionPayloadBindingCount model <> 1 \/
    llvmVersionChoiceVersionSelectorCount model <> 1 ->
    ~ LLVMVersionSessionChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hcc | [Hc0 | [Hc1 | [Hco | [Hus | [Hvb | Hvs]]]]]].
  - apply Hcc. exact (llvm_version_choice_success_chooser_count model H).
  - rewrite (llvm_version_choice_success_chooser_server_supported model H) in Hc0. discriminate.
  - rewrite (llvm_version_choice_success_chooser_hello_versions model H) in Hc1. discriminate.
  - rewrite (llvm_version_choice_success_chooser_out model H) in Hco. discriminate.
  - apply Hus. exact (llvm_version_choice_success_unsupported_selector_count model H).
  - apply Hvb. exact (llvm_version_choice_success_version_binding_count model H).
  - apply Hvs. exact (llvm_version_choice_success_version_selector_count model H).
Qed.

Theorem llvm_version_choice_client_ambient_or_gate_conflation_is_rejected :
  forall model,
    llvmVersionChoiceClientPayloadBindingCount model <> 1 \/
    llvmVersionChoiceClientRefinementCount model <> 1 \/
    llvmVersionChoiceClientRefinementTransportExact model = false \/
    llvmVersionChoiceClientRefinementPayloadExact model = false \/
    llvmVersionChoiceUnloweredPoisonPresent model = true \/
    llvmVersionChoiceGenericVersionCallPresent model = true \/
    llvmVersionChoiceAmbientSupportedLookupPresent model = true \/
    llvmVersionChoiceAmbientSelectedLookupPresent model = true \/
    llvmVersionChoiceAmbientTransportLookupPresent model = true \/
    llvmVersionChoiceProviderSetSemanticsProved model = true \/
    llvmVersionChoiceNativeExecutionProved model = true ->
    ~ LLVMVersionSessionChoiceVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hcb | [Hcr | [Hcrt | [Hcrp | [Hpoison | [Hgeneric | [Has | [Hav | [Hat | [Hprovider | Hnative]]]]]]]]]].
  - apply Hcb. exact (llvm_version_choice_success_client_binding_count model H).
  - apply Hcr. exact (llvm_version_choice_success_client_refinement_count model H).
  - rewrite (llvm_version_choice_success_client_refinement_transport model H) in Hcrt. discriminate.
  - rewrite (llvm_version_choice_success_client_refinement_payload model H) in Hcrp. discriminate.
  - rewrite (llvm_version_choice_success_no_poison model H) in Hpoison. discriminate.
  - rewrite (llvm_version_choice_success_no_generic_call model H) in Hgeneric. discriminate.
  - rewrite (llvm_version_choice_success_no_ambient_supported model H) in Has. discriminate.
  - rewrite (llvm_version_choice_success_no_ambient_selected model H) in Hav. discriminate.
  - rewrite (llvm_version_choice_success_no_ambient_transport model H) in Hat. discriminate.
  - rewrite (llvm_version_choice_success_provider_semantics_external model H) in Hprovider. discriminate.
  - rewrite (llvm_version_choice_success_native_external model H) in Hnative. discriminate.
Qed.
