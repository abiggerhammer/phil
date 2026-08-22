From Phil.Systems Require Import ScalarDataflow PayloadCancelChoice.
From Phil.LLVM Require Import FinalResponseReceive RuntimeSymbolIdentity.

(*
  PHIL-LLVM-PAYLOAD-CANCEL-001 — normalized proof model for
  phil-runtime/phase0/payload-cancel-choice-v1.

  The model preserves exact client/server transport operands, canonical
  payload=0x01 and cancel=0x00 selector constants, the exact server
  true->payload / false->cancel continuation mapping, absence of protocol
  payload values, absence of generic/ambient choice state, and preservation of
  proof-bound final-response receive authority. Reserved octets and early EOF
  have no invented Phil CFG edge; provider non-return behavior remains an
  external runtime gate rather than a Rocq theorem.
*)

Definition PayloadCancelOperandId := nat.
Definition PayloadCancelLLVMBlockId := nat.

Record PayloadCancelChoiceLLVMModel : Type := mkPayloadCancelChoiceLLVMModel {
  llvmPayloadCancelSystems : SystemsPayloadCancelChoiceModel;
  llvmPayloadCancelFinalPredecessor : FinalResponseReceiveLLVMModel;
  llvmPayloadCancelRuntimeSymbols : RuntimeSymbolModel;

  llvmPayloadCancelTransportSSAFor : ValueId -> PayloadCancelOperandId;
  llvmPayloadCancelBlockSSAFor : PayloadCancelBlockId -> PayloadCancelLLVMBlockId;

  llvmPayloadCancelExpectedClientTransport : PayloadCancelOperandId;
  llvmPayloadCancelActualPayloadTransport : PayloadCancelOperandId;
  llvmPayloadCancelActualCancelTransport : PayloadCancelOperandId;
  llvmPayloadCancelExpectedServerTransport : PayloadCancelOperandId;
  llvmPayloadCancelActualServerTransport : PayloadCancelOperandId;

  llvmPayloadCancelPayloadCode : nat;
  llvmPayloadCancelCancelCode : nat;
  llvmPayloadCancelPayloadSelectCount : nat;
  llvmPayloadCancelCancelSelectCount : nat;
  llvmPayloadCancelUsesPhysicalSelector : bool;
  llvmPayloadCancelSelectorArity : nat;

  llvmPayloadCancelReceiveCount : nat;
  llvmPayloadCancelUsesPhysicalReceiver : bool;
  llvmPayloadCancelReceiverArity : nat;
  llvmPayloadCancelReceiverReturnsI1 : bool;
  llvmPayloadCancelTrueMeansPayload : bool;
  llvmPayloadCancelFalseMeansCancel : bool;

  llvmPayloadCancelExpectedPayloadTarget : PayloadCancelLLVMBlockId;
  llvmPayloadCancelActualPayloadTarget : PayloadCancelLLVMBlockId;
  llvmPayloadCancelExpectedCancelTarget : PayloadCancelLLVMBlockId;
  llvmPayloadCancelActualCancelTarget : PayloadCancelLLVMBlockId;

  llvmPayloadCancelPhysicalChoicePayloadPresent : bool;
  llvmPayloadCancelGenericSelectPresent : bool;
  llvmPayloadCancelGenericReceivePresent : bool;
  llvmPayloadCancelAmbientChoiceStatePresent : bool;
  llvmPayloadCancelAmbientTransportStatePresent : bool;
  llvmPayloadCancelMalformedCFGBranchPresent : bool;
  llvmPayloadCancelUnauthorizedPointerStrengtheningPresent : bool
}.

Record PayloadCancelChoiceLLVMVerificationSuccess
  (model : PayloadCancelChoiceLLVMModel) : Prop :=
  mkPayloadCancelChoiceLLVMVerificationSuccess {
    llvm_payload_cancel_success_systems :
      SystemsPayloadCancelChoiceVerificationSuccess
        (llvmPayloadCancelSystems model);
    llvm_payload_cancel_success_final_predecessor :
      FinalResponseReceiveLLVMVerificationSuccess
        (llvmPayloadCancelFinalPredecessor model);
    llvm_payload_cancel_success_runtime_symbols :
      RuntimeSymbolVerificationSuccess
        (llvmPayloadCancelRuntimeSymbols model);
    llvm_payload_cancel_success_final_systems_align :
      llvmFinalSystems (llvmPayloadCancelFinalPredecessor model) =
        systemsPayloadCancelFinalPredecessor (llvmPayloadCancelSystems model);

    llvm_payload_cancel_success_expected_client_transport :
      llvmPayloadCancelExpectedClientTransport model =
        llvmPayloadCancelTransportSSAFor model
          (systemsPayloadCancelWitnessClientTransport
            (llvmPayloadCancelSystems model));
    llvm_payload_cancel_success_payload_transport :
      llvmPayloadCancelActualPayloadTransport model =
        llvmPayloadCancelExpectedClientTransport model;
    llvm_payload_cancel_success_cancel_transport :
      llvmPayloadCancelActualCancelTransport model =
        llvmPayloadCancelExpectedClientTransport model;
    llvm_payload_cancel_success_expected_server_transport :
      llvmPayloadCancelExpectedServerTransport model =
        llvmPayloadCancelTransportSSAFor model
          (systemsPayloadCancelWitnessServerTransport
            (llvmPayloadCancelSystems model));
    llvm_payload_cancel_success_server_transport :
      llvmPayloadCancelActualServerTransport model =
        llvmPayloadCancelExpectedServerTransport model;

    llvm_payload_cancel_success_payload_code :
      llvmPayloadCancelPayloadCode model = 1;
    llvm_payload_cancel_success_cancel_code :
      llvmPayloadCancelCancelCode model = 0;
    llvm_payload_cancel_success_payload_select_once :
      llvmPayloadCancelPayloadSelectCount model = 1;
    llvm_payload_cancel_success_cancel_select_once :
      llvmPayloadCancelCancelSelectCount model = 1;
    llvm_payload_cancel_success_physical_selector :
      llvmPayloadCancelUsesPhysicalSelector model = true;
    llvm_payload_cancel_success_selector_arity :
      llvmPayloadCancelSelectorArity model = 2;

    llvm_payload_cancel_success_receive_once :
      llvmPayloadCancelReceiveCount model = 1;
    llvm_payload_cancel_success_physical_receiver :
      llvmPayloadCancelUsesPhysicalReceiver model = true;
    llvm_payload_cancel_success_receiver_arity :
      llvmPayloadCancelReceiverArity model = 1;
    llvm_payload_cancel_success_receiver_i1 :
      llvmPayloadCancelReceiverReturnsI1 model = true;
    llvm_payload_cancel_success_true_payload :
      llvmPayloadCancelTrueMeansPayload model = true;
    llvm_payload_cancel_success_false_cancel :
      llvmPayloadCancelFalseMeansCancel model = true;

    llvm_payload_cancel_success_expected_payload_target :
      llvmPayloadCancelExpectedPayloadTarget model =
        llvmPayloadCancelBlockSSAFor model
          (systemsPayloadCancelWitnessPayloadTarget
            (llvmPayloadCancelSystems model));
    llvm_payload_cancel_success_payload_target :
      llvmPayloadCancelActualPayloadTarget model =
        llvmPayloadCancelExpectedPayloadTarget model;
    llvm_payload_cancel_success_expected_cancel_target :
      llvmPayloadCancelExpectedCancelTarget model =
        llvmPayloadCancelBlockSSAFor model
          (systemsPayloadCancelWitnessCancelTarget
            (llvmPayloadCancelSystems model));
    llvm_payload_cancel_success_cancel_target :
      llvmPayloadCancelActualCancelTarget model =
        llvmPayloadCancelExpectedCancelTarget model;

    llvm_payload_cancel_success_no_choice_payload :
      llvmPayloadCancelPhysicalChoicePayloadPresent model = false;
    llvm_payload_cancel_success_no_generic_select :
      llvmPayloadCancelGenericSelectPresent model = false;
    llvm_payload_cancel_success_no_generic_receive :
      llvmPayloadCancelGenericReceivePresent model = false;
    llvm_payload_cancel_success_no_ambient_choice :
      llvmPayloadCancelAmbientChoiceStatePresent model = false;
    llvm_payload_cancel_success_no_ambient_transport :
      llvmPayloadCancelAmbientTransportStatePresent model = false;
    llvm_payload_cancel_success_no_malformed_branch :
      llvmPayloadCancelMalformedCFGBranchPresent model = false;
    llvm_payload_cancel_success_no_strengthening :
      llvmPayloadCancelUnauthorizedPointerStrengtheningPresent model = false
  }.

Theorem verified_llvm_payload_cancel_reuses_semantic_final_and_symbol_authority :
  forall model,
    PayloadCancelChoiceLLVMVerificationSuccess model ->
    SystemsPayloadCancelChoiceVerificationSuccess
      (llvmPayloadCancelSystems model) /\
    FinalResponseReceiveLLVMVerificationSuccess
      (llvmPayloadCancelFinalPredecessor model) /\
    RuntimeSymbolVerificationSuccess
      (llvmPayloadCancelRuntimeSymbols model) /\
    llvmFinalSystems (llvmPayloadCancelFinalPredecessor model) =
      systemsPayloadCancelFinalPredecessor (llvmPayloadCancelSystems model).
Proof.
  intros model H.
  split.
  - exact (llvm_payload_cancel_success_systems model H).
  - split.
    + exact (llvm_payload_cancel_success_final_predecessor model H).
    + split.
      * exact (llvm_payload_cancel_success_runtime_symbols model H).
      * exact (llvm_payload_cancel_success_final_systems_align model H).
Qed.

Theorem verified_llvm_payload_cancel_preserves_exact_transport_operands :
  forall model,
    PayloadCancelChoiceLLVMVerificationSuccess model ->
    llvmPayloadCancelActualPayloadTransport model =
      llvmPayloadCancelTransportSSAFor model
        (systemsPayloadCancelWitnessClientTransport
          (llvmPayloadCancelSystems model)) /\
    llvmPayloadCancelActualCancelTransport model =
      llvmPayloadCancelTransportSSAFor model
        (systemsPayloadCancelWitnessClientTransport
          (llvmPayloadCancelSystems model)) /\
    llvmPayloadCancelActualServerTransport model =
      llvmPayloadCancelTransportSSAFor model
        (systemsPayloadCancelWitnessServerTransport
          (llvmPayloadCancelSystems model)).
Proof.
  intros model H; repeat split.
  - rewrite (llvm_payload_cancel_success_payload_transport model H).
    exact (llvm_payload_cancel_success_expected_client_transport model H).
  - rewrite (llvm_payload_cancel_success_cancel_transport model H).
    exact (llvm_payload_cancel_success_expected_client_transport model H).
  - rewrite (llvm_payload_cancel_success_server_transport model H).
    exact (llvm_payload_cancel_success_expected_server_transport model H).
Qed.

Theorem verified_llvm_payload_cancel_uses_canonical_selectors :
  forall model,
    PayloadCancelChoiceLLVMVerificationSuccess model ->
    llvmPayloadCancelPayloadCode model = 1 /\
    llvmPayloadCancelCancelCode model = 0 /\
    llvmPayloadCancelPayloadSelectCount model = 1 /\
    llvmPayloadCancelCancelSelectCount model = 1 /\
    llvmPayloadCancelUsesPhysicalSelector model = true /\
    llvmPayloadCancelSelectorArity model = 2.
Proof.
  intros model H; repeat split.
  - exact (llvm_payload_cancel_success_payload_code model H).
  - exact (llvm_payload_cancel_success_cancel_code model H).
  - exact (llvm_payload_cancel_success_payload_select_once model H).
  - exact (llvm_payload_cancel_success_cancel_select_once model H).
  - exact (llvm_payload_cancel_success_physical_selector model H).
  - exact (llvm_payload_cancel_success_selector_arity model H).
Qed.

Theorem verified_llvm_payload_cancel_preserves_receiver_and_continuations :
  forall model,
    PayloadCancelChoiceLLVMVerificationSuccess model ->
    llvmPayloadCancelReceiveCount model = 1 /\
    llvmPayloadCancelUsesPhysicalReceiver model = true /\
    llvmPayloadCancelReceiverArity model = 1 /\
    llvmPayloadCancelReceiverReturnsI1 model = true /\
    llvmPayloadCancelTrueMeansPayload model = true /\
    llvmPayloadCancelFalseMeansCancel model = true /\
    llvmPayloadCancelActualPayloadTarget model =
      llvmPayloadCancelBlockSSAFor model
        (systemsPayloadCancelWitnessPayloadTarget
          (llvmPayloadCancelSystems model)) /\
    llvmPayloadCancelActualCancelTarget model =
      llvmPayloadCancelBlockSSAFor model
        (systemsPayloadCancelWitnessCancelTarget
          (llvmPayloadCancelSystems model)).
Proof.
  intros model H; repeat split.
  - exact (llvm_payload_cancel_success_receive_once model H).
  - exact (llvm_payload_cancel_success_physical_receiver model H).
  - exact (llvm_payload_cancel_success_receiver_arity model H).
  - exact (llvm_payload_cancel_success_receiver_i1 model H).
  - exact (llvm_payload_cancel_success_true_payload model H).
  - exact (llvm_payload_cancel_success_false_cancel model H).
  - rewrite (llvm_payload_cancel_success_payload_target model H).
    exact (llvm_payload_cancel_success_expected_payload_target model H).
  - rewrite (llvm_payload_cancel_success_cancel_target model H).
    exact (llvm_payload_cancel_success_expected_cancel_target model H).
Qed.

Theorem verified_llvm_payload_cancel_forbids_payload_ambient_generic_and_malformed_edges :
  forall model,
    PayloadCancelChoiceLLVMVerificationSuccess model ->
    llvmPayloadCancelPhysicalChoicePayloadPresent model = false /\
    llvmPayloadCancelGenericSelectPresent model = false /\
    llvmPayloadCancelGenericReceivePresent model = false /\
    llvmPayloadCancelAmbientChoiceStatePresent model = false /\
    llvmPayloadCancelAmbientTransportStatePresent model = false /\
    llvmPayloadCancelMalformedCFGBranchPresent model = false /\
    llvmPayloadCancelUnauthorizedPointerStrengtheningPresent model = false.
Proof.
  intros model H; repeat split.
  - exact (llvm_payload_cancel_success_no_choice_payload model H).
  - exact (llvm_payload_cancel_success_no_generic_select model H).
  - exact (llvm_payload_cancel_success_no_generic_receive model H).
  - exact (llvm_payload_cancel_success_no_ambient_choice model H).
  - exact (llvm_payload_cancel_success_no_ambient_transport model H).
  - exact (llvm_payload_cancel_success_no_malformed_branch model H).
  - exact (llvm_payload_cancel_success_no_strengthening model H).
Qed.

Theorem llvm_payload_cancel_transport_or_selector_drift_is_rejected :
  forall model,
    llvmPayloadCancelActualPayloadTransport model <>
      llvmPayloadCancelExpectedClientTransport model \/
    llvmPayloadCancelActualCancelTransport model <>
      llvmPayloadCancelExpectedClientTransport model \/
    llvmPayloadCancelActualServerTransport model <>
      llvmPayloadCancelExpectedServerTransport model \/
    llvmPayloadCancelPayloadCode model <> 1 \/
    llvmPayloadCancelCancelCode model <> 0 \/
    llvmPayloadCancelPayloadSelectCount model <> 1 \/
    llvmPayloadCancelCancelSelectCount model <> 1 \/
    llvmPayloadCancelUsesPhysicalSelector model = false \/
    llvmPayloadCancelSelectorArity model <> 2 ->
    ~ PayloadCancelChoiceLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hpt | [Hct | [Hst | [Hpc | [Hcc | [Hps | [Hcs | [Hphys | Har]]]]]]]].
  - apply Hpt. exact (llvm_payload_cancel_success_payload_transport model H).
  - apply Hct. exact (llvm_payload_cancel_success_cancel_transport model H).
  - apply Hst. exact (llvm_payload_cancel_success_server_transport model H).
  - apply Hpc. exact (llvm_payload_cancel_success_payload_code model H).
  - apply Hcc. exact (llvm_payload_cancel_success_cancel_code model H).
  - apply Hps. exact (llvm_payload_cancel_success_payload_select_once model H).
  - apply Hcs. exact (llvm_payload_cancel_success_cancel_select_once model H).
  - rewrite (llvm_payload_cancel_success_physical_selector model H) in Hphys. discriminate.
  - apply Har. exact (llvm_payload_cancel_success_selector_arity model H).
Qed.

Theorem llvm_payload_cancel_receiver_or_target_drift_is_rejected :
  forall model,
    llvmPayloadCancelReceiveCount model <> 1 \/
    llvmPayloadCancelUsesPhysicalReceiver model = false \/
    llvmPayloadCancelReceiverArity model <> 1 \/
    llvmPayloadCancelReceiverReturnsI1 model = false \/
    llvmPayloadCancelTrueMeansPayload model = false \/
    llvmPayloadCancelFalseMeansCancel model = false \/
    llvmPayloadCancelActualPayloadTarget model <>
      llvmPayloadCancelExpectedPayloadTarget model \/
    llvmPayloadCancelActualCancelTarget model <>
      llvmPayloadCancelExpectedCancelTarget model ->
    ~ PayloadCancelChoiceLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hrc | [Hphys | [Har | [Hi1 | [Htp | [Hfc | [Hpt | Hct]]]]]]].
  - apply Hrc. exact (llvm_payload_cancel_success_receive_once model H).
  - rewrite (llvm_payload_cancel_success_physical_receiver model H) in Hphys. discriminate.
  - apply Har. exact (llvm_payload_cancel_success_receiver_arity model H).
  - rewrite (llvm_payload_cancel_success_receiver_i1 model H) in Hi1. discriminate.
  - rewrite (llvm_payload_cancel_success_true_payload model H) in Htp. discriminate.
  - rewrite (llvm_payload_cancel_success_false_cancel model H) in Hfc. discriminate.
  - apply Hpt. exact (llvm_payload_cancel_success_payload_target model H).
  - apply Hct. exact (llvm_payload_cancel_success_cancel_target model H).
Qed.

Theorem llvm_payload_cancel_ambient_generic_payload_or_malformed_drift_is_rejected :
  forall model,
    llvmPayloadCancelPhysicalChoicePayloadPresent model = true \/
    llvmPayloadCancelGenericSelectPresent model = true \/
    llvmPayloadCancelGenericReceivePresent model = true \/
    llvmPayloadCancelAmbientChoiceStatePresent model = true \/
    llvmPayloadCancelAmbientTransportStatePresent model = true \/
    llvmPayloadCancelMalformedCFGBranchPresent model = true \/
    llvmPayloadCancelUnauthorizedPointerStrengtheningPresent model = true ->
    ~ PayloadCancelChoiceLLVMVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hp | [Hgs | [Hgr | [Hac | [Hat | [Hm | Hs]]]]]].
  - rewrite (llvm_payload_cancel_success_no_choice_payload model H) in Hp. discriminate.
  - rewrite (llvm_payload_cancel_success_no_generic_select model H) in Hgs. discriminate.
  - rewrite (llvm_payload_cancel_success_no_generic_receive model H) in Hgr. discriminate.
  - rewrite (llvm_payload_cancel_success_no_ambient_choice model H) in Hac. discriminate.
  - rewrite (llvm_payload_cancel_success_no_ambient_transport model H) in Hat. discriminate.
  - rewrite (llvm_payload_cancel_success_no_malformed_branch model H) in Hm. discriminate.
  - rewrite (llvm_payload_cancel_success_no_strengthening model H) in Hs. discriminate.
Qed.
