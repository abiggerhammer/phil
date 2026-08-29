From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.
Import ListNotations.

(*
  PHIL-PROT-MSG-001 — exact protocol Message admissibility and the Phase 1
  no-remote-delegation boundary.

  The proof is representation-neutral.  It separates semantic-shape competence
  from hard Core type exclusions and from later ownership transfer.  Concrete
  Ty/SemanticForm/Text representation and Haskell traversal correspondence
  remain explicit implementation boundaries.
*)

Inductive MessageShape : Type :=
| MessageAdmittedLeaf : nat -> MessageShape
| MessageAggregate : list MessageShape -> MessageShape
| MessageScopedView : nat -> MessageShape
| MessageLiveEndpoint : MessageShape
| MessageLiveAuthority : nat -> MessageShape.

Fixpoint shapeAdmissible (shape : MessageShape) : bool :=
  match shape with
  | MessageAdmittedLeaf _ => true
  | MessageAggregate fields => forallb shapeAdmissible fields
  | MessageScopedView _ => false
  | MessageLiveEndpoint => false
  | MessageLiveAuthority _ => false
  end.

Theorem scoped_view_is_not_message :
  forall detail,
    shapeAdmissible (MessageScopedView detail) = false.
Proof.
  reflexivity.
Qed.

Theorem live_authority_is_not_message :
  forall authority,
    shapeAdmissible (MessageLiveAuthority authority) = false.
Proof.
  reflexivity.
Qed.

Theorem live_endpoint_shape_is_not_message :
  shapeAdmissible MessageLiveEndpoint = false.
Proof.
  reflexivity.
Qed.

Theorem aggregate_shape_admissibility_reaches_every_child :
  forall fields child,
    In child fields ->
    shapeAdmissible (MessageAggregate fields) = true ->
    shapeAdmissible child = true.
Proof.
  intros fields child Hin Haggregate.
  simpl in Haggregate.
  apply forallb_forall in Haggregate.
  apply Haggregate.
  exact Hin.
Qed.

Theorem aggregate_cannot_launder_forbidden_shape :
  forall fields child,
    In child fields ->
    shapeAdmissible child = false ->
    shapeAdmissible (MessageAggregate fields) = false.
Proof.
  intros fields child Hin Hforbidden.
  destruct (shapeAdmissible (MessageAggregate fields)) eqn:Haggregate.
  - pose proof
      (aggregate_shape_admissibility_reaches_every_child
        fields child Hin Haggregate) as Hchild.
    rewrite Hforbidden in Hchild.
    discriminate.
  - reflexivity.
Qed.

Inductive MessageType : Type :=
| MessageUnit : MessageType
| MessageBool : MessageType
| MessageUInt : nat -> MessageType
| MessageOpaque : nat -> MessageType
| MessageBytes : MessageType
| MessageEndpoint : MessageType
| MessagePendingReceive : MessageType
| MessageProduct : list MessageType -> MessageType
| MessageRefined : MessageType -> MessageType
| MessageOther : nat -> MessageType.

(*
  Hard Core exclusions are a second independent fail-closed layer.  Endpoint
  and internal pending-receive state reject even if an external semantic-shape
  classifier incorrectly labels them as admitted leaves.
*)
Fixpoint hardTypeAdmissible (ty : MessageType) : bool :=
  match ty with
  | MessageEndpoint => false
  | MessagePendingReceive => false
  | MessageProduct elements => forallb hardTypeAdmissible elements
  | MessageRefined inner => hardTypeAdmissible inner
  | _ => true
  end.

Theorem direct_endpoint_type_rejects :
  hardTypeAdmissible MessageEndpoint = false.
Proof.
  reflexivity.
Qed.

Theorem pending_receive_type_rejects :
  hardTypeAdmissible MessagePendingReceive = false.
Proof.
  reflexivity.
Qed.

Theorem product_hard_type_admissibility_reaches_every_child :
  forall elements child,
    In child elements ->
    hardTypeAdmissible (MessageProduct elements) = true ->
    hardTypeAdmissible child = true.
Proof.
  intros elements child Hin Hproduct.
  simpl in Hproduct.
  apply forallb_forall in Hproduct.
  apply Hproduct.
  exact Hin.
Qed.

Theorem product_cannot_launder_endpoint_type :
  forall elements,
    In MessageEndpoint elements ->
    hardTypeAdmissible (MessageProduct elements) = false.
Proof.
  intros elements Hin.
  destruct (hardTypeAdmissible (MessageProduct elements)) eqn:Hproduct.
  - pose proof
      (product_hard_type_admissibility_reaches_every_child
        elements MessageEndpoint Hin Hproduct) as Hendpoint.
    simpl in Hendpoint.
    discriminate.
  - reflexivity.
Qed.

Theorem refined_endpoint_type_rejects :
  hardTypeAdmissible (MessageRefined MessageEndpoint) = false.
Proof.
  reflexivity.
Qed.

(* Bare concrete Message positions use a deliberately small intrinsic subset. *)
Fixpoint intrinsicMessageType (ty : MessageType) : bool :=
  match ty with
  | MessageUnit => true
  | MessageBool => true
  | MessageUInt _ => true
  | MessageProduct elements => forallb intrinsicMessageType elements
  | MessageRefined inner => intrinsicMessageType inner
  | _ => false
  end.

Theorem intrinsic_uint_is_message :
  forall width,
    intrinsicMessageType (MessageUInt width) = true.
Proof.
  reflexivity.
Qed.

Theorem opaque_concrete_requires_explicit_contract :
  forall identity,
    intrinsicMessageType (MessageOpaque identity) = false.
Proof.
  reflexivity.
Qed.

Theorem endpoint_concrete_is_not_intrinsic :
  intrinsicMessageType MessageEndpoint = false.
Proof.
  reflexivity.
Qed.

Theorem intrinsic_product_requires_every_child_intrinsic :
  forall elements child,
    In child elements ->
    intrinsicMessageType (MessageProduct elements) = true ->
    intrinsicMessageType child = true.
Proof.
  intros elements child Hin Hproduct.
  simpl in Hproduct.
  apply forallb_forall in Hproduct.
  apply Hproduct.
  exact Hin.
Qed.

Record BoundaryMessageContract : Type := mkBoundaryMessageContract {
  messageContractRevision : nat;
  messageContractType : MessageType;
  messageContractSemantics : nat;
  messageContractShape : MessageShape
}.

Definition MessageContractAccepted
  (actualType : MessageType)
  (actualSemantics : nat)
  (contract : BoundaryMessageContract) : Prop :=
  messageContractRevision contract <> 0 /\
  messageContractType contract = actualType /\
  messageContractSemantics contract = actualSemantics /\
  shapeAdmissible (messageContractShape contract) = true /\
  hardTypeAdmissible actualType = true.

Theorem accepted_message_contract_has_nonempty_revision :
  forall actualType actualSemantics contract,
    MessageContractAccepted actualType actualSemantics contract ->
    messageContractRevision contract <> 0.
Proof.
  intros actualType actualSemantics contract Haccepted.
  exact (proj1 Haccepted).
Qed.

Theorem accepted_message_contract_is_tied_to_exact_type :
  forall actualType actualSemantics contract,
    MessageContractAccepted actualType actualSemantics contract ->
    messageContractType contract = actualType.
Proof.
  intros actualType actualSemantics contract Haccepted.
  destruct Haccepted as [_ [Htype _]].
  exact Htype.
Qed.

Theorem accepted_message_contract_is_tied_to_exact_semantics :
  forall actualType actualSemantics contract,
    MessageContractAccepted actualType actualSemantics contract ->
    messageContractSemantics contract = actualSemantics.
Proof.
  intros actualType actualSemantics contract Haccepted.
  destruct Haccepted as [_ [_ [Hsemantics _]]].
  exact Hsemantics.
Qed.

Theorem empty_revision_rejects :
  forall actualType actualSemantics contractType contractSemantics shape,
    ~ MessageContractAccepted
        actualType actualSemantics
        (mkBoundaryMessageContract 0 contractType contractSemantics shape).
Proof.
  intros actualType actualSemantics contractType contractSemantics shape Haccepted.
  destruct Haccepted as [Hrevision _].
  apply Hrevision.
  reflexivity.
Qed.

Theorem contract_type_mismatch_rejects :
  forall actualType actualSemantics contract,
    messageContractType contract <> actualType ->
    ~ MessageContractAccepted actualType actualSemantics contract.
Proof.
  intros actualType actualSemantics contract Hmismatch Haccepted.
  apply Hmismatch.
  apply accepted_message_contract_is_tied_to_exact_type with
    (actualSemantics := actualSemantics).
  exact Haccepted.
Qed.

Theorem contract_semantics_mismatch_rejects :
  forall actualType actualSemantics contract,
    messageContractSemantics contract <> actualSemantics ->
    ~ MessageContractAccepted actualType actualSemantics contract.
Proof.
  intros actualType actualSemantics contract Hmismatch Haccepted.
  apply Hmismatch.
  apply accepted_message_contract_is_tied_to_exact_semantics with
    (actualType := actualType).
  exact Haccepted.
Qed.

Theorem scoped_view_contract_rejects :
  forall actualType actualSemantics revision contractType contractSemantics detail,
    ~ MessageContractAccepted
        actualType actualSemantics
        (mkBoundaryMessageContract
          revision contractType contractSemantics (MessageScopedView detail)).
Proof.
  intros actualType actualSemantics revision contractType contractSemantics detail Haccepted.
  destruct Haccepted as [_ [_ [_ [Hshape _]]]].
  simpl in Hshape.
  discriminate.
Qed.

Theorem live_authority_contract_rejects :
  forall actualType actualSemantics revision contractType contractSemantics authority,
    ~ MessageContractAccepted
        actualType actualSemantics
        (mkBoundaryMessageContract
          revision contractType contractSemantics (MessageLiveAuthority authority)).
Proof.
  intros actualType actualSemantics revision contractType contractSemantics authority Haccepted.
  destruct Haccepted as [_ [_ [_ [Hshape _]]]].
  simpl in Hshape.
  discriminate.
Qed.

Theorem endpoint_type_rejects_even_if_shape_is_admitted_leaf :
  forall actualSemantics revision contractSemantics label,
    ~ MessageContractAccepted
        MessageEndpoint actualSemantics
        (mkBoundaryMessageContract
          revision MessageEndpoint contractSemantics (MessageAdmittedLeaf label)).
Proof.
  intros actualSemantics revision contractSemantics label Haccepted.
  destruct Haccepted as [_ [_ [_ [_ Hhard]]]].
  simpl in Hhard.
  discriminate.
Qed.

Theorem aggregate_shape_contract_cannot_launder_live_authority :
  forall actualType actualSemantics revision contractSemantics fields authority,
    In (MessageLiveAuthority authority) fields ->
    ~ MessageContractAccepted
        actualType actualSemantics
        (mkBoundaryMessageContract
          revision actualType contractSemantics (MessageAggregate fields)).
Proof.
  intros actualType actualSemantics revision contractSemantics fields authority Hin Haccepted.
  destruct Haccepted as [_ [_ [_ [Hshape _]]]].
  pose proof
    (aggregate_shape_admissibility_reaches_every_child
      fields (MessageLiveAuthority authority) Hin Hshape) as Hauthority.
  simpl in Hauthority.
  discriminate.
Qed.

Theorem product_type_contract_cannot_launder_endpoint :
  forall actualSemantics revision contractSemantics shape elements,
    In MessageEndpoint elements ->
    ~ MessageContractAccepted
        (MessageProduct elements) actualSemantics
        (mkBoundaryMessageContract
          revision (MessageProduct elements) contractSemantics shape).
Proof.
  intros actualSemantics revision contractSemantics shape elements Hin Haccepted.
  destruct Haccepted as [_ [_ [_ [_ Hhard]]]].
  pose proof
    (product_hard_type_admissibility_reaches_every_child
      elements MessageEndpoint Hin Hhard) as Hendpoint.
  simpl in Hendpoint.
  discriminate.
Qed.

(*
  Successful parameterized protocol instantiation must carry Message competence
  before any generic-discharge result can contribute to success.
*)
Definition ParameterizedProtocolAccepted
  (actualType : MessageType)
  (actualSemantics : nat)
  (contract : BoundaryMessageContract)
  (genericDischargeAccepted : bool) : Prop :=
  MessageContractAccepted actualType actualSemantics contract /\
  genericDischargeAccepted = true.

Theorem successful_parameterized_protocol_requires_message_admission :
  forall actualType actualSemantics contract genericDischargeAccepted,
    ParameterizedProtocolAccepted
      actualType actualSemantics contract genericDischargeAccepted ->
    MessageContractAccepted actualType actualSemantics contract.
Proof.
  intros actualType actualSemantics contract genericDischargeAccepted Haccepted.
  exact (proj1 Haccepted).
Qed.

(*
  Restricted-owner transfer is downstream and independent.  Message admission
  cannot manufacture transfer authority; successful transfer requires both.
*)
Definition RestrictedMessageTransferAccepted
  (actualType : MessageType)
  (actualSemantics : nat)
  (contract : BoundaryMessageContract)
  (ownershipTransferAccepted : bool) : Prop :=
  MessageContractAccepted actualType actualSemantics contract /\
  ownershipTransferAccepted = true.

Theorem successful_restricted_transfer_requires_message_admission :
  forall actualType actualSemantics contract ownershipTransferAccepted,
    RestrictedMessageTransferAccepted
      actualType actualSemantics contract ownershipTransferAccepted ->
    MessageContractAccepted actualType actualSemantics contract.
Proof.
  intros actualType actualSemantics contract ownershipTransferAccepted Haccepted.
  exact (proj1 Haccepted).
Qed.

Theorem successful_restricted_transfer_requires_separate_ownership_authority :
  forall actualType actualSemantics contract ownershipTransferAccepted,
    RestrictedMessageTransferAccepted
      actualType actualSemantics contract ownershipTransferAccepted ->
    ownershipTransferAccepted = true.
Proof.
  intros actualType actualSemantics contract ownershipTransferAccepted Haccepted.
  exact (proj2 Haccepted).
Qed.

Theorem message_admission_alone_cannot_authorize_failed_transfer :
  forall actualType actualSemantics contract,
    MessageContractAccepted actualType actualSemantics contract ->
    ~ RestrictedMessageTransferAccepted
        actualType actualSemantics contract false.
Proof.
  intros actualType actualSemantics contract Hmessage Htransfer.
  destruct Htransfer as [_ Hownership].
  discriminate.
Qed.
