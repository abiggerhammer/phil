From Stdlib Require Import Lists.List.

Import ListNotations.

From Phil.Core Require Import Syntax.

(*
  PHIL-PROT-ID-001 — protocol instance / role / local-state identity.

  The concrete Haskell implementation represents protocol-instance revisions,
  role keys, occurrence names, and runtime/transport identifiers with Text and
  richer records.  This normalized model keeps only the semantic coordinates
  required by PROT-001/002/007:

  - a live endpoint contract is exact protocol instance + exact role + exact
    current local Session;
  - occurrence names are not part of the endpoint contract;
  - communication authority additionally requires the current local session
    calculus to admit the requested action;
  - coincident transport/runtime representation never repairs a semantic
    instance, role, or local-state mismatch.

  PHIL-SESSION-STEP-001 remains the authority for the resource effect of an
  admitted session transition.  Here [LocalActionAllowed] is intentionally an
  abstract premise: this theorem family proves that protocol identity gates
  cannot be bypassed or inferred from equal-looking local state or realization.
*)

Definition ProtocolInstanceRevision := nat.
Definition ProtocolRoleKey := nat.
Definition ProtocolOccurrenceName := nat.
Definition TransportIdentity := nat.
Definition RuntimeRepresentationIdentity := nat.

Parameter ProtocolAction : Type.
Parameter LocalActionAllowed : Session -> ProtocolAction -> Prop.

Record ProtocolEndpointContract : Type := {
  protocolContractInstance : ProtocolInstanceRevision;
  protocolContractRole : ProtocolRoleKey;
  protocolContractSession : Session
}.

Record ProtocolEndpointOccurrence : Type := {
  protocolOccurrenceName : ProtocolOccurrenceName;
  protocolOccurrenceContract : ProtocolEndpointContract
}.

Definition ContractMatches
  (expected actual : ProtocolEndpointContract) : Prop :=
  protocolContractInstance expected = protocolContractInstance actual /\
  protocolContractRole expected = protocolContractRole actual /\
  protocolContractSession expected = protocolContractSession actual.

Definition EndpointSubstitutable
  (expected actual : ProtocolEndpointOccurrence) : Prop :=
  ContractMatches
    (protocolOccurrenceContract expected)
    (protocolOccurrenceContract actual).

Definition EndpointJoinCompatible
  (first : ProtocolEndpointOccurrence)
  (rest : list ProtocolEndpointOccurrence) : Prop :=
  forall endpoint,
    In endpoint rest ->
    EndpointSubstitutable first endpoint.

Record ProtocolActionRequest : Type := {
  requestProtocolInstance : ProtocolInstanceRevision;
  requestProtocolRole : ProtocolRoleKey;
  requestProtocolAction : ProtocolAction
}.

Definition ProtocolActionAllowed
  (request : ProtocolActionRequest)
  (endpoint : ProtocolEndpointOccurrence) : Prop :=
  requestProtocolInstance request =
    protocolContractInstance (protocolOccurrenceContract endpoint) /\
  requestProtocolRole request =
    protocolContractRole (protocolOccurrenceContract endpoint) /\
  LocalActionAllowed
    (protocolContractSession (protocolOccurrenceContract endpoint))
    (requestProtocolAction request).

Record RealizedProtocolEndpoint : Type := {
  realizedProtocolContract : ProtocolEndpointContract;
  realizedTransportIdentity : TransportIdentity;
  realizedRuntimeRepresentation : RuntimeRepresentationIdentity
}.

Definition RuntimeCoincident
  (left right : RealizedProtocolEndpoint) : Prop :=
  realizedTransportIdentity left = realizedTransportIdentity right /\
  realizedRuntimeRepresentation left = realizedRuntimeRepresentation right.

Definition RealizationCorresponds
  (left right : RealizedProtocolEndpoint) : Prop :=
  ContractMatches
    (realizedProtocolContract left)
    (realizedProtocolContract right).

Theorem contract_matches_refl :
  forall contract,
    ContractMatches contract contract.
Proof.
  intros contract.
  unfold ContractMatches.
  repeat split; reflexivity.
Qed.

Theorem occurrence_name_is_not_contract_identity :
  forall leftName rightName contract,
    EndpointSubstitutable
      {| protocolOccurrenceName := leftName;
         protocolOccurrenceContract := contract |}
      {| protocolOccurrenceName := rightName;
         protocolOccurrenceContract := contract |}.
Proof.
  intros leftName rightName contract.
  unfold EndpointSubstitutable.
  simpl.
  apply contract_matches_refl.
Qed.

Theorem equal_local_session_does_not_merge_distinct_instances :
  forall left right,
    protocolContractSession left = protocolContractSession right ->
    protocolContractInstance left <> protocolContractInstance right ->
    ~ ContractMatches left right.
Proof.
  intros left right _ Hdifferent Hmatches.
  unfold ContractMatches in Hmatches.
  destruct Hmatches as [Hinstance _].
  apply Hdifferent.
  exact Hinstance.
Qed.

Theorem equal_local_session_does_not_erase_role_identity :
  forall left right,
    protocolContractSession left = protocolContractSession right ->
    protocolContractRole left <> protocolContractRole right ->
    ~ ContractMatches left right.
Proof.
  intros left right _ Hdifferent Hmatches.
  unfold ContractMatches in Hmatches.
  destruct Hmatches as [_ [Hrole _]].
  apply Hdifferent.
  exact Hrole.
Qed.

Theorem same_instance_and_role_still_require_exact_local_state :
  forall left right,
    protocolContractInstance left = protocolContractInstance right ->
    protocolContractRole left = protocolContractRole right ->
    protocolContractSession left <> protocolContractSession right ->
    ~ ContractMatches left right.
Proof.
  intros left right _ _ Hdifferent Hmatches.
  unfold ContractMatches in Hmatches.
  destruct Hmatches as [_ [_ Hsession]].
  apply Hdifferent.
  exact Hsession.
Qed.

Theorem join_requires_exact_contract_for_every_continuing_occurrence :
  forall first rest endpoint,
    EndpointJoinCompatible first rest ->
    In endpoint rest ->
    EndpointSubstitutable first endpoint.
Proof.
  intros first rest endpoint Hjoin Hin.
  apply Hjoin.
  exact Hin.
Qed.

Theorem cross_instance_endpoint_cannot_join :
  forall first rest endpoint,
    EndpointJoinCompatible first rest ->
    In endpoint rest ->
    protocolContractInstance (protocolOccurrenceContract first) <>
      protocolContractInstance (protocolOccurrenceContract endpoint) ->
    False.
Proof.
  intros first rest endpoint Hjoin Hin Hdifferent.
  pose proof
    (join_requires_exact_contract_for_every_continuing_occurrence
      first rest endpoint Hjoin Hin)
    as Hsubstitutable.
  unfold EndpointSubstitutable, ContractMatches in Hsubstitutable.
  destruct Hsubstitutable as [Hinstance _].
  apply Hdifferent.
  exact Hinstance.
Qed.

Theorem protocol_action_requires_exact_instance :
  forall request endpoint,
    ProtocolActionAllowed request endpoint ->
    requestProtocolInstance request =
      protocolContractInstance (protocolOccurrenceContract endpoint).
Proof.
  intros request endpoint Hallowed.
  unfold ProtocolActionAllowed in Hallowed.
  destruct Hallowed as [Hinstance _].
  exact Hinstance.
Qed.

Theorem protocol_action_requires_exact_role :
  forall request endpoint,
    ProtocolActionAllowed request endpoint ->
    requestProtocolRole request =
      protocolContractRole (protocolOccurrenceContract endpoint).
Proof.
  intros request endpoint Hallowed.
  unfold ProtocolActionAllowed in Hallowed.
  destruct Hallowed as [_ [Hrole _]].
  exact Hrole.
Qed.

Theorem protocol_action_requires_current_local_state_admission :
  forall request endpoint,
    ProtocolActionAllowed request endpoint ->
    LocalActionAllowed
      (protocolContractSession (protocolOccurrenceContract endpoint))
      (requestProtocolAction request).
Proof.
  intros request endpoint Hallowed.
  unfold ProtocolActionAllowed in Hallowed.
  destruct Hallowed as [_ [_ Hsession]].
  exact Hsession.
Qed.

Theorem wrong_protocol_instance_rejects_action :
  forall request endpoint,
    requestProtocolInstance request <>
      protocolContractInstance (protocolOccurrenceContract endpoint) ->
    ~ ProtocolActionAllowed request endpoint.
Proof.
  intros request endpoint Hdifferent Hallowed.
  apply Hdifferent.
  eapply protocol_action_requires_exact_instance.
  exact Hallowed.
Qed.

Theorem wrong_protocol_role_rejects_action :
  forall request endpoint,
    requestProtocolRole request <>
      protocolContractRole (protocolOccurrenceContract endpoint) ->
    ~ ProtocolActionAllowed request endpoint.
Proof.
  intros request endpoint Hdifferent Hallowed.
  apply Hdifferent.
  eapply protocol_action_requires_exact_role.
  exact Hallowed.
Qed.

Theorem action_not_admitted_by_current_local_state_rejects :
  forall request endpoint,
    ~ LocalActionAllowed
        (protocolContractSession (protocolOccurrenceContract endpoint))
        (requestProtocolAction request) ->
    ~ ProtocolActionAllowed request endpoint.
Proof.
  intros request endpoint HnotAllowed Hallowed.
  apply HnotAllowed.
  eapply protocol_action_requires_current_local_state_admission.
  exact Hallowed.
Qed.

Theorem exact_protocol_action_gate_is_sufficient :
  forall request endpoint,
    requestProtocolInstance request =
      protocolContractInstance (protocolOccurrenceContract endpoint) ->
    requestProtocolRole request =
      protocolContractRole (protocolOccurrenceContract endpoint) ->
    LocalActionAllowed
      (protocolContractSession (protocolOccurrenceContract endpoint))
      (requestProtocolAction request) ->
    ProtocolActionAllowed request endpoint.
Proof.
  intros request endpoint Hinstance Hrole Hsession.
  unfold ProtocolActionAllowed.
  repeat split; assumption.
Qed.

Theorem coincident_runtime_representation_does_not_merge_distinct_instances :
  forall left right,
    RuntimeCoincident left right ->
    protocolContractInstance (realizedProtocolContract left) <>
      protocolContractInstance (realizedProtocolContract right) ->
    ~ RealizationCorresponds left right.
Proof.
  intros left right _ Hdifferent Hcorresponds.
  unfold RealizationCorresponds, ContractMatches in Hcorresponds.
  destruct Hcorresponds as [Hinstance _].
  apply Hdifferent.
  exact Hinstance.
Qed.

Theorem coincident_runtime_representation_does_not_erase_role_identity :
  forall left right,
    RuntimeCoincident left right ->
    protocolContractRole (realizedProtocolContract left) <>
      protocolContractRole (realizedProtocolContract right) ->
    ~ RealizationCorresponds left right.
Proof.
  intros left right _ Hdifferent Hcorresponds.
  unfold RealizationCorresponds, ContractMatches in Hcorresponds.
  destruct Hcorresponds as [_ [Hrole _]].
  apply Hdifferent.
  exact Hrole.
Qed.
