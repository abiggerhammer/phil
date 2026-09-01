From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

From Phil.Core Require Import
  Session
  ProtocolIdentity
  ProtocolProjection
  ProtocolProgressionGuard
  ProtocolMessageAdmissibility
  ConcurrencySemantics
  ConcurrencyActivation.

(*
  PHIL-CONC-RENDEZVOUS-001 — exact synchronous rendezvous, restricted-owner
  transfer, and scheduler-independent causality.

  This theorem composes Certified protocol identity/projection/progression,
  Message admissibility, PHIL-CONC-SEM-001, and PHIL-CONC-ACTIVATE-001.  It
  deliberately does not model physical transport timing or scheduler fairness.
  Concrete Haskell endpoint/resource maps, ProcessKey/role-occurrence encoding,
  and source-to-architecture extraction remain correspondence boundaries.
*)

Record EndpointProgressionWitness : Type := mkEndpointProgressionWitness {
  endpointProgressionPredecessor : ProtocolEndpointOccurrence;
  endpointProgressionSuccessorName : ProtocolOccurrenceName;
  endpointProgressionSuccessorSession : Session;
  endpointProgressionBefore : ProtocolLiveContext;
  endpointProgressionAfter : ProtocolLiveContext;
  endpointProgressionLiveSuccessor : ProtocolEndpointOccurrence;
  endpointProgressionRequest : ProtocolActionRequest
}.

Definition EndpointProgressionAccepted
  (witness : EndpointProgressionWitness) : Prop :=
  endpointProgressionBefore witness
      (protocolOccurrenceName (endpointProgressionPredecessor witness)) =
    Some (protocolOccurrenceContract (endpointProgressionPredecessor witness)) /\
  ProtocolActionAllowed
    (endpointProgressionRequest witness)
    (endpointProgressionPredecessor witness) /\
  continueProtocolOccurrence
    (protocolOccurrenceName (endpointProgressionPredecessor witness))
    (endpointProgressionSuccessorName witness)
    (endpointProgressionSuccessorSession witness)
    (endpointProgressionBefore witness) =
      ProtocolProgressionContinued
        (endpointProgressionAfter witness)
        (endpointProgressionLiveSuccessor witness).

Record DualRendezvousWitness : Type := mkDualRendezvousWitness {
  dualRendezvousInstance : BinaryProtocolInstance;
  dualRendezvousSenderEndpoint : EndpointProgressionWitness;
  dualRendezvousReceiverEndpoint : EndpointProgressionWitness;
  dualRendezvousPopulation : ProcessPopulation;
  dualRendezvousActivation : ActivationMap;
  dualRendezvousExpectedRoles : ExpectedProtocolRoles;
  dualRendezvousParticipants : ParticipantMap;
  dualRendezvousSenderRoleOccurrence : ProtocolRoleOccurrence;
  dualRendezvousReceiverRoleOccurrence : ProtocolRoleOccurrence;
  dualRendezvousSenderProcess : ProcessKey;
  dualRendezvousReceiverProcess : ProcessKey;
  dualRendezvousStep : RendezvousStep;
  dualRendezvousMessageType : MessageType;
  dualRendezvousMessageSemantics : nat;
  dualRendezvousMessageContract : BoundaryMessageContract;
  dualRendezvousMessageAdmission : MessageAdmission;
  dualRendezvousOwnershipBefore : RestrictedOwnership;
  dualRendezvousOwnershipAfter : RestrictedOwnership
}.

Record ExactInternalRendezvous
  (witness : DualRendezvousWitness) : Prop := mkExactInternalRendezvous {
  exactRendezvousBinaryWellFormed :
    BinaryInstanceWellFormed (dualRendezvousInstance witness);
  exactRendezvousSenderProgression :
    EndpointProgressionAccepted (dualRendezvousSenderEndpoint witness);
  exactRendezvousReceiverProgression :
    EndpointProgressionAccepted (dualRendezvousReceiverEndpoint witness);
  exactRendezvousSenderInstance :
    protocolContractInstance
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousSenderEndpoint witness))) =
    binaryProtocolInstanceRevision (dualRendezvousInstance witness);
  exactRendezvousReceiverInstance :
    protocolContractInstance
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousReceiverEndpoint witness))) =
    binaryProtocolInstanceRevision (dualRendezvousInstance witness);
  exactRendezvousSenderRole :
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousSenderEndpoint witness))) =
    binaryProtocolPrimaryRole (dualRendezvousInstance witness);
  exactRendezvousReceiverRole :
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousReceiverEndpoint witness))) =
    binaryProtocolPeerRole (dualRendezvousInstance witness);
  exactRendezvousCurrentSessionsDual :
    protocolContractSession
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousReceiverEndpoint witness))) =
    dualSession
      (protocolContractSession
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousSenderEndpoint witness))));
  exactRendezvousSuccessorSessionsDual :
    endpointProgressionSuccessorSession
      (dualRendezvousReceiverEndpoint witness) =
    dualSession
      (endpointProgressionSuccessorSession
        (dualRendezvousSenderEndpoint witness));
  exactRendezvousParticipantClassification :
    ParticipantClassificationValid
      (dualRendezvousPopulation witness)
      (dualRendezvousActivation witness)
      (dualRendezvousExpectedRoles witness)
      (dualRendezvousParticipants witness);
  exactRendezvousSenderParticipant :
    dualRendezvousParticipants witness
      (dualRendezvousSenderRoleOccurrence witness) =
    Some (InternalParticipant (dualRendezvousSenderProcess witness));
  exactRendezvousReceiverParticipant :
    dualRendezvousParticipants witness
      (dualRendezvousReceiverRoleOccurrence witness) =
    Some (InternalParticipant (dualRendezvousReceiverProcess witness));
  exactRendezvousSenderRoleOccurrence :
    dualRendezvousSenderRoleOccurrence witness =
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousSenderEndpoint witness)));
  exactRendezvousReceiverRoleOccurrence :
    dualRendezvousReceiverRoleOccurrence witness =
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousReceiverEndpoint witness)));
  exactRendezvousMessageAccepted :
    MessageContractAccepted
      (dualRendezvousMessageType witness)
      (dualRendezvousMessageSemantics witness)
      (dualRendezvousMessageContract witness);
  exactRendezvousCoarseStep :
    RendezvousValid
      (dualRendezvousMessageAdmission witness)
      (dualRendezvousOwnershipBefore witness)
      (dualRendezvousOwnershipAfter witness)
      (dualRendezvousStep witness);
  exactRendezvousCoarseInstance :
    rendezvousProtocolInstance (dualRendezvousStep witness) =
    binaryProtocolInstanceRevision (dualRendezvousInstance witness);
  exactRendezvousCoarseSenderRole :
    rendezvousSenderRole (dualRendezvousStep witness) =
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousSenderEndpoint witness)));
  exactRendezvousCoarseReceiverRole :
    rendezvousReceiverRole (dualRendezvousStep witness) =
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousReceiverEndpoint witness)));
  exactRendezvousCoarseSenderProcess :
    rendezvousSenderProcess (dualRendezvousStep witness) =
    dualRendezvousSenderProcess witness;
  exactRendezvousCoarseReceiverProcess :
    rendezvousReceiverProcess (dualRendezvousStep witness) =
    dualRendezvousReceiverProcess witness
}.

Theorem accepted_rendezvous_uses_exact_binary_instance_and_roles :
  forall witness,
    ExactInternalRendezvous witness ->
    protocolContractInstance
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousSenderEndpoint witness))) =
      binaryProtocolInstanceRevision (dualRendezvousInstance witness) /\
    protocolContractInstance
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousReceiverEndpoint witness))) =
      binaryProtocolInstanceRevision (dualRendezvousInstance witness) /\
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousSenderEndpoint witness))) <>
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousReceiverEndpoint witness))).
Proof.
  intros witness Haccepted.
  destruct Haccepted as
    [Hwell _ _ HsenderInstance HreceiverInstance HsenderRole HreceiverRole
     _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  split.
  - exact HsenderInstance.
  - split.
    + exact HreceiverInstance.
    + destruct Hwell as [Hroles _].
      rewrite HsenderRole, HreceiverRole.
      exact Hroles.
Qed.

Theorem accepted_rendezvous_current_and_successor_sessions_are_dual :
  forall witness,
    ExactInternalRendezvous witness ->
    protocolContractSession
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousReceiverEndpoint witness))) =
      dualSession
        (protocolContractSession
          (protocolOccurrenceContract
            (endpointProgressionPredecessor
              (dualRendezvousSenderEndpoint witness)))) /\
    endpointProgressionSuccessorSession
      (dualRendezvousReceiverEndpoint witness) =
      dualSession
        (endpointProgressionSuccessorSession
          (dualRendezvousSenderEndpoint witness)).
Proof.
  intros witness Haccepted.
  destruct Haccepted as
    [_ _ _ _ _ _ _ Hcurrent Hsuccessor _ _ _ _ _ _ _ _ _ _ _ _].
  split; assumption.
Qed.

Theorem accepted_rendezvous_predecessors_are_consumed :
  forall witness,
    ExactInternalRendezvous witness ->
    endpointProgressionAfter (dualRendezvousSenderEndpoint witness)
      (protocolOccurrenceName
        (endpointProgressionPredecessor
          (dualRendezvousSenderEndpoint witness))) = None /\
    endpointProgressionAfter (dualRendezvousReceiverEndpoint witness)
      (protocolOccurrenceName
        (endpointProgressionPredecessor
          (dualRendezvousReceiverEndpoint witness))) = None.
Proof.
  intros witness Haccepted.
  destruct Haccepted as [_ Hsender Hreceiver _].
  unfold EndpointProgressionAccepted in Hsender, Hreceiver.
  destruct Hsender as [_ [_ HsenderStep]].
  destruct Hreceiver as [_ [_ HreceiverStep]].
  split.
  - eapply successful_continuation_removes_predecessor.
    exact HsenderStep.
  - eapply successful_continuation_removes_predecessor.
    exact HreceiverStep.
Qed.

Theorem accepted_rendezvous_installs_exact_successors :
  forall witness,
    ExactInternalRendezvous witness ->
    (exists predecessorContract,
      endpointProgressionBefore (dualRendezvousSenderEndpoint witness)
        (protocolOccurrenceName
          (endpointProgressionPredecessor
            (dualRendezvousSenderEndpoint witness))) = Some predecessorContract /\
      endpointProgressionAfter (dualRendezvousSenderEndpoint witness)
        (endpointProgressionSuccessorName
          (dualRendezvousSenderEndpoint witness)) =
        Some
          (continuedContract predecessorContract
            (endpointProgressionSuccessorSession
              (dualRendezvousSenderEndpoint witness)))) /\
    (exists predecessorContract,
      endpointProgressionBefore (dualRendezvousReceiverEndpoint witness)
        (protocolOccurrenceName
          (endpointProgressionPredecessor
            (dualRendezvousReceiverEndpoint witness))) = Some predecessorContract /\
      endpointProgressionAfter (dualRendezvousReceiverEndpoint witness)
        (endpointProgressionSuccessorName
          (dualRendezvousReceiverEndpoint witness)) =
        Some
          (continuedContract predecessorContract
            (endpointProgressionSuccessorSession
              (dualRendezvousReceiverEndpoint witness)))).
Proof.
  intros witness Haccepted.
  destruct Haccepted as [_ Hsender Hreceiver _].
  unfold EndpointProgressionAccepted in Hsender, Hreceiver.
  destruct Hsender as [_ [_ HsenderStep]].
  destruct Hreceiver as [_ [_ HreceiverStep]].
  split.
  - pose proof
      (successful_continuation_installs_exact_successor
        _ _ _ _ _ _ HsenderStep) as Hinstalled.
    destruct Hinstalled as [contract [Hlookup [Hnext _]]].
    exists contract.
    split; assumption.
  - pose proof
      (successful_continuation_installs_exact_successor
        _ _ _ _ _ _ HreceiverStep) as Hinstalled.
    destruct Hinstalled as [contract [Hlookup [Hnext _]]].
    exists contract.
    split; assumption.
Qed.

Theorem accepted_rendezvous_successors_preserve_exact_instance_and_role :
  forall witness,
    ExactInternalRendezvous witness ->
    protocolContractInstance
      (protocolOccurrenceContract
        (endpointProgressionLiveSuccessor
          (dualRendezvousSenderEndpoint witness))) =
      protocolContractInstance
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousSenderEndpoint witness))) /\
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionLiveSuccessor
          (dualRendezvousSenderEndpoint witness))) =
      protocolContractRole
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousSenderEndpoint witness))) /\
    protocolContractInstance
      (protocolOccurrenceContract
        (endpointProgressionLiveSuccessor
          (dualRendezvousReceiverEndpoint witness))) =
      protocolContractInstance
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousReceiverEndpoint witness))) /\
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionLiveSuccessor
          (dualRendezvousReceiverEndpoint witness))) =
      protocolContractRole
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousReceiverEndpoint witness))).
Proof.
  intros witness Haccepted.
  destruct Haccepted as [_ Hsender Hreceiver _].
  unfold EndpointProgressionAccepted in Hsender, Hreceiver.
  destruct Hsender as [HsenderLookup [_ HsenderStep]].
  destruct Hreceiver as [HreceiverLookup [_ HreceiverStep]].
  pose proof
    (successful_continuation_preserves_exact_instance_and_role
      _ _ _ _ _ _ HsenderStep) as HsenderExact.
  pose proof
    (successful_continuation_preserves_exact_instance_and_role
      _ _ _ _ _ _ HreceiverStep) as HreceiverExact.
  destruct HsenderExact as [senderContract [HsenderFound [HsenderInstance [HsenderRole _]]]].
  destruct HreceiverExact as [receiverContract [HreceiverFound [HreceiverInstance [HreceiverRole _]]]].
  rewrite HsenderLookup in HsenderFound.
  inversion HsenderFound; subst senderContract.
  rewrite HreceiverLookup in HreceiverFound.
  inversion HreceiverFound; subst receiverContract.
  repeat split; assumption.
Qed.

Theorem accepted_rendezvous_message_admission_precedes_restricted_transfer :
  forall witness subject,
    ExactInternalRendezvous witness ->
    rendezvousRestrictedSubject (dualRendezvousStep witness) = Some subject ->
    MessageContractAccepted
      (dualRendezvousMessageType witness)
      (dualRendezvousMessageSemantics witness)
      (dualRendezvousMessageContract witness) /\
    dualRendezvousOwnershipBefore witness subject =
      Some (dualRendezvousSenderProcess witness) /\
    dualRendezvousOwnershipAfter witness subject =
      Some (dualRendezvousReceiverProcess witness).
Proof.
  intros witness subject Haccepted Hsubject.
  destruct Haccepted as
    [_ _ _ _ _ _ _ _ _ _ _ _ _ Hmessage Hcoarse _ _ _ HsenderProcess HreceiverProcess].
  pose proof
    (restricted_rendezvous_transfers_exact_owner
      (dualRendezvousMessageAdmission witness)
      (dualRendezvousOwnershipBefore witness)
      (dualRendezvousOwnershipAfter witness)
      (dualRendezvousStep witness)
      subject Hcoarse Hsubject) as Htransfer.
  destruct Htransfer as [Hbefore Hafter].
  split.
  - exact Hmessage.
  - split.
    + rewrite <- HsenderProcess.
      exact Hbefore.
    + rewrite <- HreceiverProcess.
      exact Hafter.
Qed.

Theorem accepted_rendezvous_internal_processes_are_activated :
  forall witness,
    ExactInternalRendezvous witness ->
    (exists target,
      dualRendezvousActivation witness (dualRendezvousSenderProcess witness) =
        Some target) /\
    (exists target,
      dualRendezvousActivation witness (dualRendezvousReceiverProcess witness) =
        Some target).
Proof.
  intros witness Haccepted.
  destruct Haccepted as
    [_ _ _ _ _ _ _ _ _ Hparticipants Hsender Hreceiver _ _ _ _ _ _ _ _ _].
  split.
  - eapply internal_participant_names_activated_process.
    + exact Hparticipants.
    + exact Hsender.
  - eapply internal_participant_names_activated_process.
    + exact Hparticipants.
    + exact Hreceiver.
Qed.

Theorem accepted_rendezvous_internal_processes_are_static :
  forall witness,
    ExactInternalRendezvous witness ->
    (exists occurrence,
      In occurrence (dualRendezvousPopulation witness) /\
      staticProcessKey occurrence = dualRendezvousSenderProcess witness) /\
    (exists occurrence,
      In occurrence (dualRendezvousPopulation witness) /\
      staticProcessKey occurrence = dualRendezvousReceiverProcess witness).
Proof.
  intros witness Haccepted.
  destruct Haccepted as
    [_ _ _ _ _ _ _ _ _ Hparticipants Hsender Hreceiver _ _ _ _ _ _ _ _ _].
  split.
  - eapply internal_participant_names_static_process.
    + exact Hparticipants.
    + exact Hsender.
  - eapply internal_participant_names_static_process.
    + exact Hparticipants.
    + exact Hreceiver.
Qed.

Theorem accepted_rendezvous_causality_is_semantic_not_scheduler_order :
  forall witness,
    ExactInternalRendezvous witness ->
    SourceCausalEdge
      (dualRendezvousSenderProcess witness)
      (dualRendezvousReceiverProcess witness) /\
    ~ SchedulerOnlyEdge
      (dualRendezvousSenderProcess witness)
      (dualRendezvousReceiverProcess witness).
Proof.
  intros witness Haccepted.
  destruct Haccepted as
    [_ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcoarse _ _ _ HsenderProcess HreceiverProcess].
  pose proof
    (restricted_rendezvous_sender_and_receiver_are_distinct
      (dualRendezvousMessageAdmission witness)
      (dualRendezvousOwnershipBefore witness)
      (dualRendezvousOwnershipAfter witness)
      (dualRendezvousStep witness) Hcoarse) as Hdistinct.
  rewrite HsenderProcess, HreceiverProcess in Hdistinct.
  split.
  - apply CauseRendezvous.
    exact Hdistinct.
  - apply scheduler_order_is_not_source_causality.
Qed.

Theorem accepted_rendezvous_makes_both_predecessors_stale :
  forall witness,
    ExactInternalRendezvous witness ->
    (forall attemptedSuccessor attemptedSession,
      continueProtocolOccurrence
        (protocolOccurrenceName
          (endpointProgressionPredecessor
            (dualRendezvousSenderEndpoint witness)))
        attemptedSuccessor attemptedSession
        (endpointProgressionAfter (dualRendezvousSenderEndpoint witness)) =
      ProtocolProgressionRejected) /\
    (forall attemptedSuccessor attemptedSession,
      continueProtocolOccurrence
        (protocolOccurrenceName
          (endpointProgressionPredecessor
            (dualRendezvousReceiverEndpoint witness)))
        attemptedSuccessor attemptedSession
        (endpointProgressionAfter (dualRendezvousReceiverEndpoint witness)) =
      ProtocolProgressionRejected).
Proof.
  intros witness Haccepted.
  destruct Haccepted as [_ Hsender Hreceiver _].
  unfold EndpointProgressionAccepted in Hsender, Hreceiver.
  destruct Hsender as [_ [_ HsenderStep]].
  destruct Hreceiver as [_ [_ HreceiverStep]].
  split.
  - intros attemptedSuccessor attemptedSession.
    eapply successful_continuation_makes_predecessor_stale.
    exact HsenderStep.
  - intros attemptedSuccessor attemptedSession.
    eapply successful_continuation_makes_predecessor_stale.
    exact HreceiverStep.
Qed.
