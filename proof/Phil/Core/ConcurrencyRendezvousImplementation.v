From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ConcurrencyRendezvous.

(*
  Machine-facing decision surface for PHIL-CONC-RENDEZVOUS-001.

  The exact Certified theorem has twenty-one fields.  The extracted ABI groups
  them by semantic authority rather than flattening them into one opaque call:

  - binary protocol / endpoint progression exactness;
  - activated internal-participant linkage;
  - independent Message admission plus the coarse rendezvous/ownership step.

  Concrete Haskell endpoint/resource maps, ProcessKey/role-occurrence encoding,
  source-to-architecture extraction, and physical causality realization remain
  correspondence boundaries reflected into these booleans by production code.
*)

Definition RendezvousEndpointFacts
  (witness : DualRendezvousWitness) : Prop :=
  BinaryInstanceWellFormed (dualRendezvousInstance witness) /\
  EndpointProgressionAccepted (dualRendezvousSenderEndpoint witness) /\
  EndpointProgressionAccepted (dualRendezvousReceiverEndpoint witness) /\
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
        (dualRendezvousSenderEndpoint witness))) =
    binaryProtocolPrimaryRole (dualRendezvousInstance witness) /\
  protocolContractRole
    (protocolOccurrenceContract
      (endpointProgressionPredecessor
        (dualRendezvousReceiverEndpoint witness))) =
    binaryProtocolPeerRole (dualRendezvousInstance witness) /\
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

Definition RendezvousParticipantFacts
  (witness : DualRendezvousWitness) : Prop :=
  ParticipantClassificationValid
    (dualRendezvousPopulation witness)
    (dualRendezvousActivation witness)
    (dualRendezvousExpectedRoles witness)
    (dualRendezvousParticipants witness) /\
  dualRendezvousParticipants witness
    (dualRendezvousSenderRoleOccurrence witness) =
    Some (InternalParticipant (dualRendezvousSenderProcess witness)) /\
  dualRendezvousParticipants witness
    (dualRendezvousReceiverRoleOccurrence witness) =
    Some (InternalParticipant (dualRendezvousReceiverProcess witness)) /\
  dualRendezvousSenderRoleOccurrence witness =
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousSenderEndpoint witness))) /\
  dualRendezvousReceiverRoleOccurrence witness =
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousReceiverEndpoint witness))).

Definition RendezvousMessageCoarseFacts
  (witness : DualRendezvousWitness) : Prop :=
  MessageContractAccepted
    (dualRendezvousMessageType witness)
    (dualRendezvousMessageSemantics witness)
    (dualRendezvousMessageContract witness) /\
  RendezvousValid
    (dualRendezvousMessageAdmission witness)
    (dualRendezvousOwnershipBefore witness)
    (dualRendezvousOwnershipAfter witness)
    (dualRendezvousStep witness) /\
  rendezvousProtocolInstance (dualRendezvousStep witness) =
    binaryProtocolInstanceRevision (dualRendezvousInstance witness) /\
  rendezvousSenderRole (dualRendezvousStep witness) =
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousSenderEndpoint witness))) /\
  rendezvousReceiverRole (dualRendezvousStep witness) =
    protocolContractRole
      (protocolOccurrenceContract
        (endpointProgressionPredecessor
          (dualRendezvousReceiverEndpoint witness))) /\
  rendezvousSenderProcess (dualRendezvousStep witness) =
    dualRendezvousSenderProcess witness /\
  rendezvousReceiverProcess (dualRendezvousStep witness) =
    dualRendezvousReceiverProcess witness.

Definition decideRendezvousEndpointFactsByFacts
  (binaryWellFormed senderProgression receiverProgression
   senderInstanceExact receiverInstanceExact
   senderRoleExact receiverRoleExact
   currentSessionsDual successorSessionsDual : bool) : bool :=
  andb binaryWellFormed
    (andb senderProgression
      (andb receiverProgression
        (andb senderInstanceExact
          (andb receiverInstanceExact
            (andb senderRoleExact
              (andb receiverRoleExact
                (andb currentSessionsDual successorSessionsDual))))))).

Definition decideRendezvousParticipantFactsByFacts
  (classificationValid senderParticipantExact receiverParticipantExact
   senderRoleOccurrenceExact receiverRoleOccurrenceExact : bool) : bool :=
  andb classificationValid
    (andb senderParticipantExact
      (andb receiverParticipantExact
        (andb senderRoleOccurrenceExact receiverRoleOccurrenceExact))).

Definition decideRendezvousMessageCoarseFactsByFacts
  (messageAccepted coarseStepValid coarseInstanceExact
   coarseSenderRoleExact coarseReceiverRoleExact
   coarseSenderProcessExact coarseReceiverProcessExact : bool) : bool :=
  andb messageAccepted
    (andb coarseStepValid
      (andb coarseInstanceExact
        (andb coarseSenderRoleExact
          (andb coarseReceiverRoleExact
            (andb coarseSenderProcessExact coarseReceiverProcessExact))))).

Definition decideExactInternalRendezvousByFacts
  (endpointFactsValid participantFactsValid messageCoarseFactsValid : bool) : bool :=
  andb endpointFactsValid
    (andb participantFactsValid messageCoarseFactsValid).

Theorem decideRendezvousEndpointFactsByFacts_classifies :
  forall witness
         binaryWellFormed senderProgression receiverProgression
         senderInstanceExact receiverInstanceExact
         senderRoleExact receiverRoleExact
         currentSessionsDual successorSessionsDual,
    (binaryWellFormed = true <->
      BinaryInstanceWellFormed (dualRendezvousInstance witness)) ->
    (senderProgression = true <->
      EndpointProgressionAccepted (dualRendezvousSenderEndpoint witness)) ->
    (receiverProgression = true <->
      EndpointProgressionAccepted (dualRendezvousReceiverEndpoint witness)) ->
    (senderInstanceExact = true <->
      protocolContractInstance
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousSenderEndpoint witness))) =
      binaryProtocolInstanceRevision (dualRendezvousInstance witness)) ->
    (receiverInstanceExact = true <->
      protocolContractInstance
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousReceiverEndpoint witness))) =
      binaryProtocolInstanceRevision (dualRendezvousInstance witness)) ->
    (senderRoleExact = true <->
      protocolContractRole
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousSenderEndpoint witness))) =
      binaryProtocolPrimaryRole (dualRendezvousInstance witness)) ->
    (receiverRoleExact = true <->
      protocolContractRole
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousReceiverEndpoint witness))) =
      binaryProtocolPeerRole (dualRendezvousInstance witness)) ->
    (currentSessionsDual = true <->
      protocolContractSession
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousReceiverEndpoint witness))) =
      dualSession
        (protocolContractSession
          (protocolOccurrenceContract
            (endpointProgressionPredecessor
              (dualRendezvousSenderEndpoint witness))))) ->
    (successorSessionsDual = true <->
      endpointProgressionSuccessorSession
        (dualRendezvousReceiverEndpoint witness) =
      dualSession
        (endpointProgressionSuccessorSession
          (dualRendezvousSenderEndpoint witness))) ->
    decideRendezvousEndpointFactsByFacts
      binaryWellFormed senderProgression receiverProgression
      senderInstanceExact receiverInstanceExact
      senderRoleExact receiverRoleExact
      currentSessionsDual successorSessionsDual = true <->
    RendezvousEndpointFacts witness.
Proof.
  intros witness binaryWellFormed senderProgression receiverProgression
    senderInstanceExact receiverInstanceExact senderRoleExact receiverRoleExact
    currentSessionsDual successorSessionsDual
    Hbinary HsenderProgression HreceiverProgression HsenderInstance
    HreceiverInstance HsenderRole HreceiverRole Hcurrent Hsuccessor.
  unfold decideRendezvousEndpointFactsByFacts, RendezvousEndpointFacts.
  repeat rewrite andb_true_iff.
  rewrite Hbinary, HsenderProgression, HreceiverProgression,
    HsenderInstance, HreceiverInstance, HsenderRole, HreceiverRole,
    Hcurrent, Hsuccessor.
  reflexivity.
Qed.

Theorem decideRendezvousParticipantFactsByFacts_classifies :
  forall witness
         classificationValid senderParticipantExact receiverParticipantExact
         senderRoleOccurrenceExact receiverRoleOccurrenceExact,
    (classificationValid = true <->
      ParticipantClassificationValid
        (dualRendezvousPopulation witness)
        (dualRendezvousActivation witness)
        (dualRendezvousExpectedRoles witness)
        (dualRendezvousParticipants witness)) ->
    (senderParticipantExact = true <->
      dualRendezvousParticipants witness
        (dualRendezvousSenderRoleOccurrence witness) =
      Some (InternalParticipant (dualRendezvousSenderProcess witness))) ->
    (receiverParticipantExact = true <->
      dualRendezvousParticipants witness
        (dualRendezvousReceiverRoleOccurrence witness) =
      Some (InternalParticipant (dualRendezvousReceiverProcess witness))) ->
    (senderRoleOccurrenceExact = true <->
      dualRendezvousSenderRoleOccurrence witness =
      protocolContractRole
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousSenderEndpoint witness)))) ->
    (receiverRoleOccurrenceExact = true <->
      dualRendezvousReceiverRoleOccurrence witness =
      protocolContractRole
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousReceiverEndpoint witness)))) ->
    decideRendezvousParticipantFactsByFacts
      classificationValid senderParticipantExact receiverParticipantExact
      senderRoleOccurrenceExact receiverRoleOccurrenceExact = true <->
    RendezvousParticipantFacts witness.
Proof.
  intros witness classificationValid senderParticipantExact receiverParticipantExact
    senderRoleOccurrenceExact receiverRoleOccurrenceExact
    Hclassification Hsender Hreceiver HsenderRole HreceiverRole.
  unfold decideRendezvousParticipantFactsByFacts, RendezvousParticipantFacts.
  repeat rewrite andb_true_iff.
  rewrite Hclassification, Hsender, Hreceiver, HsenderRole, HreceiverRole.
  reflexivity.
Qed.

Theorem decideRendezvousMessageCoarseFactsByFacts_classifies :
  forall witness
         messageAccepted coarseStepValid coarseInstanceExact
         coarseSenderRoleExact coarseReceiverRoleExact
         coarseSenderProcessExact coarseReceiverProcessExact,
    (messageAccepted = true <->
      MessageContractAccepted
        (dualRendezvousMessageType witness)
        (dualRendezvousMessageSemantics witness)
        (dualRendezvousMessageContract witness)) ->
    (coarseStepValid = true <->
      RendezvousValid
        (dualRendezvousMessageAdmission witness)
        (dualRendezvousOwnershipBefore witness)
        (dualRendezvousOwnershipAfter witness)
        (dualRendezvousStep witness)) ->
    (coarseInstanceExact = true <->
      rendezvousProtocolInstance (dualRendezvousStep witness) =
      binaryProtocolInstanceRevision (dualRendezvousInstance witness)) ->
    (coarseSenderRoleExact = true <->
      rendezvousSenderRole (dualRendezvousStep witness) =
      protocolContractRole
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousSenderEndpoint witness)))) ->
    (coarseReceiverRoleExact = true <->
      rendezvousReceiverRole (dualRendezvousStep witness) =
      protocolContractRole
        (protocolOccurrenceContract
          (endpointProgressionPredecessor
            (dualRendezvousReceiverEndpoint witness)))) ->
    (coarseSenderProcessExact = true <->
      rendezvousSenderProcess (dualRendezvousStep witness) =
      dualRendezvousSenderProcess witness) ->
    (coarseReceiverProcessExact = true <->
      rendezvousReceiverProcess (dualRendezvousStep witness) =
      dualRendezvousReceiverProcess witness) ->
    decideRendezvousMessageCoarseFactsByFacts
      messageAccepted coarseStepValid coarseInstanceExact
      coarseSenderRoleExact coarseReceiverRoleExact
      coarseSenderProcessExact coarseReceiverProcessExact = true <->
    RendezvousMessageCoarseFacts witness.
Proof.
  intros witness messageAccepted coarseStepValid coarseInstanceExact
    coarseSenderRoleExact coarseReceiverRoleExact
    coarseSenderProcessExact coarseReceiverProcessExact
    Hmessage Hstep Hinstance HsenderRole HreceiverRole HsenderProcess HreceiverProcess.
  unfold decideRendezvousMessageCoarseFactsByFacts, RendezvousMessageCoarseFacts.
  repeat rewrite andb_true_iff.
  rewrite Hmessage, Hstep, Hinstance, HsenderRole, HreceiverRole,
    HsenderProcess, HreceiverProcess.
  reflexivity.
Qed.

Theorem exactInternalRendezvous_grouped :
  forall witness,
    RendezvousEndpointFacts witness /\
    RendezvousParticipantFacts witness /\
    RendezvousMessageCoarseFacts witness <->
    ExactInternalRendezvous witness.
Proof.
  intros witness.
  split.
  - intros [Hendpoint [Hparticipant Hcoarse]].
    unfold RendezvousEndpointFacts in Hendpoint.
    unfold RendezvousParticipantFacts in Hparticipant.
    unfold RendezvousMessageCoarseFacts in Hcoarse.
    destruct Hendpoint as
      [Hbinary [HsenderProgression [HreceiverProgression
      [HsenderInstance [HreceiverInstance [HsenderRole [HreceiverRole
      [HcurrentDual HsuccessorDual]]]]]]]].
    destruct Hparticipant as
      [Hclassification [HsenderParticipant [HreceiverParticipant
      [HsenderRoleOccurrence HreceiverRoleOccurrence]]]].
    destruct Hcoarse as
      [Hmessage [Hstep [HcoarseInstance [HcoarseSenderRole
      [HcoarseReceiverRole [HcoarseSenderProcess HcoarseReceiverProcess]]]]]].
    constructor; assumption.
  - intros Haccepted.
    split.
    + unfold RendezvousEndpointFacts.
      refine (conj (exactRendezvousBinaryWellFormed witness Haccepted) _).
      refine (conj (exactRendezvousSenderProgression witness Haccepted) _).
      refine (conj (exactRendezvousReceiverProgression witness Haccepted) _).
      refine (conj (exactRendezvousSenderInstance witness Haccepted) _).
      refine (conj (exactRendezvousReceiverInstance witness Haccepted) _).
      refine (conj (exactRendezvousSenderRole witness Haccepted) _).
      refine (conj (exactRendezvousReceiverRole witness Haccepted) _).
      refine (conj (exactRendezvousCurrentSessionsDual witness Haccepted) _).
      exact (exactRendezvousSuccessorSessionsDual witness Haccepted).
    + split.
      * unfold RendezvousParticipantFacts.
        refine (conj (exactRendezvousParticipantClassification witness Haccepted) _).
        refine (conj (exactRendezvousSenderParticipant witness Haccepted) _).
        refine (conj (exactRendezvousReceiverParticipant witness Haccepted) _).
        refine (conj (exactRendezvousSenderRoleOccurrence witness Haccepted) _).
        exact (exactRendezvousReceiverRoleOccurrence witness Haccepted).
      * unfold RendezvousMessageCoarseFacts.
        refine (conj (exactRendezvousMessageAccepted witness Haccepted) _).
        refine (conj (exactRendezvousCoarseStep witness Haccepted) _).
        refine (conj (exactRendezvousCoarseInstance witness Haccepted) _).
        refine (conj (exactRendezvousCoarseSenderRole witness Haccepted) _).
        refine (conj (exactRendezvousCoarseReceiverRole witness Haccepted) _).
        refine (conj (exactRendezvousCoarseSenderProcess witness Haccepted) _).
        exact (exactRendezvousCoarseReceiverProcess witness Haccepted).
Qed.

Theorem decideExactInternalRendezvousByFacts_classifies :
  forall witness endpointFactsValid participantFactsValid messageCoarseFactsValid,
    (endpointFactsValid = true <-> RendezvousEndpointFacts witness) ->
    (participantFactsValid = true <-> RendezvousParticipantFacts witness) ->
    (messageCoarseFactsValid = true <-> RendezvousMessageCoarseFacts witness) ->
    decideExactInternalRendezvousByFacts
      endpointFactsValid participantFactsValid messageCoarseFactsValid = true <->
    ExactInternalRendezvous witness.
Proof.
  intros witness endpointFactsValid participantFactsValid messageCoarseFactsValid
    Hendpoint Hparticipant Hcoarse.
  unfold decideExactInternalRendezvousByFacts.
  repeat rewrite andb_true_iff.
  rewrite Hendpoint, Hparticipant, Hcoarse.
  apply exactInternalRendezvous_grouped.
Qed.

Theorem accepted_grouped_rendezvous_has_semantic_causality :
  forall witness,
    RendezvousEndpointFacts witness ->
    RendezvousParticipantFacts witness ->
    RendezvousMessageCoarseFacts witness ->
    SourceCausalEdge
      (dualRendezvousSenderProcess witness)
      (dualRendezvousReceiverProcess witness) /\
    ~ SchedulerOnlyEdge
      (dualRendezvousSenderProcess witness)
      (dualRendezvousReceiverProcess witness).
Proof.
  intros witness Hendpoint Hparticipant Hcoarse.
  apply accepted_rendezvous_causality_is_semantic_not_scheduler_order.
  apply (proj1 (exactInternalRendezvous_grouped witness)).
  exact (conj Hendpoint (conj Hparticipant Hcoarse)).
Qed.
