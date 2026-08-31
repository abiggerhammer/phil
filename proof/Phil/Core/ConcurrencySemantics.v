From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

From Phil.Core Require Import
  Syntax
  ProcessJoin
  ProcessTerminal
  SystemsGenericLowering.

(*
  PHIL-CONC-SEM-001 — bounded architecture-level CSP safety semantics.

  This normalized model captures the already implemented CONC-001--011 safety
  boundary.  It intentionally does not postulate fairness, deadlock freedom,
  eventual response, deadlines, or a physical scheduling mechanism.

  Concrete Haskell Map/Set/Text representation, source/architecture extraction,
  ProcessKey serialization, protocol-message admission implementation, and the
  physical execution runtime remain explicit correspondence/realization
  boundaries checked by the companion Haskell workflow.
*)

Definition ProcessKey := nat.
Definition ProcessTarget := nat.
Definition ProtocolInstanceKey := nat.
Definition ProtocolRoleKey := nat.
Definition MessageSubjectKey := nat.
Definition RestrictedSubjectKey := nat.

(* -------------------------------------------------------------------------- *)
(* CONC-001--003, 010--011: static population and ownership partition.         *)
(* -------------------------------------------------------------------------- *)

Record StaticProcessOccurrence : Type := mkStaticProcessOccurrence {
  staticProcessKey : ProcessKey;
  staticProcessTarget : ProcessTarget
}.

Definition ProcessPopulation := list StaticProcessOccurrence.
Definition ActivationMap := ProcessKey -> option ProcessTarget.

Record StaticPopulationValid
  (population : ProcessPopulation)
  (activation : ActivationMap) : Prop := mkStaticPopulationValid {
  staticPopulationNonempty : population <> [];
  staticPopulationKeysNonzero :
    forall occurrence,
      In occurrence population ->
      staticProcessKey occurrence <> 0;
  staticPopulationKeysUnique :
    NoDup (map staticProcessKey population);
  staticPopulationActivationExact :
    forall occurrence,
      In occurrence population ->
      activation (staticProcessKey occurrence) =
        Some (staticProcessTarget occurrence);
  staticPopulationNoExtraActivation :
    forall key target,
      activation key = Some target ->
      exists occurrence,
        In occurrence population /\
        staticProcessKey occurrence = key /\
        staticProcessTarget occurrence = target
}.

Theorem every_static_process_is_activated :
  forall population activation occurrence,
    StaticPopulationValid population activation ->
    In occurrence population ->
    activation (staticProcessKey occurrence) =
      Some (staticProcessTarget occurrence).
Proof.
  intros population activation occurrence Hvalid Hin.
  destruct Hvalid as [_ _ _ Hactivation _].
  apply Hactivation.
  exact Hin.
Qed.

Theorem activation_target_is_functional :
  forall activation key first second,
    activation key = Some first ->
    activation key = Some second ->
    first = second.
Proof.
  intros activation key first second Hfirst Hsecond.
  rewrite Hfirst in Hsecond.
  inversion Hsecond.
  reflexivity.
Qed.

Theorem activation_cannot_invent_process :
  forall population activation key target,
    StaticPopulationValid population activation ->
    activation key = Some target ->
    exists occurrence,
      In occurrence population /\
      staticProcessKey occurrence = key /\
      staticProcessTarget occurrence = target.
Proof.
  intros population activation key target Hvalid Hlookup.
  destruct Hvalid as [_ _ _ _ Hnoextra].
  eapply Hnoextra.
  exact Hlookup.
Qed.

Definition RestrictedOwnership := RestrictedSubjectKey -> option ProcessKey.

Theorem restricted_subject_has_at_most_one_owner :
  forall ownership subject first second,
    ownership subject = Some first ->
    ownership subject = Some second ->
    first = second.
Proof.
  intros ownership subject first second Hfirst Hsecond.
  rewrite Hfirst in Hsecond.
  inversion Hsecond.
  reflexivity.
Qed.

Theorem structural_wrapper_cannot_create_second_restricted_owner :
  forall ownership subject owner other,
    ownership subject = Some owner ->
    other <> owner ->
    ownership subject <> Some other.
Proof.
  intros ownership subject owner other Howner Hneq Hother.
  apply Hneq.
  eapply restricted_subject_has_at_most_one_owner.
  - exact Hother.
  - exact Howner.
Qed.

(* -------------------------------------------------------------------------- *)
(* CONC-004--006 plus PROT-008: exact synchronous rendezvous and causality.    *)
(* -------------------------------------------------------------------------- *)

Definition MessageAdmission := MessageSubjectKey -> bool.

Record RendezvousStep : Type := mkRendezvousStep {
  rendezvousProtocolInstance : ProtocolInstanceKey;
  rendezvousSenderRole : ProtocolRoleKey;
  rendezvousReceiverRole : ProtocolRoleKey;
  rendezvousSenderProcess : ProcessKey;
  rendezvousReceiverProcess : ProcessKey;
  rendezvousMessageSubject : MessageSubjectKey;
  rendezvousRestrictedSubject : option RestrictedSubjectKey
}.

Definition RendezvousValid
  (admitted : MessageAdmission)
  (before after : RestrictedOwnership)
  (step : RendezvousStep) : Prop :=
  rendezvousProtocolInstance step <> 0 /\
  rendezvousSenderRole step <> rendezvousReceiverRole step /\
  rendezvousSenderProcess step <> rendezvousReceiverProcess step /\
  admitted (rendezvousMessageSubject step) = true /\
  match rendezvousRestrictedSubject step with
  | None => True
  | Some subject =>
      before subject = Some (rendezvousSenderProcess step) /\
      after subject = Some (rendezvousReceiverProcess step)
  end.

Theorem rendezvous_requires_message_admission :
  forall admitted before after step,
    RendezvousValid admitted before after step ->
    admitted (rendezvousMessageSubject step) = true.
Proof.
  intros admitted before after step Hvalid.
  destruct Hvalid as [_ [_ [_ [Hadmitted _]]]].
  exact Hadmitted.
Qed.

Theorem nonmessage_payload_cannot_rendezvous :
  forall admitted before after step,
    admitted (rendezvousMessageSubject step) = false ->
    ~ RendezvousValid admitted before after step.
Proof.
  intros admitted before after step Hnot Hvalid.
  pose proof (rendezvous_requires_message_admission admitted before after step Hvalid)
    as Hadmitted.
  rewrite Hnot in Hadmitted.
  discriminate.
Qed.

Theorem restricted_rendezvous_transfers_exact_owner :
  forall admitted before after step subject,
    RendezvousValid admitted before after step ->
    rendezvousRestrictedSubject step = Some subject ->
    before subject = Some (rendezvousSenderProcess step) /\
    after subject = Some (rendezvousReceiverProcess step).
Proof.
  intros admitted before after step subject Hvalid Hrestricted.
  destruct Hvalid as [_ [_ [_ [_ Htransfer]]]].
  rewrite Hrestricted in Htransfer.
  exact Htransfer.
Qed.

Theorem restricted_rendezvous_sender_and_receiver_are_distinct :
  forall admitted before after step,
    RendezvousValid admitted before after step ->
    rendezvousSenderProcess step <> rendezvousReceiverProcess step.
Proof.
  intros admitted before after step Hvalid.
  destruct Hvalid as [_ [_ [Hdistinct _]]].
  exact Hdistinct.
Qed.

Inductive SourceCausalEdge : ProcessKey -> ProcessKey -> Prop :=
| CauseLocalOrder :
    forall process,
      SourceCausalEdge process process
| CauseRendezvous :
    forall sender receiver,
      sender <> receiver ->
      SourceCausalEdge sender receiver
| CauseArchitecture :
    forall predecessor successor,
      predecessor <> 0 ->
      successor <> 0 ->
      SourceCausalEdge predecessor successor.

Theorem source_causality_has_only_declared_semantic_origins :
  forall predecessor successor,
    SourceCausalEdge predecessor successor ->
    predecessor = successor \/
    predecessor <> successor \/
    (predecessor <> 0 /\ successor <> 0).
Proof.
  intros predecessor successor Hedge.
  inversion Hedge; subst.
  - left. reflexivity.
  - right. left. assumption.
  - right. right. split; assumption.
Qed.

Definition SchedulerOnlyEdge (_ _ : ProcessKey) : Prop := False.

Theorem scheduler_order_is_not_source_causality :
  forall predecessor successor,
    ~ SchedulerOnlyEdge predecessor successor.
Proof.
  intros predecessor successor Hscheduler.
  exact Hscheduler.
Qed.

(* -------------------------------------------------------------------------- *)
(* CONC-007: process failure is local and cannot fabricate peer progression.   *)
(* -------------------------------------------------------------------------- *)

Inductive ProcessExecutionStatus : Type :=
| ProcessRunning
| ProcessTerminated
| ProcessFailed.

Definition ProcessStatusMap := ProcessKey -> ProcessExecutionStatus.

Record FailureIsolationStep
  (before after : ProcessStatusMap)
  (failed : ProcessKey) : Prop := mkFailureIsolationStep {
  failedProcessWasRunning : before failed = ProcessRunning;
  failedProcessBecomesFailed : after failed = ProcessFailed;
  failureLeavesPeersUnchanged :
    forall peer,
      peer <> failed ->
      after peer = before peer
}.

Theorem process_failure_does_not_cancel_peer :
  forall before after failed peer,
    FailureIsolationStep before after failed ->
    peer <> failed ->
    after peer = before peer.
Proof.
  intros before after failed peer Hstep Hdistinct.
  destruct Hstep as [_ _ Hpeers].
  eapply Hpeers.
  exact Hdistinct.
Qed.

Theorem process_failure_cannot_fabricate_peer_terminal_state :
  forall before after failed peer,
    FailureIsolationStep before after failed ->
    peer <> failed ->
    before peer = ProcessRunning ->
    after peer = ProcessRunning.
Proof.
  intros before after failed peer Hstep Hdistinct Hrunning.
  rewrite (process_failure_does_not_cancel_peer before after failed peer Hstep Hdistinct).
  exact Hrunning.
Qed.

(* -------------------------------------------------------------------------- *)
(* CONC-008: local terminal facts and whole-program terminal/stuck closure.     *)
(* -------------------------------------------------------------------------- *)

Record LocalProcessTerminalFact : Type := mkLocalProcessTerminalFact {
  localTerminalProcess : ProcessKey;
  localTerminalControl : Control;
  localTerminalContext : ResourceContext;
  localTerminalClosure :
    TerminalFlowSuccess localTerminalControl localTerminalContext
}.

Theorem local_terminal_fact_requires_resource_closure :
  forall fact,
    ResourceComplete (localTerminalContext fact).
Proof.
  intros fact.
  destruct fact as [process control context Hterminal].
  simpl.
  eapply terminal_flow_success_requires_resource_complete.
  exact Hterminal.
Qed.

Definition TerminalFactMap := ProcessKey -> option LocalProcessTerminalFact.

Definition RootTerminal
  (population : ProcessPopulation)
  (facts : TerminalFactMap) : Prop :=
  forall occurrence,
    In occurrence population ->
    exists fact,
      facts (staticProcessKey occurrence) = Some fact /\
      localTerminalProcess fact = staticProcessKey occurrence.

Definition NetworkStuck
  (population : ProcessPopulation)
  (facts : TerminalFactMap)
  (enabledTransition : bool) : Prop :=
  ~ RootTerminal population facts /\
  enabledTransition = false.

Theorem root_terminal_requires_every_static_process_fact :
  forall population facts occurrence,
    RootTerminal population facts ->
    In occurrence population ->
    exists fact,
      facts (staticProcessKey occurrence) = Some fact /\
      localTerminalProcess fact = staticProcessKey occurrence.
Proof.
  intros population facts occurrence Hterminal Hin.
  eapply Hterminal.
  exact Hin.
Qed.

Theorem stuck_network_is_not_terminal :
  forall population facts enabledTransition,
    NetworkStuck population facts enabledTransition ->
    ~ RootTerminal population facts.
Proof.
  intros population facts enabledTransition Hstuck.
  destruct Hstuck as [Hnotterminal _].
  exact Hnotterminal.
Qed.

Theorem disabled_transition_does_not_imply_terminal :
  forall population facts,
    ~ RootTerminal population facts ->
    NetworkStuck population facts false.
Proof.
  intros population facts Hnotterminal.
  split.
  - exact Hnotterminal.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* CONC-009: execution mechanism belongs to realization, not source identity.  *)
(* -------------------------------------------------------------------------- *)

Record ConcurrencySemanticRevision : Type := mkConcurrencySemanticRevision {
  concurrencyPopulationRevision : nat;
  concurrencyRendezvousRevision : nat;
  concurrencyOwnershipRevision : nat;
  concurrencyCausalityRevision : nat;
  concurrencyTerminalRevision : nat
}.

Record ConcurrencyExecutionRealizationRevision : Type :=
  mkConcurrencyExecutionRealizationRevision {
    executionSourceConcurrencyRevision : ConcurrencySemanticRevision;
    executionPhysicalMechanismRevision : nat
  }.

Definition deriveConcurrencyExecutionRealization
  (source : ConcurrencySemanticRevision)
  (physicalMechanism : nat) : ConcurrencyExecutionRealizationRevision :=
  {| executionSourceConcurrencyRevision := source;
     executionPhysicalMechanismRevision := physicalMechanism |}.

Theorem physical_execution_choice_preserves_source_concurrency_identity :
  forall source priorMechanism replacementMechanism,
    executionSourceConcurrencyRevision
      (deriveConcurrencyExecutionRealization source priorMechanism) =
    executionSourceConcurrencyRevision
      (deriveConcurrencyExecutionRealization source replacementMechanism).
Proof.
  reflexivity.
Qed.

Theorem physical_execution_change_revises_only_realization :
  forall source priorMechanism replacementMechanism,
    priorMechanism <> replacementMechanism ->
    deriveConcurrencyExecutionRealization source priorMechanism <>
    deriveConcurrencyExecutionRealization source replacementMechanism.
Proof.
  intros source priorMechanism replacementMechanism Hneq Heq.
  apply Hneq.
  exact (f_equal executionPhysicalMechanismRevision Heq).
Qed.

(* Certified PHIL-SYS-GENERIC-001 remains the Systems identity boundary beneath
   concurrency realization.  Concurrency execution choices cannot rekey the
   checked ArchitectureInstance carried by generic lowering. *)
Theorem generic_systems_instance_identity_survives_concurrency_realization :
  forall input context physicalMechanism,
    genericSourceInstanceRevision
      (genericResultSourceRevision
        (lowerGenericSystemsModel input context)) =
    identityInstanceRevision (genericCoreArchitectureInstance input).
Proof.
  intros.
  apply generic_lowering_preserves_exact_architecture_instance_revision.
Qed.

(* -------------------------------------------------------------------------- *)
(* Aggregate safety statement.                                                *)
(* -------------------------------------------------------------------------- *)

Record BoundedConcurrencySafety
  (population : ProcessPopulation)
  (activation : ActivationMap)
  (admitted : MessageAdmission)
  (ownershipBefore ownershipAfter : RestrictedOwnership)
  (rendezvous : RendezvousStep)
  (statusBefore statusAfter : ProcessStatusMap)
  (failed : ProcessKey)
  (terminalFacts : TerminalFactMap) : Prop := mkBoundedConcurrencySafety {
  boundedConcurrencyPopulation :
    StaticPopulationValid population activation;
  boundedConcurrencyRendezvous :
    RendezvousValid admitted ownershipBefore ownershipAfter rendezvous;
  boundedConcurrencyFailureIsolation :
    FailureIsolationStep statusBefore statusAfter failed;
  boundedConcurrencyTerminalFactsCloseLocally :
    forall occurrence fact,
      In occurrence population ->
      terminalFacts (staticProcessKey occurrence) = Some fact ->
      ResourceComplete (localTerminalContext fact)
}.

Theorem bounded_concurrency_safety_preserves_single_owner_transfer_and_failure_isolation :
  forall population activation admitted ownershipBefore ownershipAfter rendezvous
         statusBefore statusAfter failed terminalFacts subject peer,
    BoundedConcurrencySafety
      population activation admitted ownershipBefore ownershipAfter rendezvous
      statusBefore statusAfter failed terminalFacts ->
    rendezvousRestrictedSubject rendezvous = Some subject ->
    peer <> failed ->
    ownershipBefore subject = Some (rendezvousSenderProcess rendezvous) /\
    ownershipAfter subject = Some (rendezvousReceiverProcess rendezvous) /\
    statusAfter peer = statusBefore peer.
Proof.
  intros population activation admitted ownershipBefore ownershipAfter rendezvous
    statusBefore statusAfter failed terminalFacts subject peer Hsafe Hrestricted Hpeer.
  destruct Hsafe as [Hpopulation Hrendezvous Hfailure Hterminal].
  pose proof
    (restricted_rendezvous_transfers_exact_owner
      admitted ownershipBefore ownershipAfter rendezvous subject
      Hrendezvous Hrestricted) as Htransfer.
  destruct Htransfer as [Hbefore Hafter].
  split.
  - exact Hbefore.
  - split.
    + exact Hafter.
    + eapply process_failure_does_not_cancel_peer.
      * exact Hfailure.
      * exact Hpeer.
Qed.
