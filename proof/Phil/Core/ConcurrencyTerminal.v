From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

From Phil.Core Require Import
  Syntax
  Context
  ProcessJoin
  ProcessTerminal
  ConcurrencySemantics
  ConcurrencyActivation
  ConcurrencyRendezvous.
From Phil.Core Require ResourceObligation.

(*
  PHIL-CONC-TERM-001 — process-local terminal closure, failure isolation,
  all-process root closure, and stuck/nonterminal separation.

  This layer composes the already Certified concurrency population/activation
  and rendezvous semantics with ProcessTerminal resource closure and the
  PHIL-RES-OBL-001 pending-obligation model. It deliberately proves safety
  only: no fairness, deadlock freedom, eventual response, deadline, or physical
  scheduler property is implied.
*)

Definition EndpointOccurrenceKey := nat.
Parameter LiveEndpoint : ProcessKey -> EndpointOccurrenceKey -> Prop.

Definition LocalObligationClosure (payload : StatePayload) : Prop :=
  forall obligation : ResourceObligation.ObligationId,
    ~ ResourceObligation.PendingObligation payload obligation.

Record CertifiedProcessTerminalFact : Type := mkCertifiedProcessTerminalFact {
  certifiedLocalTerminal : LocalProcessTerminalFact;
  certifiedTerminalPayload : StatePayload;
  certifiedTerminalNoPendingObligations :
    LocalObligationClosure certifiedTerminalPayload;
  certifiedTerminalNoLiveEndpoints :
    forall endpoint,
      ~ LiveEndpoint
          (localTerminalProcess certifiedLocalTerminal)
          endpoint
}.

Theorem certified_process_terminal_requires_resource_closure :
  forall fact,
    ResourceComplete
      (localTerminalContext (certifiedLocalTerminal fact)).
Proof.
  intros fact.
  apply local_terminal_fact_requires_resource_closure.
Qed.

Theorem pending_obligation_blocks_certified_process_terminal :
  forall fact obligation,
    ResourceObligation.PendingObligation
      (certifiedTerminalPayload fact) obligation ->
    False.
Proof.
  intros fact obligation Hpending.
  pose proof
    (certifiedTerminalNoPendingObligations fact obligation)
    as Hclosed.
  apply Hclosed.
  exact Hpending.
Qed.

Theorem live_endpoint_blocks_certified_process_terminal :
  forall fact endpoint,
    LiveEndpoint
      (localTerminalProcess (certifiedLocalTerminal fact)) endpoint ->
    False.
Proof.
  intros fact endpoint Hlive.
  pose proof (certifiedTerminalNoLiveEndpoints fact endpoint) as Hclosed.
  apply Hclosed.
  exact Hlive.
Qed.

Theorem certified_terminal_control_is_closed_or_failed :
  forall fact,
    (exists outcome,
      localTerminalControl (certifiedLocalTerminal fact) = Closed outcome) \/
    (exists failureClass detail,
      localTerminalControl (certifiedLocalTerminal fact) =
        Failed failureClass detail).
Proof.
  intros fact.
  destruct (certifiedLocalTerminal fact) as
    [process control context Hterminal].
  simpl.
  inversion Hterminal; subst.
  - left. eexists. reflexivity.
  - right. eexists. eexists. reflexivity.
Qed.

Record PeerSemanticState : Type := mkPeerSemanticState {
  peerExecutionStatus : ProcessExecutionStatus;
  peerEndpointRevision : nat;
  peerCleanupRevision : nat;
  peerOutcomeRevision : nat;
  peerObligationRevision : nat
}.

Definition PeerSemanticMap := ProcessKey -> PeerSemanticState.
Definition peerStatusMap (states : PeerSemanticMap) : ProcessStatusMap :=
  fun process => peerExecutionStatus (states process).

Record ExactFailureIsolation
  (before after : PeerSemanticMap)
  (failed : ProcessKey) : Prop := mkExactFailureIsolation {
  exactFailureActorWasRunning :
    peerExecutionStatus (before failed) = ProcessRunning;
  exactFailureActorBecomesFailed :
    peerExecutionStatus (after failed) = ProcessFailed;
  exactFailurePeersUnchanged :
    forall peer,
      peer <> failed ->
      after peer = before peer
}.

Theorem exact_failure_implies_status_isolation :
  forall (before after : PeerSemanticMap) failed,
    ExactFailureIsolation before after failed ->
    FailureIsolationStep
      (peerStatusMap before)
      (peerStatusMap after)
      failed.
Proof.
  intros before after failed Hfailure.
  constructor.
  - exact (exactFailureActorWasRunning before after failed Hfailure).
  - exact (exactFailureActorBecomesFailed before after failed Hfailure).
  - intros peer Hdistinct.
    unfold peerStatusMap.
    rewrite (exactFailurePeersUnchanged before after failed Hfailure peer Hdistinct).
    reflexivity.
Qed.

Theorem exact_failure_cannot_fabricate_peer_progress :
  forall (before after : PeerSemanticMap) failed peer,
    ExactFailureIsolation before after failed ->
    peer <> failed ->
    peerExecutionStatus (after peer) = peerExecutionStatus (before peer) /\
    peerEndpointRevision (after peer) = peerEndpointRevision (before peer) /\
    peerCleanupRevision (after peer) = peerCleanupRevision (before peer) /\
    peerOutcomeRevision (after peer) = peerOutcomeRevision (before peer) /\
    peerObligationRevision (after peer) = peerObligationRevision (before peer).
Proof.
  intros before after failed peer Hfailure Hdistinct.
  pose proof
    (exactFailurePeersUnchanged before after failed Hfailure peer Hdistinct)
    as Heq.
  rewrite Heq.
  repeat split; reflexivity.
Qed.

Theorem fatal_process_failure_leaves_running_peer_running :
  forall (before after : PeerSemanticMap) failed peer,
    ExactFailureIsolation before after failed ->
    peer <> failed ->
    peerExecutionStatus (before peer) = ProcessRunning ->
    peerExecutionStatus (after peer) = ProcessRunning.
Proof.
  intros before after failed peer Hfailure Hdistinct Hrunning.
  pose proof
    (exact_failure_implies_status_isolation before after failed Hfailure)
    as Hstatus.
  eapply process_failure_cannot_fabricate_peer_terminal_state.
  - exact Hstatus.
  - exact Hdistinct.
  - exact Hrunning.
Qed.

Definition CertifiedTerminalMap :=
  ProcessKey -> option CertifiedProcessTerminalFact.

Definition TerminalMapExact
  (population : ProcessPopulation)
  (facts : CertifiedTerminalMap) : Prop :=
  (forall occurrence,
    In occurrence population ->
    exists fact,
      facts (staticProcessKey occurrence) = Some fact /\
      localTerminalProcess (certifiedLocalTerminal fact) =
        staticProcessKey occurrence) /\
  (forall process fact,
    facts process = Some fact ->
    exists occurrence,
      In occurrence population /\
      staticProcessKey occurrence = process).

Record RootSemanticClosure : Type := mkRootSemanticClosure {
  rootResourcesClosed : bool;
  rootObligationsClosed : bool;
  rootObservablesClosed : bool
}.

Definition RootSemanticClosed (root : RootSemanticClosure) : Prop :=
  rootResourcesClosed root = true /\
  rootObligationsClosed root = true /\
  rootObservablesClosed root = true.

Definition CertifiedRootTerminal
  (population : ProcessPopulation)
  (facts : CertifiedTerminalMap)
  (statuses : ProcessStatusMap)
  (root : RootSemanticClosure) : Prop :=
  RootSemanticClosed root /\
  TerminalMapExact population facts /\
  forall occurrence,
    In occurrence population ->
    statuses (staticProcessKey occurrence) = ProcessTerminated.

Theorem certified_root_terminal_requires_every_static_process_fact :
  forall population facts statuses root occurrence,
    CertifiedRootTerminal population facts statuses root ->
    In occurrence population ->
    exists fact,
      facts (staticProcessKey occurrence) = Some fact /\
      localTerminalProcess (certifiedLocalTerminal fact) =
        staticProcessKey occurrence.
Proof.
  intros population facts statuses root occurrence Hroot Hin.
  destruct Hroot as [_ [Hexact _]].
  destruct Hexact as [Hcomplete _].
  eapply Hcomplete.
  exact Hin.
Qed.

Theorem certified_root_terminal_cannot_invent_external_process_fact :
  forall population facts process fact,
    TerminalMapExact population facts ->
    facts process = Some fact ->
    (forall occurrence, In occurrence population ->
      staticProcessKey occurrence <> process) ->
    False.
Proof.
  intros population facts process fact Hexact Hfact Habsent.
  destruct Hexact as [_ Hnoextra].
  destruct (Hnoextra process fact Hfact) as [occurrence [Hin Hkey]].
  apply (Habsent occurrence Hin).
  exact Hkey.
Qed.

Theorem external_participant_classification_cannot_supply_process_identity :
  forall process,
    ExternalParticipant = InternalParticipant process ->
    False.
Proof.
  intros process Heq.
  apply (external_participant_has_no_internal_process_key process).
  exact Heq.
Qed.

Theorem certified_root_terminal_has_no_running_static_process :
  forall population facts statuses root occurrence,
    CertifiedRootTerminal population facts statuses root ->
    In occurrence population ->
    statuses (staticProcessKey occurrence) <> ProcessRunning.
Proof.
  intros population facts statuses root occurrence Hroot Hin Hrunning.
  destruct Hroot as [_ [_ Hstatuses]].
  pose proof (Hstatuses occurrence Hin) as Hterminal.
  rewrite Hrunning in Hterminal.
  discriminate.
Qed.

Inductive SemanticEnabledStep : Type :=
| EnabledLocalSemanticStep : ProcessKey -> SemanticEnabledStep
| EnabledInternalRendezvousStep :
    DualRendezvousWitness -> SemanticEnabledStep.

Definition SemanticStepValid
  (population : ProcessPopulation)
  (step : SemanticEnabledStep) : Prop :=
  match step with
  | EnabledLocalSemanticStep process =>
      exists occurrence,
        In occurrence population /\
        staticProcessKey occurrence = process
  | EnabledInternalRendezvousStep witness =>
      ExactInternalRendezvous witness
  end.

Definition NetworkHasEnabledSemanticStep
  (population : ProcessPopulation) : Prop :=
  exists step, SemanticStepValid population step.

Definition NetworkHasRunningStaticProcess
  (population : ProcessPopulation)
  (statuses : ProcessStatusMap) : Prop :=
  exists occurrence,
    In occurrence population /\
    statuses (staticProcessKey occurrence) = ProcessRunning.

Definition CertifiedNetworkStuck
  (population : ProcessPopulation)
  (facts : CertifiedTerminalMap)
  (statuses : ProcessStatusMap)
  (root : RootSemanticClosure) : Prop :=
  ~ CertifiedRootTerminal population facts statuses root /\
  NetworkHasRunningStaticProcess population statuses /\
  ~ NetworkHasEnabledSemanticStep population.

Theorem certified_stuck_network_is_not_terminal :
  forall population facts statuses root,
    CertifiedNetworkStuck population facts statuses root ->
    ~ CertifiedRootTerminal population facts statuses root.
Proof.
  intros population facts statuses root Hstuck.
  exact (proj1 Hstuck).
Qed.

Theorem running_without_enabled_local_or_rendezvous_step_is_stuck :
  forall population facts statuses root,
    ~ CertifiedRootTerminal population facts statuses root ->
    NetworkHasRunningStaticProcess population statuses ->
    ~ NetworkHasEnabledSemanticStep population ->
    CertifiedNetworkStuck population facts statuses root.
Proof.
  intros population facts statuses root Hnotterminal Hrunning Hdisabled.
  repeat split; assumption.
Qed.

Theorem certified_root_terminal_and_stuck_are_disjoint :
  forall population facts statuses root,
    CertifiedRootTerminal population facts statuses root ->
    ~ CertifiedNetworkStuck population facts statuses root.
Proof.
  intros population facts statuses root Hterminal Hstuck.
  apply (certified_stuck_network_is_not_terminal
    population facts statuses root Hstuck).
  exact Hterminal.
Qed.

Theorem certified_terminal_layer_reuses_activation_population :
  forall population activation bindings restrictedOwner directStatefulOwner
         expected participants facts statuses root,
    CertifiedConcurrencyActivation
      population activation bindings restrictedOwner directStatefulOwner
      expected participants ->
    CertifiedRootTerminal population facts statuses root ->
    StaticPopulationValid population activation.
Proof.
  intros population activation bindings restrictedOwner directStatefulOwner
    expected participants facts statuses root Hactivation Hroot.
  eapply certified_activation_inherits_exact_static_population.
  exact Hactivation.
Qed.
