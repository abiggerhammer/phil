From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import
  Syntax
  Context
  ProcessTerminal
  ResourceObligation
  ConcurrencySemantics
  ConcurrencyActivation
  ConcurrencyRendezvous
  ConcurrencyTerminal.

(*
  Machine-facing decision surface for PHIL-CONC-TERM-001.

  The Certified terminal layer has four independent safety authorities:

  - one process can become terminal only after resource/loan, obligation, and
    live-endpoint closure, with Closed/Failed rather than Continue/Return;
  - one fatal process transition changes the actor and leaves every peer's
    complete semantic state unchanged;
  - whole-root terminal closure has exact process facts/statuses and no root
    resource/obligation/observable residue;
  - a still-running network with no valid local/rendezvous semantic step is
    stuck and explicitly nonterminal.

  The extracted ABI reflects those authorities as four grouped Bool gates.
  PHIL-CONC-ACTIVATE-001 and PHIL-CONC-RENDEZVOUS-001 remain predecessor
  authorities; this file does not redefine activation or rendezvous validity.
*)

Definition ProcessTerminalBoundaryFacts
  (process : ProcessKey)
  (control : Control)
  (context : ResourceContext)
  (payload : StatePayload) : Prop :=
  ResourceComplete context /\
  LocalObligationClosure payload /\
  (forall endpoint, ~ LiveEndpoint process endpoint) /\
  ((exists outcome, control = Closed outcome) \/
   (exists failureClass detail,
      control = Failed failureClass detail)).

Definition ExactCertifiedProcessTerminal
  (process : ProcessKey)
  (control : Control)
  (context : ResourceContext)
  (payload : StatePayload) : Prop :=
  exists fact : CertifiedProcessTerminalFact,
    localTerminalProcess (certifiedLocalTerminal fact) = process /\
    localTerminalControl (certifiedLocalTerminal fact) = control /\
    localTerminalContext (certifiedLocalTerminal fact) = context /\
    certifiedTerminalPayload fact = payload.

Theorem process_terminal_boundary_facts_exact :
  forall process control context payload,
    ProcessTerminalBoundaryFacts process control context payload <->
    ExactCertifiedProcessTerminal process control context payload.
Proof.
  intros process control context payload.
  split.
  - intros [Hresource [Hobligations [Hendpoints Hcontrol]]].
    destruct Hcontrol as [[outcome Hclosed] | [failureClass [detail Hfailed]]].
    + subst control.
      exists
        (mkCertifiedProcessTerminalFact
          (mkLocalProcessTerminalFact
            process
            (Closed outcome)
            context
            (resource_complete_allows_closed outcome context Hresource))
          payload
          Hobligations
          Hendpoints).
      repeat split; reflexivity.
    + subst control.
      exists
        (mkCertifiedProcessTerminalFact
          (mkLocalProcessTerminalFact
            process
            (Failed failureClass detail)
            context
            (resource_complete_allows_failed
              failureClass detail context Hresource))
          payload
          Hobligations
          Hendpoints).
      repeat split; reflexivity.
  - intros [fact [Hprocess [Hcontrol [Hcontext Hpayload]]]].
    unfold ProcessTerminalBoundaryFacts.
    refine (conj _ (conj _ (conj _ _))).
    + rewrite <- Hcontext.
      exact (certified_process_terminal_requires_resource_closure fact).
    + rewrite <- Hpayload.
      exact (certifiedTerminalNoPendingObligations fact).
    + rewrite <- Hprocess.
      exact (certifiedTerminalNoLiveEndpoints fact).
    + rewrite <- Hcontrol.
      exact (certified_terminal_control_is_closed_or_failed fact).
Qed.

Definition ExactFailureIsolationFacts
  (before after : PeerSemanticMap)
  (failed : ProcessKey) : Prop :=
  peerExecutionStatus (before failed) = ProcessRunning /\
  peerExecutionStatus (after failed) = ProcessFailed /\
  (forall peer, peer <> failed -> after peer = before peer).

Theorem exact_failure_isolation_facts_exact :
  forall before after failed,
    ExactFailureIsolationFacts before after failed <->
    ExactFailureIsolation before after failed.
Proof.
  intros before after failed.
  split.
  - intros [Hbefore [Hafter Hpeers]].
    constructor; assumption.
  - intros Hfailure.
    destruct Hfailure as [Hbefore Hafter Hpeers].
    unfold ExactFailureIsolationFacts.
    exact (conj Hbefore (conj Hafter Hpeers)).
Qed.

Definition TerminalFactsComplete
  (population : ProcessPopulation)
  (facts : CertifiedTerminalMap) : Prop :=
  forall occurrence,
    In occurrence population ->
    exists fact,
      facts (staticProcessKey occurrence) = Some fact /\
      localTerminalProcess (certifiedLocalTerminal fact) =
        staticProcessKey occurrence.

Definition TerminalFactsNoExtra
  (population : ProcessPopulation)
  (facts : CertifiedTerminalMap) : Prop :=
  forall process fact,
    facts process = Some fact ->
    exists occurrence,
      In occurrence population /\
      staticProcessKey occurrence = process.

Definition CertifiedRootTerminalFacts
  (population : ProcessPopulation)
  (facts : CertifiedTerminalMap)
  (statuses : ProcessStatusMap)
  (root : RootSemanticClosure) : Prop :=
  rootResourcesClosed root = true /\
  rootObligationsClosed root = true /\
  rootObservablesClosed root = true /\
  TerminalFactsComplete population facts /\
  TerminalFactsNoExtra population facts /\
  (forall occurrence,
    In occurrence population ->
    statuses (staticProcessKey occurrence) = ProcessTerminated).

Theorem certified_root_terminal_facts_exact :
  forall population facts statuses root,
    CertifiedRootTerminalFacts population facts statuses root <->
    CertifiedRootTerminal population facts statuses root.
Proof.
  intros population facts statuses root.
  split.
  - intros [Hresources [Hobligations [Hobservables
      [Hcomplete [Hnoextra Hstatuses]]]]].
    unfold CertifiedRootTerminal.
    refine (conj _ (conj _ Hstatuses)).
    + unfold RootSemanticClosed.
      exact (conj Hresources (conj Hobligations Hobservables)).
    + unfold TerminalMapExact.
      exact (conj Hcomplete Hnoextra).
  - intros [Hroot [Hmap Hstatuses]].
    unfold RootSemanticClosed in Hroot.
    destruct Hroot as [Hresources [Hobligations Hobservables]].
    unfold TerminalMapExact in Hmap.
    destruct Hmap as [Hcomplete Hnoextra].
    unfold CertifiedRootTerminalFacts.
    exact
      (conj Hresources
        (conj Hobligations
          (conj Hobservables
            (conj Hcomplete (conj Hnoextra Hstatuses))))).
Qed.

Definition CertifiedNetworkStuckFacts
  (population : ProcessPopulation)
  (facts : CertifiedTerminalMap)
  (statuses : ProcessStatusMap)
  (root : RootSemanticClosure) : Prop :=
  ~ CertifiedRootTerminal population facts statuses root /\
  NetworkHasRunningStaticProcess population statuses /\
  ~ NetworkHasEnabledSemanticStep population.

Theorem certified_network_stuck_facts_exact :
  forall population facts statuses root,
    CertifiedNetworkStuckFacts population facts statuses root <->
    CertifiedNetworkStuck population facts statuses root.
Proof.
  intros population facts statuses root.
  unfold CertifiedNetworkStuckFacts, CertifiedNetworkStuck.
  reflexivity.
Qed.

Definition decideCertifiedProcessTerminalByFacts
  (resourceClosed obligationsClosed endpointsClosed controlTerminal : bool) : bool :=
  andb resourceClosed
    (andb obligationsClosed
      (andb endpointsClosed controlTerminal)).

Definition decideExactFailureIsolationByFacts
  (actorWasRunning actorBecomesFailed peersUnchanged : bool) : bool :=
  andb actorWasRunning
    (andb actorBecomesFailed peersUnchanged).

Definition decideCertifiedRootTerminalByFacts
  (rootResources rootObligations rootObservables
   terminalFactsComplete noInventedTerminalFacts
   allStaticStatusesTerminated : bool) : bool :=
  andb rootResources
    (andb rootObligations
      (andb rootObservables
        (andb terminalFactsComplete
          (andb noInventedTerminalFacts allStaticStatusesTerminated)))).

Definition decideCertifiedNetworkStuckByFacts
  (rootNotTerminal runningStaticProcess noEnabledSemanticStep : bool) : bool :=
  andb rootNotTerminal
    (andb runningStaticProcess noEnabledSemanticStep).

Theorem decideCertifiedProcessTerminalByFacts_classifies :
  forall process control context payload
         resourceClosed obligationsClosed endpointsClosed controlTerminal,
    (resourceClosed = true <-> ResourceComplete context) ->
    (obligationsClosed = true <-> LocalObligationClosure payload) ->
    (endpointsClosed = true <->
      forall endpoint, ~ LiveEndpoint process endpoint) ->
    (controlTerminal = true <->
      (exists outcome, control = Closed outcome) \/
      (exists failureClass detail,
        control = Failed failureClass detail)) ->
    decideCertifiedProcessTerminalByFacts
      resourceClosed obligationsClosed endpointsClosed controlTerminal = true <->
    ExactCertifiedProcessTerminal process control context payload.
Proof.
  intros process control context payload
    resourceClosed obligationsClosed endpointsClosed controlTerminal
    Hresource Hobligations Hendpoints Hcontrol.
  unfold decideCertifiedProcessTerminalByFacts.
  repeat rewrite andb_true_iff.
  rewrite Hresource, Hobligations, Hendpoints, Hcontrol.
  apply process_terminal_boundary_facts_exact.
Qed.

Theorem decideExactFailureIsolationByFacts_classifies :
  forall before after failed actorWasRunning actorBecomesFailed peersUnchanged,
    (actorWasRunning = true <->
      peerExecutionStatus (before failed) = ProcessRunning) ->
    (actorBecomesFailed = true <->
      peerExecutionStatus (after failed) = ProcessFailed) ->
    (peersUnchanged = true <->
      forall peer, peer <> failed -> after peer = before peer) ->
    decideExactFailureIsolationByFacts
      actorWasRunning actorBecomesFailed peersUnchanged = true <->
    ExactFailureIsolation before after failed.
Proof.
  intros before after failed actorWasRunning actorBecomesFailed peersUnchanged
    Hbefore Hafter Hpeers.
  unfold decideExactFailureIsolationByFacts.
  repeat rewrite andb_true_iff.
  rewrite Hbefore, Hafter, Hpeers.
  apply exact_failure_isolation_facts_exact.
Qed.

Theorem decideCertifiedRootTerminalByFacts_classifies :
  forall population facts statuses root
         rootResources rootObligations rootObservables
         terminalFactsComplete noInventedTerminalFacts
         allStaticStatusesTerminated,
    (rootResources = true <-> rootResourcesClosed root = true) ->
    (rootObligations = true <-> rootObligationsClosed root = true) ->
    (rootObservables = true <-> rootObservablesClosed root = true) ->
    (terminalFactsComplete = true <-> TerminalFactsComplete population facts) ->
    (noInventedTerminalFacts = true <-> TerminalFactsNoExtra population facts) ->
    (allStaticStatusesTerminated = true <->
      forall occurrence,
        In occurrence population ->
        statuses (staticProcessKey occurrence) = ProcessTerminated) ->
    decideCertifiedRootTerminalByFacts
      rootResources rootObligations rootObservables
      terminalFactsComplete noInventedTerminalFacts
      allStaticStatusesTerminated = true <->
    CertifiedRootTerminal population facts statuses root.
Proof.
  intros population facts statuses root
    rootResources rootObligations rootObservables
    terminalFactsComplete noInventedTerminalFacts
    allStaticStatusesTerminated
    Hresources Hobligations Hobservables Hcomplete Hnoextra Hstatuses.
  unfold decideCertifiedRootTerminalByFacts.
  repeat rewrite andb_true_iff.
  rewrite Hresources, Hobligations, Hobservables, Hcomplete, Hnoextra, Hstatuses.
  apply certified_root_terminal_facts_exact.
Qed.

Theorem decideCertifiedNetworkStuckByFacts_classifies :
  forall population facts statuses root
         rootNotTerminal runningStaticProcess noEnabledSemanticStep,
    (rootNotTerminal = true <->
      ~ CertifiedRootTerminal population facts statuses root) ->
    (runningStaticProcess = true <->
      NetworkHasRunningStaticProcess population statuses) ->
    (noEnabledSemanticStep = true <->
      ~ NetworkHasEnabledSemanticStep population) ->
    decideCertifiedNetworkStuckByFacts
      rootNotTerminal runningStaticProcess noEnabledSemanticStep = true <->
    CertifiedNetworkStuck population facts statuses root.
Proof.
  intros population facts statuses root
    rootNotTerminal runningStaticProcess noEnabledSemanticStep
    Hnotterminal Hrunning Hdisabled.
  unfold decideCertifiedNetworkStuckByFacts.
  repeat rewrite andb_true_iff.
  rewrite Hnotterminal, Hrunning, Hdisabled.
  apply certified_network_stuck_facts_exact.
Qed.
