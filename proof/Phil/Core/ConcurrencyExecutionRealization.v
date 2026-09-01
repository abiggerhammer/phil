From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  PHIL-CONC-LOWER-001 — execution-realization preservation.

  This normalized theorem models the already implemented CONC-009 relation in
  Phil.Systems.ProcessRealization.  Source ProcessKey / ProcessEvent identity is
  deliberately a different type from physical worker/task/event identity.

  The theorem establishes exact preservation requirements across an otherwise
  many-to-many physical execution mapping:

  - every source process has at least one physical execution realization, and
    no non-source process can appear in the mapping;
  - every source event maps to exactly one nonempty physical event identity and
    distinct source events cannot collapse to one physical event;
  - every source causal edge survives as a physical causal path;
  - restricted ownership, process-scoped effect/authority/failure facts, and
    terminal facts are preserved exactly;
  - every referenced physical execution is justified by exactly one lowering
    decision with explicit cost classification;
  - every execution assumption is declared in the StageContract and the
    realized assumption set is exact;
  - process/event/physical-causality realization entries remain explicit trace
    relations rather than ambient scheduler facts.

  Concrete Haskell Text/Map/Set/list correspondence, construction of ProcessKey
  and ProcessEventKey values, physical path search, lowering-ledger lookup,
  scheduler/IPC/device correctness, and numeric/profile-specific cost remain
  explicit correspondence/realization boundaries.
*)

Inductive SourceProcessKey : Type :=
| SourceProcess : nat -> SourceProcessKey.

Inductive PhysicalExecutionKey : Type :=
| PhysicalExecution : nat -> PhysicalExecutionKey.

Inductive SourceEventKey : Type :=
| SourceEvent : nat -> SourceEventKey.

Inductive PhysicalEventKey : Type :=
| PhysicalEvent : nat -> PhysicalEventKey.

Definition RestrictedOwnerId := nat.
Definition SemanticFactId := nat.
Definition DecisionId := nat.
Definition AssumptionId := nat.

Record ProcessSemanticFact : Type := mkProcessSemanticFact {
  semanticFactProcess : SourceProcessKey;
  semanticFactKind : nat;
  semanticFactPayload : nat
}.

Definition SourceProcessSet := SourceProcessKey -> bool.
Definition ProcessExecutionRelation :=
  SourceProcessKey -> PhysicalExecutionKey -> bool.
Definition SourceEventSet := SourceEventKey -> bool.
Definition EventExecutionMap := SourceEventKey -> option PhysicalEventKey.
Definition PhysicalCausalEdgeSet :=
  PhysicalEventKey -> PhysicalEventKey -> bool.
Definition PhysicalCausalPath :=
  PhysicalEventKey -> PhysicalEventKey -> Prop.
Definition SourceCausalEdgeSet :=
  SourceEventKey -> SourceEventKey -> bool.
Definition RestrictedOwnerEnvironment :=
  RestrictedOwnerId -> option SourceProcessKey.
Definition SemanticFactEnvironment :=
  SemanticFactId -> option ProcessSemanticFact.
Definition TerminalFactEnvironment :=
  SourceProcessKey -> option nat.
Definition ExecutionDecisionEnvironment :=
  PhysicalExecutionKey -> option DecisionId.
Definition DecisionCostEnvironment := DecisionId -> bool.
Definition DecisionAssumptionEnvironment :=
  DecisionId -> AssumptionId -> bool.
Definition AssumptionSet := AssumptionId -> bool.
Definition StageFactSet := SemanticFactId -> bool.
Definition ProcessExecutionTrace :=
  SourceProcessKey -> PhysicalExecutionKey -> bool.
Definition EventExecutionTrace :=
  SourceEventKey -> PhysicalEventKey -> bool.
Definition PhysicalCausalityTrace :=
  PhysicalEventKey -> PhysicalEventKey -> bool.

Record ProcessExecutionRealizationModel : Type :=
  mkProcessExecutionRealizationModel {
    realizationSourceProcesses : SourceProcessSet;
    realizationProcessExecutions : ProcessExecutionRelation;

    realizationSourceEvents : SourceEventSet;
    realizationEventExecutions : EventExecutionMap;
    realizationSourceCausality : SourceCausalEdgeSet;
    realizationPhysicalCausalEdges : PhysicalCausalEdgeSet;
    realizationPhysicalPath : PhysicalCausalPath;

    realizationSourceRestrictedOwners : RestrictedOwnerEnvironment;
    realizationRestrictedOwners : RestrictedOwnerEnvironment;

    realizationSourceFacts : SemanticFactEnvironment;
    realizationFacts : SemanticFactEnvironment;
    realizationStageFacts : StageFactSet;

    realizationSourceTerminalFacts : TerminalFactEnvironment;
    realizationTerminalFacts : TerminalFactEnvironment;

    realizationExecutionDecisions : ExecutionDecisionEnvironment;
    realizationDecisionHasCost : DecisionCostEnvironment;
    realizationDecisionAssumptions : DecisionAssumptionEnvironment;
    realizationStageAssumptions : AssumptionSet;
    realizationAssumptions : AssumptionSet;

    realizationProcessExecutionTrace : ProcessExecutionTrace;
    realizationEventExecutionTrace : EventExecutionTrace;
    realizationPhysicalCausalityTrace : PhysicalCausalityTrace
  }.

Definition ExecutionReferenced
  (model : ProcessExecutionRealizationModel)
  (execution : PhysicalExecutionKey) : Prop :=
  exists process,
    realizationProcessExecutions model process execution = true.

Definition FactPresent
  (facts : SemanticFactEnvironment)
  (fact : SemanticFactId) : Prop :=
  exists value, facts fact = Some value.

Record ProcessExecutionRealizationValid
  (model : ProcessExecutionRealizationModel) : Prop :=
  mkProcessExecutionRealizationValid {
    processRealizationCoverageExact :
      forall process,
        realizationSourceProcesses model process = true <->
        exists execution,
          realizationProcessExecutions model process execution = true;

    processRealizationNoEmptyExecutionId :
      forall process,
        realizationProcessExecutions model process (PhysicalExecution 0) = false;

    processExecutionDecisionCoverageExact :
      forall execution,
        ExecutionReferenced model execution <->
        exists decision,
          realizationExecutionDecisions model execution = Some decision;

    processExecutionDecisionCostExplicit :
      forall execution decision,
        realizationExecutionDecisions model execution = Some decision ->
        realizationDecisionHasCost model decision = true;

    processExecutionAssumptionsDeclared :
      forall execution decision assumption,
        realizationExecutionDecisions model execution = Some decision ->
        realizationDecisionAssumptions model decision assumption = true ->
        realizationStageAssumptions model assumption = true;

    processEventCoverageExact :
      forall event,
        realizationSourceEvents model event = true <->
        exists physicalEvent,
          realizationEventExecutions model event = Some physicalEvent;

    processEventNoEmptyPhysicalIdentity :
      forall event,
        realizationEventExecutions model event <> Some (PhysicalEvent 0);

    processEventPhysicalIdentityInjective :
      forall first second physicalEvent,
        realizationEventExecutions model first = Some physicalEvent ->
        realizationEventExecutions model second = Some physicalEvent ->
        first = second;

    processSourceCausalityPreserved :
      forall before after physicalBefore physicalAfter,
        realizationSourceCausality model before after = true ->
        realizationEventExecutions model before = Some physicalBefore ->
        realizationEventExecutions model after = Some physicalAfter ->
        realizationPhysicalPath model physicalBefore physicalAfter;

    processRestrictedOwnersExact :
      forall owner,
        realizationRestrictedOwners model owner =
        realizationSourceRestrictedOwners model owner;

    processSemanticFactsExact :
      forall fact,
        realizationFacts model fact = realizationSourceFacts model fact;

    processSemanticFactsDeclaredInStage :
      forall fact,
        FactPresent (realizationSourceFacts model) fact ->
        realizationStageFacts model fact = true;

    processTerminalFactsExact :
      forall process,
        realizationTerminalFacts model process =
        realizationSourceTerminalFacts model process;

    processRealizationAssumptionsExact :
      forall assumption,
        realizationAssumptions model assumption =
        realizationStageAssumptions model assumption;

    processExecutionTraceExplicit :
      forall process execution,
        realizationProcessExecutions model process execution = true ->
        realizationProcessExecutionTrace model process execution = true;

    processEventTraceExplicit :
      forall event physicalEvent,
        realizationEventExecutions model event = Some physicalEvent ->
        realizationEventExecutionTrace model event physicalEvent = true;

    processPhysicalCausalityTraceExplicit :
      forall before after,
        realizationPhysicalCausalEdges model before after = true ->
        realizationPhysicalCausalityTrace model before after = true
  }.

Theorem every_source_process_has_a_physical_execution :
  forall model process,
    ProcessExecutionRealizationValid model ->
    realizationSourceProcesses model process = true ->
    exists execution,
      realizationProcessExecutions model process execution = true.
Proof.
  intros model process Hvalid Hsource.
  destruct Hvalid as [Hcoverage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  apply (proj1 (Hcoverage process)).
  exact Hsource.
Qed.

Theorem non_source_process_cannot_acquire_a_physical_execution :
  forall model process execution,
    ProcessExecutionRealizationValid model ->
    realizationSourceProcesses model process = false ->
    realizationProcessExecutions model process execution = false.
Proof.
  intros model process execution Hvalid HnotSource.
  destruct Hvalid as [Hcoverage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  destruct (realizationProcessExecutions model process execution) eqn:Hexecution.
  - assert (realizationSourceProcesses model process = true) as Hsource.
    + apply (proj2 (Hcoverage process)).
      exists execution.
      exact Hexecution.
    + rewrite HnotSource in Hsource.
      discriminate.
  - reflexivity.
Qed.

Theorem physical_execution_requires_exact_cost_bearing_decision :
  forall model execution,
    ProcessExecutionRealizationValid model ->
    ExecutionReferenced model execution ->
    exists decision,
      realizationExecutionDecisions model execution = Some decision /\
      realizationDecisionHasCost model decision = true.
Proof.
  intros model execution Hvalid Hreferenced.
  destruct Hvalid as [_ _ Hcoverage Hcost _ _ _ _ _ _ _ _ _ _ _ _ _].
  apply (proj1 (Hcoverage execution)) in Hreferenced.
  destruct Hreferenced as [decision Hdecision].
  exists decision.
  split.
  - exact Hdecision.
  - eapply Hcost.
    exact Hdecision.
Qed.

Theorem hidden_execution_assumption_cannot_certify :
  forall model execution decision assumption,
    realizationExecutionDecisions model execution = Some decision ->
    realizationDecisionAssumptions model decision assumption = true ->
    realizationStageAssumptions model assumption = false ->
    ~ ProcessExecutionRealizationValid model.
Proof.
  intros model execution decision assumption Hdecision Hassumption Hhidden Hvalid.
  destruct Hvalid as [_ _ _ _ Hdeclared _ _ _ _ _ _ _ _ _ _ _ _].
  pose proof
    (Hdeclared execution decision assumption Hdecision Hassumption)
    as Hstage.
  rewrite Hhidden in Hstage.
  discriminate.
Qed.

Theorem source_event_mapping_is_functional :
  forall model event first second,
    realizationEventExecutions model event = Some first ->
    realizationEventExecutions model event = Some second ->
    first = second.
Proof.
  intros model event first second Hfirst Hsecond.
  rewrite Hfirst in Hsecond.
  inversion Hsecond.
  reflexivity.
Qed.

Theorem distinct_source_events_cannot_collapse_to_one_physical_event :
  forall model first second physicalEvent,
    ProcessExecutionRealizationValid model ->
    first <> second ->
    realizationEventExecutions model first = Some physicalEvent ->
    realizationEventExecutions model second = Some physicalEvent ->
    False.
Proof.
  intros model first second physicalEvent Hvalid Hdistinct Hfirst Hsecond.
  destruct Hvalid as [_ _ _ _ _ _ _ Hinjective _ _ _ _ _ _ _ _ _].
  apply Hdistinct.
  eapply Hinjective; eauto.
Qed.

Theorem source_causality_survives_as_physical_path :
  forall model before after physicalBefore physicalAfter,
    ProcessExecutionRealizationValid model ->
    realizationSourceCausality model before after = true ->
    realizationEventExecutions model before = Some physicalBefore ->
    realizationEventExecutions model after = Some physicalAfter ->
    realizationPhysicalPath model physicalBefore physicalAfter.
Proof.
  intros model before after physicalBefore physicalAfter
    Hvalid Hcausal Hbefore Hafter.
  destruct Hvalid as [_ _ _ _ _ _ _ _ Hpreserved _ _ _ _ _ _ _ _].
  eapply Hpreserved; eauto.
Qed.

Theorem restricted_ownership_is_preserved_exactly :
  forall model owner,
    ProcessExecutionRealizationValid model ->
    realizationRestrictedOwners model owner =
    realizationSourceRestrictedOwners model owner.
Proof.
  intros model owner Hvalid.
  destruct Hvalid as [_ _ _ _ _ _ _ _ _ Howners _ _ _ _ _ _ _].
  apply Howners.
Qed.

Theorem process_scoped_semantic_facts_are_preserved_exactly :
  forall model fact,
    ProcessExecutionRealizationValid model ->
    realizationFacts model fact = realizationSourceFacts model fact.
Proof.
  intros model fact Hvalid.
  destruct Hvalid as [_ _ _ _ _ _ _ _ _ _ Hfacts _ _ _ _ _ _].
  apply Hfacts.
Qed.

Theorem source_process_fact_must_remain_declared_in_stage_contract :
  forall model fact,
    ProcessExecutionRealizationValid model ->
    FactPresent (realizationSourceFacts model) fact ->
    realizationStageFacts model fact = true.
Proof.
  intros model fact Hvalid Hpresent.
  destruct Hvalid as [_ _ _ _ _ _ _ _ _ _ _ Hdeclared _ _ _ _ _].
  eapply Hdeclared.
  exact Hpresent.
Qed.

Theorem one_physical_worker_completion_cannot_replace_process_terminal_facts :
  forall model process,
    ProcessExecutionRealizationValid model ->
    realizationTerminalFacts model process =
    realizationSourceTerminalFacts model process.
Proof.
  intros model process Hvalid.
  destruct Hvalid as [_ _ _ _ _ _ _ _ _ _ _ _ Hterminal _ _ _ _].
  apply Hterminal.
Qed.

Theorem realization_assumptions_are_exact_stage_assumptions :
  forall model assumption,
    ProcessExecutionRealizationValid model ->
    realizationAssumptions model assumption =
    realizationStageAssumptions model assumption.
Proof.
  intros model assumption Hvalid.
  destruct Hvalid as [_ _ _ _ _ _ _ _ _ _ _ _ _ Hassumptions _ _ _].
  apply Hassumptions.
Qed.

Theorem process_realization_entries_are_explicitly_trace_bound :
  forall model process execution event physicalEvent before after,
    ProcessExecutionRealizationValid model ->
    realizationProcessExecutions model process execution = true ->
    realizationEventExecutions model event = Some physicalEvent ->
    realizationPhysicalCausalEdges model before after = true ->
    realizationProcessExecutionTrace model process execution = true /\
    realizationEventExecutionTrace model event physicalEvent = true /\
    realizationPhysicalCausalityTrace model before after = true.
Proof.
  intros model process execution event physicalEvent before after
    Hvalid Hprocess Hevent Hedge.
  destruct Hvalid as
    [_ _ _ _ _ _ _ _ _ _ _ _ _ _ HprocessTrace HeventTrace HedgeTrace].
  split.
  - eapply HprocessTrace.
    exact Hprocess.
  - split.
    + eapply HeventTrace.
      exact Hevent.
    + eapply HedgeTrace.
      exact Hedge.
Qed.

(* Many-to-many physical realization is permitted by construction: there is no
   uniqueness premise from ProcessKey to PhysicalExecutionKey or vice versa.
   These preservation lemmas show that such sharing/splitting never authorizes
   process-identity collapse. *)
Theorem shared_worker_does_not_collapse_distinct_processes :
  forall model first second worker,
    first <> second ->
    realizationProcessExecutions model first worker = true ->
    realizationProcessExecutions model second worker = true ->
    first <> second.
Proof.
  intros model first second worker Hdistinct Hfirst Hsecond.
  exact Hdistinct.
Qed.

Theorem split_process_does_not_collapse_distinct_executions :
  forall model process first second,
    first <> second ->
    realizationProcessExecutions model process first = true ->
    realizationProcessExecutions model process second = true ->
    first <> second.
Proof.
  intros model process first second Hdistinct Hfirst Hsecond.
  exact Hdistinct.
Qed.

Theorem concurrency_execution_realization_preserves_exact_source_semantics :
  forall model,
    ProcessExecutionRealizationValid model ->
    (forall process,
      realizationSourceProcesses model process = true ->
      exists execution,
        realizationProcessExecutions model process execution = true) /\
    (forall owner,
      realizationRestrictedOwners model owner =
      realizationSourceRestrictedOwners model owner) /\
    (forall fact,
      realizationFacts model fact = realizationSourceFacts model fact) /\
    (forall process,
      realizationTerminalFacts model process =
      realizationSourceTerminalFacts model process) /\
    (forall assumption,
      realizationAssumptions model assumption =
      realizationStageAssumptions model assumption).
Proof.
  intros model Hvalid.
  split.
  - intros process Hsource.
    eapply every_source_process_has_a_physical_execution; eauto.
  - split.
    + intros owner.
      eapply restricted_ownership_is_preserved_exactly; eauto.
    + split.
      * intros fact.
        eapply process_scoped_semantic_facts_are_preserved_exactly; eauto.
      * split.
        -- intros process.
           eapply one_physical_worker_completion_cannot_replace_process_terminal_facts; eauto.
        -- intros assumption.
           eapply realization_assumptions_are_exact_stage_assumptions; eauto.
Qed.
