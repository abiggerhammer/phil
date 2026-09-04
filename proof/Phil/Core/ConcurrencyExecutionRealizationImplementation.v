From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ConcurrencyExecutionRealization.

(*
  Machine-facing decision surface for PHIL-CONC-LOWER-001.

  The Certified execution-realization record has seventeen independent
  preservation fields.  They are grouped only by competent authority here;
  no field is dropped and target scheduler/worker identity is not promoted to
  source semantic identity.
*)

Definition ProcessDecisionRealizationFacts
  (model : ProcessExecutionRealizationModel) : Prop :=
  (forall process,
    realizationSourceProcesses model process = true <->
    exists execution,
      realizationProcessExecutions model process execution = true) /\
  (forall process,
    realizationProcessExecutions model process (PhysicalExecution 0) = false) /\
  (forall execution,
    ExecutionReferenced model execution <->
    exists decision,
      realizationExecutionDecisions model execution = Some decision) /\
  (forall execution decision,
    realizationExecutionDecisions model execution = Some decision ->
    realizationDecisionHasCost model decision = true) /\
  (forall execution decision assumption,
    realizationExecutionDecisions model execution = Some decision ->
    realizationDecisionAssumptions model decision assumption = true ->
    realizationStageAssumptions model assumption = true).

Definition EventCausalityRealizationFacts
  (model : ProcessExecutionRealizationModel) : Prop :=
  (forall event,
    realizationSourceEvents model event = true <->
    exists physicalEvent,
      realizationEventExecutions model event = Some physicalEvent) /\
  (forall event,
    realizationEventExecutions model event <> Some (PhysicalEvent 0)) /\
  (forall first second physicalEvent,
    realizationEventExecutions model first = Some physicalEvent ->
    realizationEventExecutions model second = Some physicalEvent ->
    first = second) /\
  (forall before after physicalBefore physicalAfter,
    realizationSourceCausality model before after = true ->
    realizationEventExecutions model before = Some physicalBefore ->
    realizationEventExecutions model after = Some physicalAfter ->
    realizationPhysicalPath model physicalBefore physicalAfter).

Definition SemanticPreservationRealizationFacts
  (model : ProcessExecutionRealizationModel) : Prop :=
  (forall owner,
    realizationRestrictedOwners model owner =
    realizationSourceRestrictedOwners model owner) /\
  (forall fact,
    realizationFacts model fact = realizationSourceFacts model fact) /\
  (forall fact,
    FactPresent (realizationSourceFacts model) fact ->
    realizationStageFacts model fact = true) /\
  (forall process,
    realizationTerminalFacts model process =
    realizationSourceTerminalFacts model process) /\
  (forall assumption,
    realizationAssumptions model assumption =
    realizationStageAssumptions model assumption).

Definition TraceRealizationFacts
  (model : ProcessExecutionRealizationModel) : Prop :=
  (forall process execution,
    realizationProcessExecutions model process execution = true ->
    realizationProcessExecutionTrace model process execution = true) /\
  (forall event physicalEvent,
    realizationEventExecutions model event = Some physicalEvent ->
    realizationEventExecutionTrace model event physicalEvent = true) /\
  (forall before after,
    realizationPhysicalCausalEdges model before after = true ->
    realizationPhysicalCausalityTrace model before after = true).

Theorem process_execution_realization_grouped :
  forall model,
    ProcessDecisionRealizationFacts model /\
    EventCausalityRealizationFacts model /\
    SemanticPreservationRealizationFacts model /\
    TraceRealizationFacts model <->
    ProcessExecutionRealizationValid model.
Proof.
  intros model.
  split.
  - intros [Hprocess [Hevent [Hsemantic Htrace]]].
    destruct Hprocess as [H1 [H2 [H3 [H4 H5]]]].
    destruct Hevent as [H6 [H7 [H8 H9]]].
    destruct Hsemantic as [H10 [H11 [H12 [H13 H14]]]].
    destruct Htrace as [H15 [H16 H17]].
    constructor; assumption.
  - intros Hvalid.
    destruct Hvalid as
      [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17].
    exact
      (conj
        (conj H1 (conj H2 (conj H3 (conj H4 H5))))
        (conj
          (conj H6 (conj H7 (conj H8 H9)))
          (conj
            (conj H10 (conj H11 (conj H12 (conj H13 H14))))
            (conj H15 (conj H16 H17))))).
Qed.

Definition decideProcessDecisionRealizationByFacts
  (processCoverage noEmptyExecution decisionCoverage costExplicit
   assumptionsDeclared : bool) : bool :=
  andb processCoverage
    (andb noEmptyExecution
      (andb decisionCoverage
        (andb costExplicit assumptionsDeclared))).

Definition decideEventCausalityRealizationByFacts
  (eventCoverage noEmptyEvent eventInjective causalityPreserved : bool) : bool :=
  andb eventCoverage
    (andb noEmptyEvent
      (andb eventInjective causalityPreserved)).

Definition decideSemanticPreservationRealizationByFacts
  (ownersExact factsExact factsDeclared terminalExact assumptionsExact : bool) : bool :=
  andb ownersExact
    (andb factsExact
      (andb factsDeclared
        (andb terminalExact assumptionsExact))).

Definition decideTraceRealizationByFacts
  (processTrace eventTrace causalityTrace : bool) : bool :=
  andb processTrace (andb eventTrace causalityTrace).

Definition decideProcessExecutionRealizationByFacts
  (processDecision eventCausality semanticPreservation traceExplicit : bool) : bool :=
  andb processDecision
    (andb eventCausality
      (andb semanticPreservation traceExplicit)).

Theorem decideProcessDecisionRealizationByFacts_classifies :
  forall model processCoverage noEmptyExecution decisionCoverage costExplicit
         assumptionsDeclared,
    (processCoverage = true <->
      forall process,
        realizationSourceProcesses model process = true <->
        exists execution,
          realizationProcessExecutions model process execution = true) ->
    (noEmptyExecution = true <->
      forall process,
        realizationProcessExecutions model process (PhysicalExecution 0) = false) ->
    (decisionCoverage = true <->
      forall execution,
        ExecutionReferenced model execution <->
        exists decision,
          realizationExecutionDecisions model execution = Some decision) ->
    (costExplicit = true <->
      forall execution decision,
        realizationExecutionDecisions model execution = Some decision ->
        realizationDecisionHasCost model decision = true) ->
    (assumptionsDeclared = true <->
      forall execution decision assumption,
        realizationExecutionDecisions model execution = Some decision ->
        realizationDecisionAssumptions model decision assumption = true ->
        realizationStageAssumptions model assumption = true) ->
    decideProcessDecisionRealizationByFacts
      processCoverage noEmptyExecution decisionCoverage costExplicit
      assumptionsDeclared = true <->
    ProcessDecisionRealizationFacts model.
Proof.
  intros model processCoverage noEmptyExecution decisionCoverage costExplicit
    assumptionsDeclared H1 H2 H3 H4 H5.
  unfold decideProcessDecisionRealizationByFacts,
    ProcessDecisionRealizationFacts.
  repeat rewrite andb_true_iff.
  rewrite H1, H2, H3, H4, H5.
  reflexivity.
Qed.

Theorem decideEventCausalityRealizationByFacts_classifies :
  forall model eventCoverage noEmptyEvent eventInjective causalityPreserved,
    (eventCoverage = true <->
      forall event,
        realizationSourceEvents model event = true <->
        exists physicalEvent,
          realizationEventExecutions model event = Some physicalEvent) ->
    (noEmptyEvent = true <->
      forall event,
        realizationEventExecutions model event <> Some (PhysicalEvent 0)) ->
    (eventInjective = true <->
      forall first second physicalEvent,
        realizationEventExecutions model first = Some physicalEvent ->
        realizationEventExecutions model second = Some physicalEvent ->
        first = second) ->
    (causalityPreserved = true <->
      forall before after physicalBefore physicalAfter,
        realizationSourceCausality model before after = true ->
        realizationEventExecutions model before = Some physicalBefore ->
        realizationEventExecutions model after = Some physicalAfter ->
        realizationPhysicalPath model physicalBefore physicalAfter) ->
    decideEventCausalityRealizationByFacts
      eventCoverage noEmptyEvent eventInjective causalityPreserved = true <->
    EventCausalityRealizationFacts model.
Proof.
  intros model eventCoverage noEmptyEvent eventInjective causalityPreserved
    H1 H2 H3 H4.
  unfold decideEventCausalityRealizationByFacts,
    EventCausalityRealizationFacts.
  repeat rewrite andb_true_iff.
  rewrite H1, H2, H3, H4.
  reflexivity.
Qed.

Theorem decideSemanticPreservationRealizationByFacts_classifies :
  forall model ownersExact factsExact factsDeclared terminalExact assumptionsExact,
    (ownersExact = true <->
      forall owner,
        realizationRestrictedOwners model owner =
        realizationSourceRestrictedOwners model owner) ->
    (factsExact = true <->
      forall fact,
        realizationFacts model fact = realizationSourceFacts model fact) ->
    (factsDeclared = true <->
      forall fact,
        FactPresent (realizationSourceFacts model) fact ->
        realizationStageFacts model fact = true) ->
    (terminalExact = true <->
      forall process,
        realizationTerminalFacts model process =
        realizationSourceTerminalFacts model process) ->
    (assumptionsExact = true <->
      forall assumption,
        realizationAssumptions model assumption =
        realizationStageAssumptions model assumption) ->
    decideSemanticPreservationRealizationByFacts
      ownersExact factsExact factsDeclared terminalExact assumptionsExact = true <->
    SemanticPreservationRealizationFacts model.
Proof.
  intros model ownersExact factsExact factsDeclared terminalExact assumptionsExact
    H1 H2 H3 H4 H5.
  unfold decideSemanticPreservationRealizationByFacts,
    SemanticPreservationRealizationFacts.
  repeat rewrite andb_true_iff.
  rewrite H1, H2, H3, H4, H5.
  reflexivity.
Qed.

Theorem decideTraceRealizationByFacts_classifies :
  forall model processTrace eventTrace causalityTrace,
    (processTrace = true <->
      forall process execution,
        realizationProcessExecutions model process execution = true ->
        realizationProcessExecutionTrace model process execution = true) ->
    (eventTrace = true <->
      forall event physicalEvent,
        realizationEventExecutions model event = Some physicalEvent ->
        realizationEventExecutionTrace model event physicalEvent = true) ->
    (causalityTrace = true <->
      forall before after,
        realizationPhysicalCausalEdges model before after = true ->
        realizationPhysicalCausalityTrace model before after = true) ->
    decideTraceRealizationByFacts processTrace eventTrace causalityTrace = true <->
    TraceRealizationFacts model.
Proof.
  intros model processTrace eventTrace causalityTrace H1 H2 H3.
  unfold decideTraceRealizationByFacts, TraceRealizationFacts.
  repeat rewrite andb_true_iff.
  rewrite H1, H2, H3.
  reflexivity.
Qed.

Theorem decideProcessExecutionRealizationByFacts_classifies :
  forall model processDecision eventCausality semanticPreservation traceExplicit,
    (processDecision = true <-> ProcessDecisionRealizationFacts model) ->
    (eventCausality = true <-> EventCausalityRealizationFacts model) ->
    (semanticPreservation = true <-> SemanticPreservationRealizationFacts model) ->
    (traceExplicit = true <-> TraceRealizationFacts model) ->
    decideProcessExecutionRealizationByFacts
      processDecision eventCausality semanticPreservation traceExplicit = true <->
    ProcessExecutionRealizationValid model.
Proof.
  intros model processDecision eventCausality semanticPreservation traceExplicit
    H1 H2 H3 H4.
  unfold decideProcessExecutionRealizationByFacts.
  repeat rewrite andb_true_iff.
  rewrite H1, H2, H3, H4.
  apply process_execution_realization_grouped.
Qed.
