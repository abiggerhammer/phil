From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import SequentialExecutionOrder.

(*
  PHIL-EXEC-ORDER-001 — finite executable correspondence.

  Production splits the obligation across two bounded authorities:

  - Grammar-v1 local execution produces deterministic source-order traces; and
  - SequentialTrace accepts target projections only when identity/domain/trace
    gates hold and every changed crossing has explicit StageContract evidence.

  The other StageContract effect/resource/failure/authority/observable relations
  remain independently checked.  This boolean layer mirrors that finite gate
  conjunction without reimplementing Haskell list traversal, sorting, Set
  normalization, digest/Text identity, or StageContract serialization.
*)

Definition sequentialRefinementFactsb
  (stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique eventDomainMatches
    traceRelationRecorded crossingsJustified stageSemanticsPreserved : bool)
  : bool :=
  andb stageContractMatches
    (andb sourceArtifactMatches
      (andb targetArtifactMatches
        (andb sourceEventsUnique
          (andb targetEventsUnique
            (andb eventDomainMatches
              (andb traceRelationRecorded
                (andb crossingsJustified stageSemanticsPreserved))))))).

Inductive SequentialRefinementDecision : Type :=
| SequentialRefinementAccepted
| SequentialRefinementRejected.

Definition decideSequentialRefinement
  (stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique eventDomainMatches
    traceRelationRecorded crossingsJustified stageSemanticsPreserved : bool)
  : SequentialRefinementDecision :=
  if sequentialRefinementFactsb
      stageContractMatches sourceArtifactMatches targetArtifactMatches
      sourceEventsUnique targetEventsUnique eventDomainMatches
      traceRelationRecorded crossingsJustified stageSemanticsPreserved
  then SequentialRefinementAccepted
  else SequentialRefinementRejected.

Theorem sequential_refinement_facts_true_iff_all_gates :
  forall stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique eventDomainMatches
    traceRelationRecorded crossingsJustified stageSemanticsPreserved,
    sequentialRefinementFactsb
      stageContractMatches sourceArtifactMatches targetArtifactMatches
      sourceEventsUnique targetEventsUnique eventDomainMatches
      traceRelationRecorded crossingsJustified stageSemanticsPreserved = true <->
    stageContractMatches = true /\
    sourceArtifactMatches = true /\
    targetArtifactMatches = true /\
    sourceEventsUnique = true /\
    targetEventsUnique = true /\
    eventDomainMatches = true /\
    traceRelationRecorded = true /\
    crossingsJustified = true /\
    stageSemanticsPreserved = true.
Proof.
  intros stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique eventDomainMatches
    traceRelationRecorded crossingsJustified stageSemanticsPreserved.
  unfold sequentialRefinementFactsb.
  repeat rewrite andb_true_iff.
  tauto.
Qed.

Theorem sequential_refinement_decision_accept_iff_facts_true :
  forall stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique eventDomainMatches
    traceRelationRecorded crossingsJustified stageSemanticsPreserved,
    decideSequentialRefinement
      stageContractMatches sourceArtifactMatches targetArtifactMatches
      sourceEventsUnique targetEventsUnique eventDomainMatches
      traceRelationRecorded crossingsJustified stageSemanticsPreserved =
      SequentialRefinementAccepted <->
    sequentialRefinementFactsb
      stageContractMatches sourceArtifactMatches targetArtifactMatches
      sourceEventsUnique targetEventsUnique eventDomainMatches
      traceRelationRecorded crossingsJustified stageSemanticsPreserved = true.
Proof.
  intros stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique eventDomainMatches
    traceRelationRecorded crossingsJustified stageSemanticsPreserved.
  unfold decideSequentialRefinement.
  destruct (sequentialRefinementFactsb
    stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique eventDomainMatches
    traceRelationRecorded crossingsJustified stageSemanticsPreserved).
  - split; intros H; reflexivity.
  - split; intros H; discriminate H.
Qed.

Theorem event_domain_drift_rejects_executable_refinement :
  forall stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique traceRelationRecorded
    crossingsJustified stageSemanticsPreserved,
    decideSequentialRefinement
      stageContractMatches sourceArtifactMatches targetArtifactMatches
      sourceEventsUnique targetEventsUnique false
      traceRelationRecorded crossingsJustified stageSemanticsPreserved =
      SequentialRefinementRejected.
Proof.
  intros stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique traceRelationRecorded
    crossingsJustified stageSemanticsPreserved.
  unfold decideSequentialRefinement, sequentialRefinementFactsb.
  destruct stageContractMatches, sourceArtifactMatches, targetArtifactMatches,
    sourceEventsUnique, targetEventsUnique, traceRelationRecorded,
    crossingsJustified, stageSemanticsPreserved; reflexivity.
Qed.

Theorem unproved_crossing_rejects_executable_refinement :
  forall stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique eventDomainMatches
    traceRelationRecorded stageSemanticsPreserved,
    decideSequentialRefinement
      stageContractMatches sourceArtifactMatches targetArtifactMatches
      sourceEventsUnique targetEventsUnique eventDomainMatches
      traceRelationRecorded false stageSemanticsPreserved =
      SequentialRefinementRejected.
Proof.
  intros stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique eventDomainMatches
    traceRelationRecorded stageSemanticsPreserved.
  unfold decideSequentialRefinement, sequentialRefinementFactsb.
  destruct stageContractMatches, sourceArtifactMatches, targetArtifactMatches,
    sourceEventsUnique, targetEventsUnique, eventDomainMatches,
    traceRelationRecorded, stageSemanticsPreserved; reflexivity.
Qed.

Theorem stage_semantics_drift_rejects_executable_refinement :
  forall stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique eventDomainMatches
    traceRelationRecorded crossingsJustified,
    decideSequentialRefinement
      stageContractMatches sourceArtifactMatches targetArtifactMatches
      sourceEventsUnique targetEventsUnique eventDomainMatches
      traceRelationRecorded crossingsJustified false =
      SequentialRefinementRejected.
Proof.
  intros stageContractMatches sourceArtifactMatches targetArtifactMatches
    sourceEventsUnique targetEventsUnique eventDomainMatches
    traceRelationRecorded crossingsJustified.
  unfold decideSequentialRefinement, sequentialRefinementFactsb.
  destruct stageContractMatches, sourceArtifactMatches, targetArtifactMatches,
    sourceEventsUnique, targetEventsUnique, eventDomainMatches,
    traceRelationRecorded, crossingsJustified; reflexivity.
Qed.

Theorem all_exact_sequential_refinement_gates_accept :
  decideSequentialRefinement
    true true true true true true true true true =
    SequentialRefinementAccepted.
Proof.
  reflexivity.
Qed.
