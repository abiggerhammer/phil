From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import ResourceJoin ResourceInvariant.

Definition InvariantPredecessorsDistinct
  (predecessors : list InvariantPredecessor) : Prop :=
  NoDup predecessors.

Definition InvariantBoundaryStructuralFacts
  (succession : SuccessionEvidence)
  (predecessors : list InvariantPredecessor) : Prop :=
  forall predecessor,
    In predecessor predecessors ->
    ResourceProjectionSuccess
      succession
      (invariantPredecessorProjection predecessor).

Definition InvariantBoundaryWitnessFacts
  (predecessors : list InvariantPredecessor) : Prop :=
  forall predecessor,
    In predecessor predecessors ->
    ExactInvariantWitnessDomain predecessor.

Definition InvariantBoundaryEstablishedFacts
  (predecessors : list InvariantPredecessor) : Prop :=
  forall predecessor,
    In predecessor predecessors ->
    ExactInvariantEstablished predecessor.

Theorem invariant_boundary_success_is_exact_facts :
  forall succession predecessors,
    InvariantBoundarySuccess succession predecessors <->
    InvariantPredecessorsDistinct predecessors /\
    InvariantBoundaryStructuralFacts succession predecessors /\
    InvariantBoundaryWitnessFacts predecessors /\
    InvariantBoundaryEstablishedFacts predecessors.
Proof.
  intros succession predecessors.
  split.
  - intro Hsuccess.
    destruct Hsuccess as [Hdistinct Hstructural Hwitnesses Hestablished].
    split.
    + exact Hdistinct.
    + split.
      * exact Hstructural.
      * split.
        -- exact Hwitnesses.
        -- exact Hestablished.
  - intros [Hdistinct [Hstructural [Hwitnesses Hestablished]]].
    constructor.
    + exact Hdistinct.
    + exact Hstructural.
    + exact Hwitnesses.
    + exact Hestablished.
Qed.

Inductive InvariantBoundaryDecision : Type :=
| InvariantBoundaryAcceptedDecision
| InvariantBoundaryDuplicatePredecessorDecision
| InvariantBoundaryStructuralDecision
| InvariantBoundaryWitnessDomainDecision
| InvariantBoundaryEstablishmentDecision.

Definition decideInvariantBoundaryByFacts
  (predecessorsDistinct structuralAccepted witnessesExact invariantEstablished : bool)
  : InvariantBoundaryDecision :=
  if predecessorsDistinct then
    if structuralAccepted then
      if witnessesExact then
        if invariantEstablished then
          InvariantBoundaryAcceptedDecision
        else
          InvariantBoundaryEstablishmentDecision
      else
        InvariantBoundaryWitnessDomainDecision
    else
      InvariantBoundaryStructuralDecision
  else
    InvariantBoundaryDuplicatePredecessorDecision.

Theorem invariant_boundary_accepted_implies_distinct :
  forall predecessorsDistinct structuralAccepted witnessesExact invariantEstablished,
    decideInvariantBoundaryByFacts
      predecessorsDistinct structuralAccepted witnessesExact invariantEstablished =
      InvariantBoundaryAcceptedDecision ->
    predecessorsDistinct = true.
Proof.
  intros predecessorsDistinct structuralAccepted witnessesExact invariantEstablished Hdecision.
  destruct predecessorsDistinct.
  - reflexivity.
  - simpl in Hdecision. discriminate.
Qed.

Theorem invariant_boundary_accepted_implies_structural :
  forall predecessorsDistinct structuralAccepted witnessesExact invariantEstablished,
    decideInvariantBoundaryByFacts
      predecessorsDistinct structuralAccepted witnessesExact invariantEstablished =
      InvariantBoundaryAcceptedDecision ->
    structuralAccepted = true.
Proof.
  intros predecessorsDistinct structuralAccepted witnessesExact invariantEstablished Hdecision.
  destruct predecessorsDistinct.
  - destruct structuralAccepted.
    + reflexivity.
    + simpl in Hdecision. discriminate.
  - simpl in Hdecision. discriminate.
Qed.

Theorem invariant_boundary_accepted_implies_witnesses :
  forall predecessorsDistinct structuralAccepted witnessesExact invariantEstablished,
    decideInvariantBoundaryByFacts
      predecessorsDistinct structuralAccepted witnessesExact invariantEstablished =
      InvariantBoundaryAcceptedDecision ->
    witnessesExact = true.
Proof.
  intros predecessorsDistinct structuralAccepted witnessesExact invariantEstablished Hdecision.
  destruct predecessorsDistinct.
  - destruct structuralAccepted.
    + destruct witnessesExact.
      * reflexivity.
      * simpl in Hdecision. discriminate.
    + simpl in Hdecision. discriminate.
  - simpl in Hdecision. discriminate.
Qed.

Theorem invariant_boundary_accepted_implies_established :
  forall predecessorsDistinct structuralAccepted witnessesExact invariantEstablished,
    decideInvariantBoundaryByFacts
      predecessorsDistinct structuralAccepted witnessesExact invariantEstablished =
      InvariantBoundaryAcceptedDecision ->
    invariantEstablished = true.
Proof.
  intros predecessorsDistinct structuralAccepted witnessesExact invariantEstablished Hdecision.
  destruct predecessorsDistinct.
  - destruct structuralAccepted.
    + destruct witnessesExact.
      * destruct invariantEstablished.
        -- reflexivity.
        -- simpl in Hdecision. discriminate.
      * simpl in Hdecision. discriminate.
    + simpl in Hdecision. discriminate.
  - simpl in Hdecision. discriminate.
Qed.

Theorem invariant_boundary_all_facts_accept :
  forall predecessorsDistinct structuralAccepted witnessesExact invariantEstablished,
    predecessorsDistinct = true ->
    structuralAccepted = true ->
    witnessesExact = true ->
    invariantEstablished = true ->
    decideInvariantBoundaryByFacts
      predecessorsDistinct structuralAccepted witnessesExact invariantEstablished =
      InvariantBoundaryAcceptedDecision.
Proof.
  intros predecessorsDistinct structuralAccepted witnessesExact invariantEstablished
    Hdistinct Hstructural Hwitnesses Hestablished.
  rewrite Hdistinct, Hstructural, Hwitnesses, Hestablished.
  reflexivity.
Qed.

Theorem invariant_boundary_decision_corresponds_success :
  forall succession predecessors
    predecessorsDistinct structuralAccepted witnessesExact invariantEstablished,
    (predecessorsDistinct = true <->
      InvariantPredecessorsDistinct predecessors) ->
    (structuralAccepted = true <->
      InvariantBoundaryStructuralFacts succession predecessors) ->
    (witnessesExact = true <->
      InvariantBoundaryWitnessFacts predecessors) ->
    (invariantEstablished = true <->
      InvariantBoundaryEstablishedFacts predecessors) ->
    (decideInvariantBoundaryByFacts
       predecessorsDistinct structuralAccepted witnessesExact invariantEstablished =
       InvariantBoundaryAcceptedDecision <->
     InvariantBoundarySuccess succession predecessors).
Proof.
  intros succession predecessors
    predecessorsDistinct structuralAccepted witnessesExact invariantEstablished
    Hdistinct Hstructural Hwitnesses Hestablished.
  split.
  - intro Hdecision.
    apply (proj2 (invariant_boundary_success_is_exact_facts succession predecessors)).
    split.
    + exact ((proj1 Hdistinct)
        (invariant_boundary_accepted_implies_distinct
          predecessorsDistinct structuralAccepted witnessesExact invariantEstablished
          Hdecision)).
    + split.
      * exact ((proj1 Hstructural)
          (invariant_boundary_accepted_implies_structural
            predecessorsDistinct structuralAccepted witnessesExact invariantEstablished
            Hdecision)).
      * split.
        -- exact ((proj1 Hwitnesses)
            (invariant_boundary_accepted_implies_witnesses
              predecessorsDistinct structuralAccepted witnessesExact invariantEstablished
              Hdecision)).
        -- exact ((proj1 Hestablished)
            (invariant_boundary_accepted_implies_established
              predecessorsDistinct structuralAccepted witnessesExact invariantEstablished
              Hdecision)).
  - intro Hsuccess.
    pose proof
      ((proj1 (invariant_boundary_success_is_exact_facts succession predecessors))
        Hsuccess)
      as [Pdistinct [Pstructural [Pwitnesses Pestablished]]].
    apply invariant_boundary_all_facts_accept.
    + exact ((proj2 Hdistinct) Pdistinct).
    + exact ((proj2 Hstructural) Pstructural).
    + exact ((proj2 Hwitnesses) Pwitnesses).
    + exact ((proj2 Hestablished) Pestablished).
Qed.
