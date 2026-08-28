From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import CallableLifecycle.

(*
  Executable correspondence layer for PHIL-CALL-LIFE-001.

  Concrete callable/capture identities and Map/Set representation stay outside
  this kernel. Production supplies native equality, emptiness, presence, and
  freshness facts; the extracted decisions own the ordered lifecycle result.
*)

Inductive CallablePreserveDecision : Type :=
| CallablePreserveAccepted
| CallablePreserveResidueMismatch
| CallablePreserveProducedSuccessor.

Definition decideCallablePreserve
  (residueMatches successorAbsent : bool)
  : CallablePreserveDecision :=
  if residueMatches
  then if successorAbsent
       then CallablePreserveAccepted
       else CallablePreserveProducedSuccessor
  else CallablePreserveResidueMismatch.

Theorem preserve_decision_accepts_iff_facts :
  forall residueMatches successorAbsent,
    decideCallablePreserve residueMatches successorAbsent =
      CallablePreserveAccepted <->
    residueMatches = true /\ successorAbsent = true.
Proof.
  intros residueMatches successorAbsent.
  destruct residueMatches, successorAbsent; cbn; split; intro H.
  - split; reflexivity.
  - reflexivity.
  - discriminate.
  - destruct H as [_ H]. discriminate.
  - discriminate.
  - destruct H as [H _]. discriminate.
  - discriminate.
  - destruct H as [H _]. discriminate.
Qed.

Theorem preserve_decision_accepts_iff_certified :
  forall expected actual successor residueMatches successorAbsent,
    (residueMatches = true <-> sameCaptureSet expected actual) ->
    (successorAbsent = true <-> successor = None) ->
    (decideCallablePreserve residueMatches successorAbsent =
       CallablePreserveAccepted <->
     preserveTransitionValid expected actual successor).
Proof.
  intros expected actual successor residueMatches successorAbsent
    Hresidue Hsuccessor.
  split.
  - intro Hdecision.
    apply (proj1
      (preserve_decision_accepts_iff_facts
        residueMatches successorAbsent)) in Hdecision.
    destruct Hdecision as [Hmatches Habsent].
    unfold preserveTransitionValid.
    split.
    + apply (proj1 Hresidue). exact Hmatches.
    + apply (proj1 Hsuccessor). exact Habsent.
  - intro Hvalid.
    unfold preserveTransitionValid in Hvalid.
    destruct Hvalid as [Hmatches Habsent].
    apply (proj2
      (preserve_decision_accepts_iff_facts
        residueMatches successorAbsent)).
    split.
    + apply (proj2 Hresidue). exact Hmatches.
    + apply (proj2 Hsuccessor). exact Habsent.
Qed.

Theorem preserve_residue_mismatch_precedes_successor :
  forall successorAbsent,
    decideCallablePreserve false successorAbsent =
      CallablePreserveResidueMismatch.
Proof.
  intros successorAbsent.
  reflexivity.
Qed.

Inductive CallableConsumeDecision : Type :=
| CallableConsumeAccepted
| CallableConsumeRetainedResidue
| CallableConsumeProducedSuccessor.

Definition decideCallableConsume
  (residueEmpty successorAbsent : bool)
  : CallableConsumeDecision :=
  if residueEmpty
  then if successorAbsent
       then CallableConsumeAccepted
       else CallableConsumeProducedSuccessor
  else CallableConsumeRetainedResidue.

Theorem consume_decision_accepts_iff_facts :
  forall residueEmpty successorAbsent,
    decideCallableConsume residueEmpty successorAbsent =
      CallableConsumeAccepted <->
    residueEmpty = true /\ successorAbsent = true.
Proof.
  intros residueEmpty successorAbsent.
  destruct residueEmpty, successorAbsent; cbn; split; intro H.
  - split; reflexivity.
  - reflexivity.
  - discriminate.
  - destruct H as [_ H]. discriminate.
  - discriminate.
  - destruct H as [H _]. discriminate.
  - discriminate.
  - destruct H as [H _]. discriminate.
Qed.

Theorem consume_decision_accepts_iff_certified :
  forall actual successor residueEmpty successorAbsent,
    (residueEmpty = true <-> captureSetEmpty actual) ->
    (successorAbsent = true <-> successor = None) ->
    (decideCallableConsume residueEmpty successorAbsent =
       CallableConsumeAccepted <->
     consumeTransitionValid actual successor).
Proof.
  intros actual successor residueEmpty successorAbsent
    Hresidue Hsuccessor.
  split.
  - intro Hdecision.
    apply (proj1
      (consume_decision_accepts_iff_facts
        residueEmpty successorAbsent)) in Hdecision.
    destruct Hdecision as [Hempty Habsent].
    unfold consumeTransitionValid.
    split.
    + apply (proj1 Hresidue). exact Hempty.
    + apply (proj1 Hsuccessor). exact Habsent.
  - intro Hvalid.
    unfold consumeTransitionValid in Hvalid.
    destruct Hvalid as [Hempty Habsent].
    apply (proj2
      (consume_decision_accepts_iff_facts
        residueEmpty successorAbsent)).
    split.
    + apply (proj2 Hresidue). exact Hempty.
    + apply (proj2 Hsuccessor). exact Habsent.
Qed.

Theorem consume_retained_residue_precedes_successor :
  forall successorAbsent,
    decideCallableConsume false successorAbsent =
      CallableConsumeRetainedResidue.
Proof.
  intros successorAbsent.
  reflexivity.
Qed.

Inductive CallableReplaceDecision : Type :=
| CallableReplaceAccepted
| CallableReplaceRetainedResidue
| CallableReplaceMissingSuccessor
| CallableReplaceReusedPredecessor
| CallableReplaceSuccessorAlreadyAvailable
| CallableReplaceInterfaceMismatch
| CallableReplaceStateMismatch.

Definition decideCallableReplace
  (residueEmpty successorPresent successorDistinct successorFresh
    interfaceMatches stateMatches : bool)
  : CallableReplaceDecision :=
  if residueEmpty then
    if successorPresent then
      if successorDistinct then
        if successorFresh then
          if interfaceMatches then
            if stateMatches
            then CallableReplaceAccepted
            else CallableReplaceStateMismatch
          else CallableReplaceInterfaceMismatch
        else CallableReplaceSuccessorAlreadyAvailable
      else CallableReplaceReusedPredecessor
    else CallableReplaceMissingSuccessor
  else CallableReplaceRetainedResidue.

Theorem replace_decision_accepts_iff_facts :
  forall residueEmpty successorPresent successorDistinct successorFresh
      interfaceMatches stateMatches,
    decideCallableReplace
      residueEmpty successorPresent successorDistinct successorFresh
      interfaceMatches stateMatches = CallableReplaceAccepted <->
    residueEmpty = true /\
    successorPresent = true /\
    successorDistinct = true /\
    successorFresh = true /\
    interfaceMatches = true /\
    stateMatches = true.
Proof.
  intros residueEmpty successorPresent successorDistinct successorFresh
    interfaceMatches stateMatches.
  destruct residueEmpty, successorPresent, successorDistinct, successorFresh,
    interfaceMatches, stateMatches; cbn; split; intro H;
    repeat match goal with
    | Hconj : _ /\ _ |- _ => destruct Hconj
    end;
    try discriminate;
    repeat split; reflexivity.
Qed.

Theorem replace_some_decision_accepts_iff_certified :
  forall predecessor state expectedInterface expectedState actual successor
      residueEmpty successorDistinct successorFresh interfaceMatches stateMatches,
    (residueEmpty = true <-> captureSetEmpty actual) ->
    (successorDistinct = true <->
      successorOccurrence successor <> predecessor) ->
    (successorFresh = true <->
      state (successorOccurrence successor) = false) ->
    (interfaceMatches = true <->
      successorInterface successor = expectedInterface) ->
    (stateMatches = true <->
      successorState successor = expectedState) ->
    (decideCallableReplace
      residueEmpty true successorDistinct successorFresh
      interfaceMatches stateMatches = CallableReplaceAccepted <->
     replaceTransitionValid
      predecessor state expectedInterface expectedState actual (Some successor)).
Proof.
  intros predecessor state expectedInterface expectedState actual successor
    residueEmpty successorDistinct successorFresh interfaceMatches stateMatches
    Hempty Hdistinct Hfresh Hinterface Hstate.
  split.
  - intro Hdecision.
    apply (proj1
      (replace_decision_accepts_iff_facts
        residueEmpty true successorDistinct successorFresh
        interfaceMatches stateMatches)) in Hdecision.
    destruct Hdecision as
      [HemptyFact [_ [HdistinctFact [HfreshFact [HinterfaceFact HstateFact]]]]].
    unfold replaceTransitionValid.
    split.
    + apply (proj1 Hempty). exact HemptyFact.
    + exists successor.
      split.
      * reflexivity.
      * split.
        -- apply (proj1 Hdistinct). exact HdistinctFact.
        -- split.
           ++ apply (proj1 Hfresh). exact HfreshFact.
           ++ split.
              ** apply (proj1 Hinterface). exact HinterfaceFact.
              ** apply (proj1 Hstate). exact HstateFact.
  - intro Hvalid.
    unfold replaceTransitionValid in Hvalid.
    destruct Hvalid as
      [HemptyFact [replacement [Hsome [HdistinctFact
        [HfreshFact [HinterfaceFact HstateFact]]]]]].
    inversion Hsome; subst replacement.
    apply (proj2
      (replace_decision_accepts_iff_facts
        residueEmpty true successorDistinct successorFresh
        interfaceMatches stateMatches)).
    split.
    + apply (proj2 Hempty). exact HemptyFact.
    + split.
      * reflexivity.
      * split.
        -- apply (proj2 Hdistinct). exact HdistinctFact.
        -- split.
           ++ apply (proj2 Hfresh). exact HfreshFact.
           ++ split.
              ** apply (proj2 Hinterface). exact HinterfaceFact.
              ** apply (proj2 Hstate). exact HstateFact.
Qed.

Theorem replace_retained_residue_precedes_all_other_failures :
  forall successorPresent successorDistinct successorFresh interfaceMatches stateMatches,
    decideCallableReplace
      false successorPresent successorDistinct successorFresh
      interfaceMatches stateMatches = CallableReplaceRetainedResidue.
Proof.
  intros successorPresent successorDistinct successorFresh interfaceMatches stateMatches.
  reflexivity.
Qed.

Theorem replace_missing_successor_precedes_successor_facts :
  forall successorDistinct successorFresh interfaceMatches stateMatches,
    decideCallableReplace
      true false successorDistinct successorFresh
      interfaceMatches stateMatches = CallableReplaceMissingSuccessor.
Proof.
  intros successorDistinct successorFresh interfaceMatches stateMatches.
  reflexivity.
Qed.
