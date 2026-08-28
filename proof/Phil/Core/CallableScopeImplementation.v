From Stdlib Require Import Bool.Bool.
From Phil.Core Require Import CallableScope.

(*
  PHIL-CALL-SCOPE-IMPL-001 staging seam.

  The production checker keeps concrete Text/Map/Set/Data.Graph machinery.
  This file isolates only the representation-neutral decisions that production
  can feed with reflected native facts.
*)

Definition extentIsEscaping (extent : ClosureExtent) : bool :=
  match extent with
  | EscapingClosure => true
  | ClosureContainedIn _ => false
  end.

Definition captureIsScopedLoan (capture : ClosureScopeCapture) : bool :=
  match capture with
  | ScopeIndependentCapture _ => false
  | ScopedSharedLoanCapture _ _ => true
  end.

Definition scopeEqualityFact
  (extent : ClosureExtent)
  (capture : ClosureScopeCapture) : bool :=
  match extent, capture with
  | ClosureContainedIn closureScope, ScopedSharedLoanCapture _ loanScope =>
      Nat.eqb closureScope loanScope
  | _, _ => true
  end.

Definition decideScopeCaptureByFacts
  (isEscaping isScopedLoan sameScope : bool) : ScopeCaptureDecision :=
  if isScopedLoan then
    if isEscaping then ScopeCaptureEscapingLoan
    else if sameScope then ScopeCaptureAccepted
    else ScopeCaptureOutsideLoanValidity
  else ScopeCaptureAccepted.

Theorem scope_capture_fact_decision_agrees_with_certified :
  forall extent capture,
    decideScopeCaptureByFacts
      (extentIsEscaping extent)
      (captureIsScopedLoan capture)
      (scopeEqualityFact extent capture) =
    decideClosureScopeCapture extent capture.
Proof.
  intros extent capture.
  destruct capture as [capture|capture loanScope];
    destruct extent as [|closureScope];
    cbn; reflexivity.
Qed.

Inductive RecursiveClosureGraphDecision : Type :=
| RecursiveClosureGraphAccepted
| RecursiveClosureDuplicateNode
| RecursiveClosureUnknownReference
| RecursiveClosureRestrictedCycle.

Definition decideRecursiveClosureGraphFacts
  (uniqueNodes referencesKnownFact noRestrictedCycleFact : bool)
  : RecursiveClosureGraphDecision :=
  if uniqueNodes then
    if referencesKnownFact then
      if noRestrictedCycleFact
      then RecursiveClosureGraphAccepted
      else RecursiveClosureRestrictedCycle
    else RecursiveClosureUnknownReference
  else RecursiveClosureDuplicateNode.

Theorem recursive_graph_fact_accept_iff_all_true :
  forall uniqueNodes referencesKnownFact noRestrictedCycleFact,
    decideRecursiveClosureGraphFacts
      uniqueNodes referencesKnownFact noRestrictedCycleFact =
      RecursiveClosureGraphAccepted <->
    uniqueNodes = true /\
    referencesKnownFact = true /\
    noRestrictedCycleFact = true.
Proof.
  intros uniqueNodes referencesKnownFact noRestrictedCycleFact.
  destruct uniqueNodes, referencesKnownFact, noRestrictedCycleFact;
    cbn; split; intro H.
  all: try discriminate.
  all: try (repeat split; reflexivity).
  all: destruct H as [Hunique [Hknown Hcycle]]; discriminate.
Qed.

Theorem recursive_graph_fact_accept_iff_certified
  : forall nodes uniqueNodes referencesKnownFact noRestrictedCycleFact,
    (uniqueNodes = true <-> uniqueClosureNodes nodes) ->
    (referencesKnownFact = true <-> referencesKnown nodes) ->
    (noRestrictedCycleFact = true <-> noRestrictedClosureCycles nodes) ->
    (decideRecursiveClosureGraphFacts
      uniqueNodes referencesKnownFact noRestrictedCycleFact =
      RecursiveClosureGraphAccepted <->
      recursiveClosureGraphValid nodes).
Proof.
  intros nodes uniqueNodes referencesKnownFact noRestrictedCycleFact
    Hunique Hknown Hcycles.
  rewrite recursive_graph_fact_accept_iff_all_true.
  split.
  - intros [HuniqueTrue [HknownTrue HcyclesTrue]].
    repeat split.
    + apply (proj1 Hunique). exact HuniqueTrue.
    + apply (proj1 Hknown). exact HknownTrue.
    + apply (proj1 Hcycles). exact HcyclesTrue.
  - intros [HuniqueValid [HknownValid HcyclesValid]].
    repeat split.
    + apply (proj2 Hunique). exact HuniqueValid.
    + apply (proj2 Hknown). exact HknownValid.
    + apply (proj2 Hcycles). exact HcyclesValid.
Qed.

Theorem duplicate_node_fact_has_first_precedence :
  forall referencesKnownFact noRestrictedCycleFact,
    decideRecursiveClosureGraphFacts
      false referencesKnownFact noRestrictedCycleFact =
      RecursiveClosureDuplicateNode.
Proof.
  reflexivity.
Qed.

Theorem unknown_reference_fact_has_second_precedence :
  forall noRestrictedCycleFact,
    decideRecursiveClosureGraphFacts
      true false noRestrictedCycleFact =
      RecursiveClosureUnknownReference.
Proof.
  reflexivity.
Qed.

Theorem restricted_cycle_fact_has_third_precedence :
  decideRecursiveClosureGraphFacts true true false =
  RecursiveClosureRestrictedCycle.
Proof.
  reflexivity.
Qed.

Theorem fully_valid_graph_facts_accept :
  decideRecursiveClosureGraphFacts true true true =
  RecursiveClosureGraphAccepted.
Proof.
  reflexivity.
Qed.
