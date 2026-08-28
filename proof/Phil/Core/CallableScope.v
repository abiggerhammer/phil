From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List.

Import ListNotations.

(*
  PHIL-CALL-SCOPE-001 — bounded closure scope and recursive-environment safety.

  The model deliberately separates the two existing Phase 1 rules:

  - scoped shared-loan captures may not outlive their exact lexical scope; and
  - runtime closure-environment cycles may not hide restricted captures.

  Concrete Text-backed identities, Haskell Map/Set operations, SCC discovery,
  diagnostic payload construction, and source lifetime inference remain
  correspondence boundaries.
*)

Inductive ClosureExtent : Type :=
| EscapingClosure
| ClosureContainedIn (scope : nat).

Inductive ClosureScopeCapture : Type :=
| ScopeIndependentCapture (capture : nat)
| ScopedSharedLoanCapture (capture scope : nat).

Definition scopeCaptureValid
  (extent : ClosureExtent)
  (capture : ClosureScopeCapture) : Prop :=
  match capture with
  | ScopeIndependentCapture _ => True
  | ScopedSharedLoanCapture _ loanScope =>
      match extent with
      | EscapingClosure => False
      | ClosureContainedIn closureScope => closureScope = loanScope
      end
  end.

Inductive ScopeCaptureDecision : Type :=
| ScopeCaptureAccepted
| ScopeCaptureEscapingLoan
| ScopeCaptureOutsideLoanValidity.

Definition decideClosureScopeCapture
  (extent : ClosureExtent)
  (capture : ClosureScopeCapture) : ScopeCaptureDecision :=
  match capture with
  | ScopeIndependentCapture _ => ScopeCaptureAccepted
  | ScopedSharedLoanCapture _ loanScope =>
      match extent with
      | EscapingClosure => ScopeCaptureEscapingLoan
      | ClosureContainedIn closureScope =>
          if Nat.eqb closureScope loanScope
          then ScopeCaptureAccepted
          else ScopeCaptureOutsideLoanValidity
      end
  end.

Theorem scope_capture_accept_iff_valid :
  forall extent capture,
    decideClosureScopeCapture extent capture = ScopeCaptureAccepted <->
    scopeCaptureValid extent capture.
Proof.
  intros extent capture.
  destruct capture as [capture|capture loanScope]; cbn.
  - split; intro H.
    + exact I.
    + reflexivity.
  - destruct extent as [|closureScope]; cbn.
    + split; intro H; contradiction.
    + destruct (Nat.eqb closureScope loanScope) eqn:Heq.
      * apply Nat.eqb_eq in Heq.
        subst loanScope.
        split; intro H; reflexivity.
      * apply Nat.eqb_neq in Heq.
        split; intro H.
        -- discriminate.
        -- exfalso. apply Heq. exact H.
Qed.

Theorem scope_independent_capture_may_escape :
  forall capture,
    decideClosureScopeCapture
      EscapingClosure
      (ScopeIndependentCapture capture) = ScopeCaptureAccepted.
Proof.
  reflexivity.
Qed.

Theorem escaping_scoped_loan_rejects :
  forall capture scope,
    decideClosureScopeCapture
      EscapingClosure
      (ScopedSharedLoanCapture capture scope) = ScopeCaptureEscapingLoan.
Proof.
  reflexivity.
Qed.

Theorem exact_scope_scoped_loan_accepts :
  forall capture scope,
    decideClosureScopeCapture
      (ClosureContainedIn scope)
      (ScopedSharedLoanCapture capture scope) = ScopeCaptureAccepted.
Proof.
  intros capture scope.
  cbn.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem mismatched_scope_scoped_loan_rejects :
  forall capture loanScope closureScope,
    closureScope <> loanScope ->
    decideClosureScopeCapture
      (ClosureContainedIn closureScope)
      (ScopedSharedLoanCapture capture loanScope) =
      ScopeCaptureOutsideLoanValidity.
Proof.
  intros capture loanScope closureScope Hneq.
  cbn.
  destruct (Nat.eqb closureScope loanScope) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Record ClosureRecursionNode : Type := mkClosureRecursionNode {
  closureOccurrence : nat;
  closureReferences : list nat;
  closureHasRestrictedCapture : bool
}.

Definition nodeKeys (nodes : list ClosureRecursionNode) : list nat :=
  map closureOccurrence nodes.

Definition uniqueClosureNodes (nodes : list ClosureRecursionNode) : Prop :=
  NoDup (nodeKeys nodes).

Definition nodeKnown
  (nodes : list ClosureRecursionNode)
  (key : nat) : Prop :=
  exists node,
    In node nodes /\ closureOccurrence node = key.

Definition referencesKnown (nodes : list ClosureRecursionNode) : Prop :=
  forall node target,
    In node nodes ->
    In target (closureReferences node) ->
    nodeKnown nodes target.

Definition closureEdge
  (nodes : list ClosureRecursionNode)
  (source target : nat) : Prop :=
  exists node,
    In node nodes /\
    closureOccurrence node = source /\
    In target (closureReferences node).

Inductive NonEmptyClosurePath
  (nodes : list ClosureRecursionNode) : nat -> nat -> Prop :=
| ClosurePathEdge :
    forall source target,
      closureEdge nodes source target ->
      NonEmptyClosurePath nodes source target
| ClosurePathStep :
    forall source middle target,
      closureEdge nodes source middle ->
      NonEmptyClosurePath nodes middle target ->
      NonEmptyClosurePath nodes source target.

Definition cyclicClosureOccurrence
  (nodes : list ClosureRecursionNode)
  (key : nat) : Prop :=
  NonEmptyClosurePath nodes key key.

Definition noRestrictedClosureCycles
  (nodes : list ClosureRecursionNode) : Prop :=
  forall node,
    In node nodes ->
    closureHasRestrictedCapture node = true ->
    ~ cyclicClosureOccurrence nodes (closureOccurrence node).

Definition recursiveClosureGraphValid
  (nodes : list ClosureRecursionNode) : Prop :=
  uniqueClosureNodes nodes /\
  referencesKnown nodes /\
  noRestrictedClosureCycles nodes.

Theorem duplicate_closure_nodes_reject :
  forall nodes,
    ~ uniqueClosureNodes nodes ->
    ~ recursiveClosureGraphValid nodes.
Proof.
  intros nodes Hduplicate Hvalid.
  apply Hduplicate.
  exact (proj1 Hvalid).
Qed.

Theorem unknown_recursive_reference_rejects :
  forall nodes,
    ~ referencesKnown nodes ->
    ~ recursiveClosureGraphValid nodes.
Proof.
  intros nodes Hunknown Hvalid.
  apply Hunknown.
  exact (proj1 (proj2 Hvalid)).
Qed.

Theorem closure_self_edge_is_cycle :
  forall nodes key,
    closureEdge nodes key key ->
    cyclicClosureOccurrence nodes key.
Proof.
  intros nodes key Hedge.
  unfold cyclicClosureOccurrence.
  apply ClosurePathEdge.
  exact Hedge.
Qed.

Theorem restricted_self_recursive_environment_rejects :
  forall nodes node,
    In node nodes ->
    closureHasRestrictedCapture node = true ->
    In (closureOccurrence node) (closureReferences node) ->
    ~ recursiveClosureGraphValid nodes.
Proof.
  intros nodes node Hin Hrestricted Hself Hvalid.
  destruct Hvalid as [_ [_ HnoRestricted]].
  specialize (HnoRestricted node Hin Hrestricted).
  apply HnoRestricted.
  apply closure_self_edge_is_cycle.
  exists node.
  split.
  - exact Hin.
  - split.
    + reflexivity.
    + exact Hself.
Qed.

Theorem two_node_reference_cycle :
  forall nodes first second,
    In first nodes ->
    In second nodes ->
    In (closureOccurrence second) (closureReferences first) ->
    In (closureOccurrence first) (closureReferences second) ->
    cyclicClosureOccurrence nodes (closureOccurrence first).
Proof.
  intros nodes first second Hfirst Hsecond HfirstRef HsecondRef.
  unfold cyclicClosureOccurrence.
  eapply ClosurePathStep with (middle := closureOccurrence second).
  - exists first.
    split.
    + exact Hfirst.
    + split.
      * reflexivity.
      * exact HfirstRef.
  - apply ClosurePathEdge.
    exists second.
    split.
    + exact Hsecond.
    + split.
      * reflexivity.
      * exact HsecondRef.
Qed.

Theorem restricted_mutual_recursive_environment_rejects :
  forall nodes first second,
    In first nodes ->
    In second nodes ->
    closureHasRestrictedCapture first = true ->
    In (closureOccurrence second) (closureReferences first) ->
    In (closureOccurrence first) (closureReferences second) ->
    ~ recursiveClosureGraphValid nodes.
Proof.
  intros nodes first second Hfirst Hsecond Hrestricted HfirstRef HsecondRef Hvalid.
  destruct Hvalid as [_ [_ HnoRestricted]].
  specialize (HnoRestricted first Hfirst Hrestricted).
  apply HnoRestricted.
  eapply two_node_reference_cycle; eauto.
Qed.

Theorem unrestricted_recursive_environment_satisfies_cycle_rule :
  forall nodes,
    (forall node,
      In node nodes ->
      closureHasRestrictedCapture node = false) ->
    noRestrictedClosureCycles nodes.
Proof.
  intros nodes Hall node Hin Hrestricted.
  specialize (Hall node Hin).
  rewrite Hall in Hrestricted.
  discriminate.
Qed.

Theorem acyclic_restricted_environment_satisfies_cycle_rule :
  forall nodes,
    (forall node,
      In node nodes ->
      closureHasRestrictedCapture node = true ->
      ~ cyclicClosureOccurrence nodes (closureOccurrence node)) ->
    noRestrictedClosureCycles nodes.
Proof.
  intros nodes Hacyclic node Hin Hrestricted.
  eapply Hacyclic; eauto.
Qed.

Theorem structurally_valid_cycle_safe_graph_accepts :
  forall nodes,
    uniqueClosureNodes nodes ->
    referencesKnown nodes ->
    noRestrictedClosureCycles nodes ->
    recursiveClosureGraphValid nodes.
Proof.
  intros nodes Hunique Hknown Hcycles.
  repeat split; assumption.
Qed.

Theorem valid_graph_has_no_hidden_restricted_cycle :
  forall nodes node,
    recursiveClosureGraphValid nodes ->
    In node nodes ->
    closureHasRestrictedCapture node = true ->
    ~ cyclicClosureOccurrence nodes (closureOccurrence node).
Proof.
  intros nodes node Hvalid Hin Hrestricted.
  exact (proj2 (proj2 Hvalid) node Hin Hrestricted).
Qed.
