From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ResourceJoin.
From Phil.Core Require Import ResourceScope.

Inductive ScopedBoundaryDecision : Type :=
| ScopedBoundaryAcceptedDecision
| ScopedBoundaryResourceJoinDecision
| ScopedBoundaryLexicalLoanDecision.

Definition decideScopedBoundaryByFacts
  (resourceProjectionAccepted lexicalLoansClosed : bool)
  : ScopedBoundaryDecision :=
  if resourceProjectionAccepted then
    if lexicalLoansClosed then
      ScopedBoundaryAcceptedDecision
    else
      ScopedBoundaryLexicalLoanDecision
  else
    ScopedBoundaryResourceJoinDecision.

Theorem scoped_boundary_decision_corresponds_success :
  forall succession kind projection resourceProjectionAccepted lexicalLoansClosed,
    (resourceProjectionAccepted = true <->
      ResourceProjectionSuccess succession (scopedResourceProjection projection)) ->
    (lexicalLoansClosed = true <->
      LexicalLoansClosedAtBoundary (scopedLexicalLoans projection)) ->
    (decideScopedBoundaryByFacts resourceProjectionAccepted lexicalLoansClosed =
       ScopedBoundaryAcceptedDecision <->
      ScopedBoundaryProjectionSuccess succession kind projection).
Proof.
  intros succession kind projection resourceProjectionAccepted lexicalLoansClosed
    Hresource Hloans.
  unfold decideScopedBoundaryByFacts, ScopedBoundaryProjectionSuccess.
  destruct resourceProjectionAccepted eqn:HresourceBool;
    destruct lexicalLoansClosed eqn:HloansBool; simpl.
  - split.
    + intros _. split.
      * apply (proj1 Hresource). exact HresourceBool.
      * apply (proj1 Hloans). exact HloansBool.
    + intros _. reflexivity.
  - split.
    + discriminate.
    + intros [_ Hclosed].
      apply (proj2 Hloans) in Hclosed.
      rewrite HloansBool in Hclosed.
      discriminate.
  - split.
    + discriminate.
    + intros [Hprojection _].
      apply (proj2 Hresource) in Hprojection.
      rewrite HresourceBool in Hprojection.
      discriminate.
  - split.
    + discriminate.
    + intros [Hprojection _].
      apply (proj2 Hresource) in Hprojection.
      rewrite HresourceBool in Hprojection.
      discriminate.
Qed.

Inductive AffineProjectionDecision : Type :=
| AffineProjectionAcceptedDecision
| AffineProjectionExplicitCarrierDecision.

Definition decideAffineProjectionByFact
  (explicitCarrier : bool) : AffineProjectionDecision :=
  if explicitCarrier then
    AffineProjectionAcceptedDecision
  else
    AffineProjectionExplicitCarrierDecision.

Theorem affine_projection_decision_corresponds_explicit_state :
  forall declared state explicitCarrier,
    (explicitCarrier = true <-> ExplicitAffineProjection declared state) ->
    (decideAffineProjectionByFact explicitCarrier =
       AffineProjectionAcceptedDecision <->
      ExplicitAffineProjection declared state).
Proof.
  intros declared state explicitCarrier Hexplicit.
  unfold decideAffineProjectionByFact.
  destruct explicitCarrier eqn:Hcarrier; simpl.
  - split.
    + intros _. apply (proj1 Hexplicit). exact Hcarrier.
    + intros _. reflexivity.
  - split.
    + discriminate.
    + intros Hstate.
      apply (proj2 Hexplicit) in Hstate.
      rewrite Hcarrier in Hstate.
      discriminate.
Qed.

Definition TerminalArmsExcluded : Prop :=
  forall projection,
    ~ ContributesContinuingProjection TerminalArm projection.

Definition ContinuingArmContributionExact : Prop :=
  forall actual reported,
    ContributesContinuingProjection (ContinuingArm actual) reported ->
    actual = reported.

Inductive BranchDispositionDecision : Type :=
| BranchDispositionAcceptedDecision
| BranchDispositionTerminalExclusionDecision
| BranchDispositionContinuingExactDecision.

Definition decideBranchDispositionByFacts
  (terminalExcluded continuingExact : bool)
  : BranchDispositionDecision :=
  if terminalExcluded then
    if continuingExact then
      BranchDispositionAcceptedDecision
    else
      BranchDispositionContinuingExactDecision
  else
    BranchDispositionTerminalExclusionDecision.

Theorem branch_disposition_decision_corresponds_scope_theorems :
  forall terminalExcluded continuingExact,
    (terminalExcluded = true <-> TerminalArmsExcluded) ->
    (continuingExact = true <-> ContinuingArmContributionExact) ->
    (decideBranchDispositionByFacts terminalExcluded continuingExact =
       BranchDispositionAcceptedDecision <->
      TerminalArmsExcluded /\ ContinuingArmContributionExact).
Proof.
  intros terminalExcluded continuingExact Hterminal Hcontinuing.
  unfold decideBranchDispositionByFacts.
  destruct terminalExcluded eqn:HterminalBool;
    destruct continuingExact eqn:HcontinuingBool; simpl.
  - split.
    + intros _. split.
      * apply (proj1 Hterminal). exact HterminalBool.
      * apply (proj1 Hcontinuing). exact HcontinuingBool.
    + intros _. reflexivity.
  - split.
    + discriminate.
    + intros [_ Hexact].
      apply (proj2 Hcontinuing) in Hexact.
      rewrite HcontinuingBool in Hexact.
      discriminate.
  - split.
    + discriminate.
    + intros [Hexcluded _].
      apply (proj2 Hterminal) in Hexcluded.
      rewrite HterminalBool in Hexcluded.
      discriminate.
  - split.
    + discriminate.
    + intros [Hexcluded _].
      apply (proj2 Hterminal) in Hexcluded.
      rewrite HterminalBool in Hexcluded.
      discriminate.
Qed.
