From Stdlib Require Import Bool.Bool.
From Phil.Core Require Import CallableMode CallableModeStrengthening.

(*
  Executable implementation correspondence for PHIL-CALL-MODE-STRENGTHEN-001.

  Production remains responsible for capture discovery, concrete Mode ordering,
  InterfaceRevision/Text equality, diagnostic payloads, and truth of referenced
  lifecycle/authority obligations. This layer owns only the final reflected
  explicit-mode decision and the checked-result shape postcheck.
*)

Inductive ExplicitClosureModeDecision : Type :=
| ExplicitClosureModeWeakeningDecision
| ExplicitClosureModeEqualDecision
| ExplicitClosureModeMissingJustificationDecision
| ExplicitClosureModeTargetImplementationDecision
| ExplicitClosureModeWrongContractDecision
| ExplicitClosureModeEmptyJustificationDecision
| ExplicitClosureModeStrengthenedDecision.

Definition decideExplicitClosureModeByFacts
  (nonWeakening
   equalToMinimum
   justificationPresent
   targetImplementationReason
   contractMatches
   detailPresent : bool) : ExplicitClosureModeDecision :=
  if nonWeakening then
    if equalToMinimum then
      ExplicitClosureModeEqualDecision
    else if justificationPresent then
      if targetImplementationReason then
        ExplicitClosureModeTargetImplementationDecision
      else if contractMatches then
        if detailPresent then
          ExplicitClosureModeStrengthenedDecision
        else ExplicitClosureModeEmptyJustificationDecision
      else ExplicitClosureModeWrongContractDecision
    else ExplicitClosureModeMissingJustificationDecision
  else ExplicitClosureModeWeakeningDecision.

Definition explicitClosureModeDecisionAcceptsBool
  (decision : ExplicitClosureModeDecision) : bool :=
  match decision with
  | ExplicitClosureModeEqualDecision => true
  | ExplicitClosureModeStrengthenedDecision => true
  | _ => false
  end.

Definition explicitClosureModeFacts
  (nonWeakening
   equalToMinimum
   justificationPresent
   targetImplementationReason
   contractMatches
   detailPresent : bool) : bool :=
  andb nonWeakening
    (orb equalToMinimum
      (andb justificationPresent
        (andb (negb targetImplementationReason)
          (andb contractMatches detailPresent)))).

Theorem explicit_closure_mode_decision_computes_facts :
  forall nonWeakening equalToMinimum justificationPresent
         targetImplementationReason contractMatches detailPresent,
    explicitClosureModeDecisionAcceptsBool
      (decideExplicitClosureModeByFacts
        nonWeakening
        equalToMinimum
        justificationPresent
        targetImplementationReason
        contractMatches
        detailPresent) =
    explicitClosureModeFacts
      nonWeakening
      equalToMinimum
      justificationPresent
      targetImplementationReason
      contractMatches
      detailPresent.
Proof.
  intros nonWeakening equalToMinimum justificationPresent
    targetImplementationReason contractMatches detailPresent.
  destruct nonWeakening, equalToMinimum, justificationPresent,
    targetImplementationReason, contractMatches, detailPresent;
    reflexivity.
Qed.

Definition ExplicitClosureModeDecisionAccepts
  (decision : ExplicitClosureModeDecision) : Prop :=
  explicitClosureModeDecisionAcceptsBool decision = true.

Theorem explicit_closure_mode_decision_accept_iff_facts :
  forall nonWeakening equalToMinimum justificationPresent
         targetImplementationReason contractMatches detailPresent,
    ExplicitClosureModeDecisionAccepts
      (decideExplicitClosureModeByFacts
        nonWeakening
        equalToMinimum
        justificationPresent
        targetImplementationReason
        contractMatches
        detailPresent) <->
    explicitClosureModeFacts
      nonWeakening
      equalToMinimum
      justificationPresent
      targetImplementationReason
      contractMatches
      detailPresent = true.
Proof.
  intros nonWeakening equalToMinimum justificationPresent
    targetImplementationReason contractMatches detailPresent.
  unfold ExplicitClosureModeDecisionAccepts.
  rewrite explicit_closure_mode_decision_computes_facts.
  reflexivity.
Qed.

Theorem constructed_explicit_closure_mode_valid_iff_semantic_core :
  forall contractRevision captureMinimum declared justification,
    ClosureModeDeclarationValid
      contractRevision
      captureMinimum
      (ExplicitClosureMode declared justification)
      (mkCheckedClosureMode captureMinimum declared justification) <->
    modeLe captureMinimum declared = true /\
    (declared = captureMinimum \/
     SemanticStrengtheningJustification contractRevision justification).
Proof.
  intros contractRevision captureMinimum declared justification.
  unfold ClosureModeDeclarationValid.
  simpl.
  split.
  - intros [_ [_ [_ Hcore]]].
    exact Hcore.
  - intros [HnonWeakening Hreason].
    repeat split; try reflexivity; assumption.
Qed.

Theorem explicit_closure_mode_decision_accept_iff_certified :
  forall contractRevision captureMinimum declared justification
         nonWeakening equalToMinimum justificationPresent
         targetImplementationReason contractMatches detailPresent,
    (explicitClosureModeFacts
       nonWeakening
       equalToMinimum
       justificationPresent
       targetImplementationReason
       contractMatches
       detailPresent = true <->
      modeLe captureMinimum declared = true /\
      (declared = captureMinimum \/
       SemanticStrengtheningJustification contractRevision justification)) ->
    ExplicitClosureModeDecisionAccepts
      (decideExplicitClosureModeByFacts
        nonWeakening
        equalToMinimum
        justificationPresent
        targetImplementationReason
        contractMatches
        detailPresent) <->
    ClosureModeDeclarationValid
      contractRevision
      captureMinimum
      (ExplicitClosureMode declared justification)
      (mkCheckedClosureMode captureMinimum declared justification).
Proof.
  intros contractRevision captureMinimum declared justification
    nonWeakening equalToMinimum justificationPresent
    targetImplementationReason contractMatches detailPresent Hreflection.
  rewrite explicit_closure_mode_decision_accept_iff_facts.
  rewrite constructed_explicit_closure_mode_valid_iff_semantic_core.
  exact Hreflection.
Qed.

Inductive CheckedClosureModeShapeDecision : Type :=
| CheckedClosureModeMinimumDecision
| CheckedClosureModeSelectedDecision
| CheckedClosureModeJustificationDecision
| CheckedClosureModeShapeAcceptedDecision.

Definition decideCheckedClosureModeShapeByFacts
  (minimumExact selectedExact justificationExact : bool)
  : CheckedClosureModeShapeDecision :=
  if minimumExact then
    if selectedExact then
      if justificationExact then
        CheckedClosureModeShapeAcceptedDecision
      else CheckedClosureModeJustificationDecision
    else CheckedClosureModeSelectedDecision
  else CheckedClosureModeMinimumDecision.

Definition checkedClosureModeShapeDecisionAcceptsBool
  (decision : CheckedClosureModeShapeDecision) : bool :=
  match decision with
  | CheckedClosureModeShapeAcceptedDecision => true
  | _ => false
  end.

Definition checkedClosureModeShapeFacts
  (minimumExact selectedExact justificationExact : bool) : bool :=
  andb minimumExact (andb selectedExact justificationExact).

Theorem checked_closure_mode_shape_decision_computes_facts :
  forall minimumExact selectedExact justificationExact,
    checkedClosureModeShapeDecisionAcceptsBool
      (decideCheckedClosureModeShapeByFacts
        minimumExact selectedExact justificationExact) =
    checkedClosureModeShapeFacts
      minimumExact selectedExact justificationExact.
Proof.
  intros minimumExact selectedExact justificationExact.
  destruct minimumExact, selectedExact, justificationExact;
    reflexivity.
Qed.

Definition CheckedClosureModeShapeDecisionAccepts
  (decision : CheckedClosureModeShapeDecision) : Prop :=
  checkedClosureModeShapeDecisionAcceptsBool decision = true.

Theorem checked_closure_mode_shape_accept_iff_facts :
  forall minimumExact selectedExact justificationExact,
    CheckedClosureModeShapeDecisionAccepts
      (decideCheckedClosureModeShapeByFacts
        minimumExact selectedExact justificationExact) <->
    checkedClosureModeShapeFacts
      minimumExact selectedExact justificationExact = true.
Proof.
  intros minimumExact selectedExact justificationExact.
  unfold CheckedClosureModeShapeDecisionAccepts.
  rewrite checked_closure_mode_shape_decision_computes_facts.
  reflexivity.
Qed.

Theorem certified_explicit_closure_mode_supplies_checked_shape :
  forall contractRevision captureMinimum declared justification checked
         minimumExact selectedExact justificationExact,
    ClosureModeDeclarationValid
      contractRevision
      captureMinimum
      (ExplicitClosureMode declared justification)
      checked ->
    (checkedClosureModeShapeFacts
       minimumExact selectedExact justificationExact = true <->
      checkedMinimumMode checked = captureMinimum /\
      checkedSelectedMode checked = declared /\
      checkedModeJustification checked = justification) ->
    CheckedClosureModeShapeDecisionAccepts
      (decideCheckedClosureModeShapeByFacts
        minimumExact selectedExact justificationExact).
Proof.
  intros contractRevision captureMinimum declared justification checked
    minimumExact selectedExact justificationExact Hvalid Hreflection.
  apply (proj2
    (checked_closure_mode_shape_accept_iff_facts
      minimumExact selectedExact justificationExact)).
  apply (proj2 Hreflection).
  unfold ClosureModeDeclarationValid in Hvalid.
  destruct Hvalid as [Hminimum [Hselected [Hjustification _]]].
  repeat split; assumption.
Qed.

Theorem certified_derived_closure_mode_supplies_checked_shape :
  forall contractRevision captureMinimum checked
         minimumExact selectedExact justificationExact,
    ClosureModeDeclarationValid
      contractRevision captureMinimum DerivedClosureMode checked ->
    (checkedClosureModeShapeFacts
       minimumExact selectedExact justificationExact = true <->
      checkedMinimumMode checked = captureMinimum /\
      checkedSelectedMode checked = captureMinimum /\
      checkedModeJustification checked = None) ->
    CheckedClosureModeShapeDecisionAccepts
      (decideCheckedClosureModeShapeByFacts
        minimumExact selectedExact justificationExact).
Proof.
  intros contractRevision captureMinimum checked
    minimumExact selectedExact justificationExact Hvalid Hreflection.
  apply (proj2
    (checked_closure_mode_shape_accept_iff_facts
      minimumExact selectedExact justificationExact)).
  apply (proj2 Hreflection).
  unfold ClosureModeDeclarationValid in Hvalid.
  destruct Hvalid as [Hminimum [Hselected Hjustification]].
  repeat split; assumption.
Qed.
