From Stdlib Require Import Bool.Bool.
From Phil.Core Require Import CallableModeStrengthening.

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

Definition ExplicitClosureModeDecisionAccepts
  (decision : ExplicitClosureModeDecision) : Prop :=
  decision = ExplicitClosureModeEqualDecision \/
  decision = ExplicitClosureModeStrengthenedDecision.

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
    nonWeakening = true /\
    (equalToMinimum = true \/
      (justificationPresent = true /\
       targetImplementationReason = false /\
       contractMatches = true /\
       detailPresent = true)).
Proof.
  intros nonWeakening equalToMinimum justificationPresent
    targetImplementationReason contractMatches detailPresent.
  destruct nonWeakening, equalToMinimum, justificationPresent,
    targetImplementationReason, contractMatches, detailPresent;
    simpl; intuition.
Qed.

Theorem explicit_closure_mode_decision_accept_iff_certified :
  forall contractRevision captureMinimum declared justification
         nonWeakening equalToMinimum justificationPresent
         targetImplementationReason contractMatches detailPresent,
    (nonWeakening = true <-> modeLe captureMinimum declared = true) ->
    (equalToMinimum = true <-> declared = captureMinimum) ->
    (justificationPresent = true /\
     targetImplementationReason = false /\
     contractMatches = true /\
     detailPresent = true <->
       SemanticStrengtheningJustification contractRevision justification) ->
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
    targetImplementationReason contractMatches detailPresent
    HnonWeakening Hequal Hsemantic.
  rewrite explicit_closure_mode_decision_accept_iff_facts.
  unfold ClosureModeDeclarationValid.
  simpl.
  rewrite HnonWeakening, Hequal, Hsemantic.
  reflexivity.
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

Theorem checked_closure_mode_shape_accept_iff_facts :
  forall minimumExact selectedExact justificationExact,
    decideCheckedClosureModeShapeByFacts
      minimumExact selectedExact justificationExact =
      CheckedClosureModeShapeAcceptedDecision <->
    minimumExact = true /\
    selectedExact = true /\
    justificationExact = true.
Proof.
  intros minimumExact selectedExact justificationExact.
  destruct minimumExact, selectedExact, justificationExact;
    simpl; intuition.
Qed.

Theorem certified_explicit_closure_mode_supplies_checked_shape :
  forall contractRevision captureMinimum declared justification checked
         minimumExact selectedExact justificationExact,
    ClosureModeDeclarationValid
      contractRevision
      captureMinimum
      (ExplicitClosureMode declared justification)
      checked ->
    (minimumExact = true <->
      checkedMinimumMode checked = captureMinimum) ->
    (selectedExact = true <->
      checkedSelectedMode checked = declared) ->
    (justificationExact = true <->
      checkedModeJustification checked = justification) ->
    decideCheckedClosureModeShapeByFacts
      minimumExact selectedExact justificationExact =
      CheckedClosureModeShapeAcceptedDecision.
Proof.
  intros contractRevision captureMinimum declared justification checked
    minimumExact selectedExact justificationExact
    Hvalid Hminimum Hselected Hjustification.
  apply (proj2
    (checked_closure_mode_shape_accept_iff_facts
      minimumExact selectedExact justificationExact)).
  unfold ClosureModeDeclarationValid in Hvalid.
  destruct Hvalid as [HminimumEq [HselectedEq [HjustificationEq _]]].
  repeat split.
  - exact ((proj2 Hminimum) HminimumEq).
  - exact ((proj2 Hselected) HselectedEq).
  - exact ((proj2 Hjustification) HjustificationEq).
Qed.

Theorem certified_derived_closure_mode_supplies_checked_shape :
  forall contractRevision captureMinimum checked
         minimumExact selectedExact justificationExact,
    ClosureModeDeclarationValid
      contractRevision captureMinimum DerivedClosureMode checked ->
    (minimumExact = true <->
      checkedMinimumMode checked = captureMinimum) ->
    (selectedExact = true <->
      checkedSelectedMode checked = captureMinimum) ->
    (justificationExact = true <->
      checkedModeJustification checked = None) ->
    decideCheckedClosureModeShapeByFacts
      minimumExact selectedExact justificationExact =
      CheckedClosureModeShapeAcceptedDecision.
Proof.
  intros contractRevision captureMinimum checked
    minimumExact selectedExact justificationExact
    Hvalid Hminimum Hselected Hjustification.
  apply (proj2
    (checked_closure_mode_shape_accept_iff_facts
      minimumExact selectedExact justificationExact)).
  unfold ClosureModeDeclarationValid in Hvalid.
  destruct Hvalid as [HminimumEq [HselectedEq HjustificationEq]].
  repeat split.
  - exact ((proj2 Hminimum) HminimumEq).
  - exact ((proj2 Hselected) HselectedEq).
  - exact ((proj2 Hjustification) HjustificationEq).
Qed.
