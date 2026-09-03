From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import GenericStaticKind.

(*
  PHIL-GEN-KIND-001 — executable implementation-refinement staging.

  Parsing/candidate construction remain native.  The extracted kernel owns the
  final per-actual kind/reference classification over exact reflected facts.
*)

Inductive DirectStaticActualDecision : Type :=
| DirectStaticActualAcceptedDecision
| DirectStaticActualKindMismatchDecision.

Definition decideDirectStaticActualByFact
  (kindMatches : bool) : DirectStaticActualDecision :=
  if kindMatches
    then DirectStaticActualAcceptedDecision
    else DirectStaticActualKindMismatchDecision.

Theorem direct_static_actual_accepts_iff_fact :
  forall kindMatches,
    decideDirectStaticActualByFact kindMatches =
      DirectStaticActualAcceptedDecision <->
    kindMatches = true.
Proof.
  intros kindMatches.
  destruct kindMatches; cbn; intuition discriminate.
Qed.

Theorem direct_static_actual_decision_reflects_certified :
  forall references parameter actualKind semanticForm kindMatches,
    (kindMatches = true <-> actualKind = parameterKind parameter) ->
    (decideDirectStaticActualByFact kindMatches =
       DirectStaticActualAcceptedDecision <->
     exists checked,
       StaticActualAccepts references
         parameter
         (DirectStaticActual actualKind semanticForm)
         checked).
Proof.
  intros references parameter actualKind semanticForm kindMatches Hkind.
  split.
  - intro Hdecision.
    apply direct_static_actual_accepts_iff_fact in Hdecision.
    apply (proj1 Hkind) in Hdecision.
    subst actualKind.
    exists
      (mkCheckedStaticActual
        (parameterKey parameter)
        (parameterKind parameter)
        semanticForm).
    constructor.
  - intros [checked Haccepted].
    apply direct_static_actual_accepts_iff_fact.
    apply (proj2 Hkind).
    inversion Haccepted; subst.
    reflexivity.
Qed.

Inductive ReferencedStaticActualDecision : Type :=
| ReferencedStaticActualAcceptedDecision
| ReferencedStaticActualUnresolvedDecision
| ReferencedStaticActualKindMismatchDecision
| ReferencedStaticActualAmbiguousDecision
| ReferencedStaticActualSemanticFormMismatchDecision.

Definition decideReferencedStaticActualByFacts
  (nameExists expectedKindPresent expectedKindUnique selectedSemanticFormExact : bool)
  : ReferencedStaticActualDecision :=
  if nameExists then
    if expectedKindPresent then
      if expectedKindUnique then
        if selectedSemanticFormExact then
          ReferencedStaticActualAcceptedDecision
        else
          ReferencedStaticActualSemanticFormMismatchDecision
      else
        ReferencedStaticActualAmbiguousDecision
    else
      ReferencedStaticActualKindMismatchDecision
  else
    ReferencedStaticActualUnresolvedDecision.

Theorem referenced_static_actual_accepts_iff_facts :
  forall nameExists expectedKindPresent expectedKindUnique selectedSemanticFormExact,
    decideReferencedStaticActualByFacts
      nameExists expectedKindPresent expectedKindUnique selectedSemanticFormExact =
      ReferencedStaticActualAcceptedDecision <->
    nameExists = true /\
    expectedKindPresent = true /\
    expectedKindUnique = true /\
    selectedSemanticFormExact = true.
Proof.
  intros nameExists expectedKindPresent expectedKindUnique selectedSemanticFormExact.
  destruct nameExists, expectedKindPresent, expectedKindUnique,
    selectedSemanticFormExact; cbn; intuition discriminate.
Qed.

Theorem referenced_static_actual_decision_reflects_certified :
  forall references expectedKind referenceName semanticForm
    nameExists expectedKindPresent expectedKindUnique selectedSemanticFormExact,
    (nameExists = true <->
      exists candidate,
        In candidate references /\
        candidateName candidate = referenceName) ->
    (expectedKindPresent = true <->
      matchingCandidates expectedKind referenceName references <> []) ->
    (expectedKindUnique = true <->
      exists candidate,
        matchingCandidates expectedKind referenceName references = [candidate]) ->
    (selectedSemanticFormExact = true <->
      ReferenceResolves references expectedKind referenceName semanticForm) ->
    (decideReferencedStaticActualByFacts
       nameExists expectedKindPresent expectedKindUnique selectedSemanticFormExact =
       ReferencedStaticActualAcceptedDecision <->
     ReferenceResolves references expectedKind referenceName semanticForm).
Proof.
  intros references expectedKind referenceName semanticForm
    nameExists expectedKindPresent expectedKindUnique selectedSemanticFormExact
    Hname Hpresent Hunique Hselected.
  split.
  - intro Hdecision.
    apply referenced_static_actual_accepts_iff_facts in Hdecision.
    destruct Hdecision as [_ [_ [_ HselectedBool]]].
    apply (proj1 Hselected).
    exact HselectedBool.
  - intro Hresolves.
    apply referenced_static_actual_accepts_iff_facts.
    repeat split.
    + apply (proj2 Hname).
      destruct (reference_resolution_uses_declared_kind
        references expectedKind referenceName semanticForm Hresolves)
        as [candidate [Hin [HcandidateName [_ _]]]].
      exists candidate.
      split; assumption.
    + apply (proj2 Hpresent).
      destruct Hresolves as [candidate [Hmatching Hsemantic]].
      intro Hempty.
      rewrite Hmatching in Hempty.
      discriminate.
    + apply (proj2 Hunique).
      destruct Hresolves as [candidate [Hmatching Hsemantic]].
      exists candidate.
      exact Hmatching.
    + apply (proj2 Hselected).
      exact Hresolves.
Qed.

Inductive CheckedStaticActualShapeDecision : Type :=
| CheckedStaticActualShapeAcceptedDecision
| CheckedStaticActualParameterKeyDecision
| CheckedStaticActualKindDecision.

Definition decideCheckedStaticActualShapeByFacts
  (parameterKeyExact kindExact : bool) : CheckedStaticActualShapeDecision :=
  if parameterKeyExact then
    if kindExact then
      CheckedStaticActualShapeAcceptedDecision
    else
      CheckedStaticActualKindDecision
  else
    CheckedStaticActualParameterKeyDecision.

Theorem checked_static_actual_shape_accepts_iff_facts :
  forall parameterKeyExact kindExact,
    decideCheckedStaticActualShapeByFacts parameterKeyExact kindExact =
      CheckedStaticActualShapeAcceptedDecision <->
    parameterKeyExact = true /\ kindExact = true.
Proof.
  intros parameterKeyExact kindExact.
  destruct parameterKeyExact, kindExact; cbn; intuition discriminate.
Qed.

Theorem certified_static_actual_implies_shape_decision :
  forall references parameter actual checked parameterKeyExact kindExact,
    StaticActualAccepts references parameter actual checked ->
    (parameterKeyExact = true <->
      checkedParameterKey checked = parameterKey parameter) ->
    (kindExact = true <->
      checkedStaticKind checked = parameterKind parameter) ->
    decideCheckedStaticActualShapeByFacts parameterKeyExact kindExact =
      CheckedStaticActualShapeAcceptedDecision.
Proof.
  intros references parameter actual checked parameterKeyExact kindExact
    Haccepted Hkey Hkind.
  apply checked_static_actual_shape_accepts_iff_facts.
  destruct (accepted_static_actual_preserves_parameter_identity
    references parameter actual checked Haccepted) as [HkeyExact HkindExact].
  split.
  - apply (proj2 Hkey). exact HkeyExact.
  - apply (proj2 Hkind). exact HkindExact.
Qed.
