From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import BoundaryRepresentation.

(*
  PHIL-BND-REP-001 — representation-neutral implementation correspondence.

  Production reflects concrete Haskell equality for the five exact identity
  gates plus the explicit mapping disposition into Boolean facts.  This layer
  owns their certified rejection order and the exact correspondence-evidence
  construction coordinates.  Boundary direction reuses the already-Certified
  checkBoundaryUse decision directly.
*)

Inductive BoundaryMappingDecision : Type :=
| BoundaryMappingDecisionAccepted
| BoundaryRepresentationMismatchDecision
| BoundaryGrammarMismatchDecision
| BoundaryValueTypeMismatchDecision
| RecognizedGrammarMismatchDecision
| RecognizedValueMismatchDecision
| BoundaryMappingRejectedDecision.

Definition decideBoundaryMappingByFacts
  (representationMatches grammarMatches valueTypeMatches
   recognizedGrammarMatches recognizedValueMatches dispositionAccepted : bool)
  : BoundaryMappingDecision :=
  if representationMatches then
    if grammarMatches then
      if valueTypeMatches then
        if recognizedGrammarMatches then
          if recognizedValueMatches then
            if dispositionAccepted then
              BoundaryMappingDecisionAccepted
            else BoundaryMappingRejectedDecision
          else RecognizedValueMismatchDecision
        else RecognizedGrammarMismatchDecision
      else BoundaryValueTypeMismatchDecision
    else BoundaryGrammarMismatchDecision
  else BoundaryRepresentationMismatchDecision.

Record BoundaryCorrespondencePlan
  (representation grammar valueType value : Type) : Type :=
  mkBoundaryCorrespondencePlan {
    plannedRepresentation : representation;
    plannedGrammar : grammar;
    plannedValueType : valueType;
    plannedGrammarValue : value;
    plannedSemanticValue : value
  }.

Arguments mkBoundaryCorrespondencePlan
  {representation grammar valueType value} _ _ _ _ _.

Definition planBoundaryCorrespondence
  {representation grammar valueType value : Type}
  (representationId : representation)
  (grammarId : grammar)
  (valueTypeId : valueType)
  (grammarValue semanticValue : value)
  : BoundaryCorrespondencePlan representation grammar valueType value :=
  mkBoundaryCorrespondencePlan
    representationId grammarId valueTypeId grammarValue semanticValue.

Definition decideBoundaryUse
  (direction : BoundaryDirection) (use : BoundaryUse)
  : BoundaryDirectionResult :=
  checkBoundaryUse direction use.

Theorem boundary_mapping_all_reflected_facts_accept :
  decideBoundaryMappingByFacts true true true true true true =
    BoundaryMappingDecisionAccepted.
Proof. reflexivity. Qed.

Theorem boundary_mapping_acceptance_requires_all_reflected_facts :
  forall representationMatches grammarMatches valueTypeMatches
         recognizedGrammarMatches recognizedValueMatches dispositionAccepted,
    decideBoundaryMappingByFacts
      representationMatches grammarMatches valueTypeMatches
      recognizedGrammarMatches recognizedValueMatches dispositionAccepted =
      BoundaryMappingDecisionAccepted ->
    representationMatches = true /\
    grammarMatches = true /\
    valueTypeMatches = true /\
    recognizedGrammarMatches = true /\
    recognizedValueMatches = true /\
    dispositionAccepted = true.
Proof.
  intros representationMatches grammarMatches valueTypeMatches
    recognizedGrammarMatches recognizedValueMatches dispositionAccepted Haccepted.
  destruct representationMatches; simpl in Haccepted; try discriminate.
  destruct grammarMatches; simpl in Haccepted; try discriminate.
  destruct valueTypeMatches; simpl in Haccepted; try discriminate.
  destruct recognizedGrammarMatches; simpl in Haccepted; try discriminate.
  destruct recognizedValueMatches; simpl in Haccepted; try discriminate.
  destruct dispositionAccepted; simpl in Haccepted; try discriminate.
  repeat split; reflexivity.
Qed.

Theorem boundary_representation_mismatch_has_precedence :
  forall grammarMatches valueTypeMatches recognizedGrammarMatches
         recognizedValueMatches dispositionAccepted,
    decideBoundaryMappingByFacts
      false grammarMatches valueTypeMatches recognizedGrammarMatches
      recognizedValueMatches dispositionAccepted =
      BoundaryRepresentationMismatchDecision.
Proof. reflexivity. Qed.

Theorem boundary_grammar_mismatch_has_precedence :
  forall valueTypeMatches recognizedGrammarMatches recognizedValueMatches
         dispositionAccepted,
    decideBoundaryMappingByFacts
      true false valueTypeMatches recognizedGrammarMatches
      recognizedValueMatches dispositionAccepted =
      BoundaryGrammarMismatchDecision.
Proof. reflexivity. Qed.

Theorem boundary_value_type_mismatch_has_precedence :
  forall recognizedGrammarMatches recognizedValueMatches dispositionAccepted,
    decideBoundaryMappingByFacts
      true true false recognizedGrammarMatches recognizedValueMatches
      dispositionAccepted =
      BoundaryValueTypeMismatchDecision.
Proof. reflexivity. Qed.

Theorem boundary_recognized_grammar_mismatch_has_precedence :
  forall recognizedValueMatches dispositionAccepted,
    decideBoundaryMappingByFacts
      true true true false recognizedValueMatches dispositionAccepted =
      RecognizedGrammarMismatchDecision.
Proof. reflexivity. Qed.

Theorem boundary_recognized_value_mismatch_has_precedence :
  forall dispositionAccepted,
    decideBoundaryMappingByFacts true true true true false dispositionAccepted =
      RecognizedValueMismatchDecision.
Proof. reflexivity. Qed.

Theorem boundary_explicit_mapping_rejection_is_last :
  decideBoundaryMappingByFacts true true true true true false =
    BoundaryMappingRejectedDecision.
Proof. reflexivity. Qed.

Theorem boundary_mapping_decision_sound_complete :
  forall representation parsed request disposition
         representationMatches grammarMatches valueTypeMatches
         recognizedGrammarMatches recognizedValueMatches dispositionAccepted,
    (representationMatches = true <->
      requestedRepresentation request = representationId representation) ->
    (grammarMatches = true <->
      requestedGrammar request = representationGrammar representation) ->
    (valueTypeMatches = true <->
      requestedValueType request = representationValueType representation) ->
    (recognizedGrammarMatches = true <->
      parsedGrammarId parsed = representationGrammar representation) ->
    (recognizedValueMatches = true <->
      parsedValueName parsed = requestedGrammarValue request) ->
    (dispositionAccepted = true <-> disposition = MappingAccepted) ->
    (decideBoundaryMappingByFacts
      representationMatches grammarMatches valueTypeMatches
      recognizedGrammarMatches recognizedValueMatches dispositionAccepted =
      BoundaryMappingDecisionAccepted <->
     requestedRepresentation request = representationId representation /\
     requestedGrammar request = representationGrammar representation /\
     requestedValueType request = representationValueType representation /\
     parsedGrammarId parsed = representationGrammar representation /\
     parsedValueName parsed = requestedGrammarValue request /\
     disposition = MappingAccepted).
Proof.
  intros representation parsed request disposition
    representationMatches grammarMatches valueTypeMatches
    recognizedGrammarMatches recognizedValueMatches dispositionAccepted
    Hrepresentation Hgrammar Htype HrecognizedGrammar HrecognizedValue Hdisposition.
  split.
  - intro Haccepted.
    apply boundary_mapping_acceptance_requires_all_reflected_facts in Haccepted.
    destruct Haccepted as
      [HrepresentationFact [HgrammarFact [HtypeFact
       [HrecognizedGrammarFact [HrecognizedValueFact HdispositionFact]]]]].
    repeat split.
    + apply (proj1 Hrepresentation). exact HrepresentationFact.
    + apply (proj1 Hgrammar). exact HgrammarFact.
    + apply (proj1 Htype). exact HtypeFact.
    + apply (proj1 HrecognizedGrammar). exact HrecognizedGrammarFact.
    + apply (proj1 HrecognizedValue). exact HrecognizedValueFact.
    + apply (proj1 Hdisposition). exact HdispositionFact.
  - intros
      [HrepresentationEq [HgrammarEq [HtypeEq
       [HrecognizedGrammarEq [HrecognizedValueEq HdispositionEq]]]]].
    assert (HrepresentationFact : representationMatches = true).
    { apply (proj2 Hrepresentation). exact HrepresentationEq. }
    assert (HgrammarFact : grammarMatches = true).
    { apply (proj2 Hgrammar). exact HgrammarEq. }
    assert (HtypeFact : valueTypeMatches = true).
    { apply (proj2 Htype). exact HtypeEq. }
    assert (HrecognizedGrammarFact : recognizedGrammarMatches = true).
    { apply (proj2 HrecognizedGrammar). exact HrecognizedGrammarEq. }
    assert (HrecognizedValueFact : recognizedValueMatches = true).
    { apply (proj2 HrecognizedValue). exact HrecognizedValueEq. }
    assert (HdispositionFact : dispositionAccepted = true).
    { apply (proj2 Hdisposition). exact HdispositionEq. }
    rewrite HrepresentationFact, HgrammarFact, HtypeFact,
      HrecognizedGrammarFact, HrecognizedValueFact, HdispositionFact.
    reflexivity.
Qed.

Theorem boundary_correspondence_plan_is_exact :
  forall representation grammar valueType value
         (representationId : representation)
         (grammarId : grammar)
         (valueTypeId : valueType)
         (grammarValue semanticValue : value),
    plannedRepresentation
      (planBoundaryCorrespondence
        representationId grammarId valueTypeId grammarValue semanticValue) =
      representationId /\
    plannedGrammar
      (planBoundaryCorrespondence
        representationId grammarId valueTypeId grammarValue semanticValue) =
      grammarId /\
    plannedValueType
      (planBoundaryCorrespondence
        representationId grammarId valueTypeId grammarValue semanticValue) =
      valueTypeId /\
    plannedGrammarValue
      (planBoundaryCorrespondence
        representationId grammarId valueTypeId grammarValue semanticValue) =
      grammarValue /\
    plannedSemanticValue
      (planBoundaryCorrespondence
        representationId grammarId valueTypeId grammarValue semanticValue) =
      semanticValue.
Proof.
  intros.
  repeat split; reflexivity.
Qed.

Theorem boundary_direction_decision_is_certified :
  forall direction use,
    decideBoundaryUse direction use = checkBoundaryUse direction use.
Proof. reflexivity. Qed.
