From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import BoundaryProgression.

Set Implicit Arguments.

(*
  PHIL-BND-PROGRESS-001 — representation-neutral implementation correspondence.

  Production reflects exact receive/send identity checks and predecessor
  progression results into Boolean facts. Concrete Int emission arithmetic is
  separately classified into the already-Certified EmissionDisposition enum.
  This layer owns the Certified rejection order and exact complete-emission
  construction coordinates.
*)

Inductive ReceiveProgressionDecision : Type :=
| ReceiveProgressionDecisionAccepted
| ReceiveMappingGrammarMismatchDecision
| ReceiveMappingValueMismatchDecision
| UnderlyingReceiveRejectedDecision.

Definition decideReceiveProgressionByFacts
  (grammarMatches valueMatches underlyingAccepted : bool)
  : ReceiveProgressionDecision :=
  if grammarMatches then
    if valueMatches then
      if underlyingAccepted then
        ReceiveProgressionDecisionAccepted
      else UnderlyingReceiveRejectedDecision
    else ReceiveMappingValueMismatchDecision
  else ReceiveMappingGrammarMismatchDecision.

Theorem receive_progression_all_reflected_facts_accept :
  decideReceiveProgressionByFacts true true true =
    ReceiveProgressionDecisionAccepted.
Proof. reflexivity. Qed.

Theorem receive_progression_acceptance_requires_all_reflected_facts :
  forall grammarMatches valueMatches underlyingAccepted,
    decideReceiveProgressionByFacts grammarMatches valueMatches underlyingAccepted =
      ReceiveProgressionDecisionAccepted ->
    grammarMatches = true /\ valueMatches = true /\ underlyingAccepted = true.
Proof.
  intros grammarMatches valueMatches underlyingAccepted Haccepted.
  destruct grammarMatches; simpl in Haccepted; try discriminate.
  destruct valueMatches; simpl in Haccepted; try discriminate.
  destruct underlyingAccepted; simpl in Haccepted; try discriminate.
  repeat split; reflexivity.
Qed.

Theorem receive_grammar_mismatch_has_precedence :
  forall valueMatches underlyingAccepted,
    decideReceiveProgressionByFacts false valueMatches underlyingAccepted =
      ReceiveMappingGrammarMismatchDecision.
Proof. reflexivity. Qed.

Theorem receive_value_mismatch_has_precedence :
  forall underlyingAccepted,
    decideReceiveProgressionByFacts true false underlyingAccepted =
      ReceiveMappingValueMismatchDecision.
Proof. reflexivity. Qed.

Theorem underlying_receive_rejection_is_last :
  decideReceiveProgressionByFacts true true false =
    UnderlyingReceiveRejectedDecision.
Proof. reflexivity. Qed.

Theorem receive_progression_decision_sound_complete :
  forall (parsedGrammarId parsedValueId correspondenceGrammarId correspondenceValueId : nat)
         underlying grammarMatches valueMatches underlyingAccepted,
    (grammarMatches = true <-> parsedGrammarId = correspondenceGrammarId) ->
    (valueMatches = true <-> parsedValueId = correspondenceValueId) ->
    (underlyingAccepted = true <-> underlying = UnderlyingAdvance) ->
    (decideReceiveProgressionByFacts grammarMatches valueMatches underlyingAccepted =
       ReceiveProgressionDecisionAccepted <->
     parsedGrammarId = correspondenceGrammarId /\
     parsedValueId = correspondenceValueId /\
     underlying = UnderlyingAdvance).
Proof.
  intros parsedGrammarId parsedValueId correspondenceGrammarId correspondenceValueId
    underlying grammarMatches valueMatches underlyingAccepted
    Hgrammar Hvalue Hunderlying.
  split.
  - intro Haccepted.
    apply receive_progression_acceptance_requires_all_reflected_facts in Haccepted.
    destruct Haccepted as [HgrammarFact [HvalueFact HunderlyingFact]].
    repeat split.
    + apply (proj1 Hgrammar). exact HgrammarFact.
    + apply (proj1 Hvalue). exact HvalueFact.
    + apply (proj1 Hunderlying). exact HunderlyingFact.
  - intros [HgrammarEq [HvalueEq HunderlyingEq]].
    assert (HgrammarFact : grammarMatches = true).
    { apply (proj2 Hgrammar). exact HgrammarEq. }
    assert (HvalueFact : valueMatches = true).
    { apply (proj2 Hvalue). exact HvalueEq. }
    assert (HunderlyingFact : underlyingAccepted = true).
    { apply (proj2 Hunderlying). exact HunderlyingEq. }
    rewrite HgrammarFact, HvalueFact, HunderlyingFact.
    reflexivity.
Qed.

Inductive CompleteEmissionDecision : Type :=
| CompleteEmissionDecisionAccepted
| InvalidEmissionExtentDecision
| PartialEmissionDecision
| EmissionPastDeclaredFrameDecision.

Definition decideEmissionDisposition
  (disposition : EmissionDisposition) : CompleteEmissionDecision :=
  match disposition with
  | InvalidEmissionExtent => InvalidEmissionExtentDecision
  | PartialEmission => PartialEmissionDecision
  | CompleteEmission => CompleteEmissionDecisionAccepted
  | EmissionPastDeclaredFrame => EmissionPastDeclaredFrameDecision
  end.

Theorem emission_decision_matches_certified_cases :
  decideEmissionDisposition InvalidEmissionExtent = InvalidEmissionExtentDecision /\
  decideEmissionDisposition PartialEmission = PartialEmissionDecision /\
  decideEmissionDisposition CompleteEmission = CompleteEmissionDecisionAccepted /\
  decideEmissionDisposition EmissionPastDeclaredFrame = EmissionPastDeclaredFrameDecision.
Proof. repeat split; reflexivity. Qed.

Record CompleteEmissionPlan (representation owner : Type) : Type :=
  mkCompleteEmissionPlan {
    plannedCompleteEmissionRepresentation : representation;
    plannedCompleteEmissionOwner : owner
  }.

Definition planCompleteEmission
  {representation owner : Type}
  (representationId : representation) (ownerId : owner)
  : CompleteEmissionPlan representation owner :=
  {| plannedCompleteEmissionRepresentation := representationId;
     plannedCompleteEmissionOwner := ownerId |}.

Theorem complete_emission_plan_is_exact :
  forall representation owner
         (representationId : representation) (ownerId : owner),
    plannedCompleteEmissionRepresentation
      (planCompleteEmission representationId ownerId) = representationId /\
    plannedCompleteEmissionOwner
      (planCompleteEmission representationId ownerId) = ownerId.
Proof.
  intros.
  split; reflexivity.
Qed.

Inductive SendProgressionDecision : Type :=
| SendProgressionDecisionAccepted
| SendEmissionRepresentationMismatchDecision
| SendEmissionOwnerMismatchDecision
| UnderlyingSendRejectedDecision.

Definition decideSendProgressionByFacts
  (representationMatches ownerMatches underlyingAccepted : bool)
  : SendProgressionDecision :=
  if representationMatches then
    if ownerMatches then
      if underlyingAccepted then
        SendProgressionDecisionAccepted
      else UnderlyingSendRejectedDecision
    else SendEmissionOwnerMismatchDecision
  else SendEmissionRepresentationMismatchDecision.

Theorem send_progression_all_reflected_facts_accept :
  decideSendProgressionByFacts true true true = SendProgressionDecisionAccepted.
Proof. reflexivity. Qed.

Theorem send_progression_acceptance_requires_all_reflected_facts :
  forall representationMatches ownerMatches underlyingAccepted,
    decideSendProgressionByFacts representationMatches ownerMatches underlyingAccepted =
      SendProgressionDecisionAccepted ->
    representationMatches = true /\ ownerMatches = true /\ underlyingAccepted = true.
Proof.
  intros representationMatches ownerMatches underlyingAccepted Haccepted.
  destruct representationMatches; simpl in Haccepted; try discriminate.
  destruct ownerMatches; simpl in Haccepted; try discriminate.
  destruct underlyingAccepted; simpl in Haccepted; try discriminate.
  repeat split; reflexivity.
Qed.

Theorem send_representation_mismatch_has_precedence :
  forall ownerMatches underlyingAccepted,
    decideSendProgressionByFacts false ownerMatches underlyingAccepted =
      SendEmissionRepresentationMismatchDecision.
Proof. reflexivity. Qed.

Theorem send_owner_mismatch_has_precedence :
  forall underlyingAccepted,
    decideSendProgressionByFacts true false underlyingAccepted =
      SendEmissionOwnerMismatchDecision.
Proof. reflexivity. Qed.

Theorem underlying_send_rejection_is_last :
  decideSendProgressionByFacts true true false = UnderlyingSendRejectedDecision.
Proof. reflexivity. Qed.

Theorem send_progression_decision_sound_complete :
  forall (generatedRepresentationId generatedOwner emissionRepresentationId emissionOwner : nat)
         underlying representationMatches ownerMatches underlyingAccepted,
    (representationMatches = true <-> generatedRepresentationId = emissionRepresentationId) ->
    (ownerMatches = true <-> generatedOwner = emissionOwner) ->
    (underlyingAccepted = true <-> underlying = UnderlyingAdvance) ->
    (decideSendProgressionByFacts representationMatches ownerMatches underlyingAccepted =
       SendProgressionDecisionAccepted <->
     generatedRepresentationId = emissionRepresentationId /\
     generatedOwner = emissionOwner /\
     underlying = UnderlyingAdvance).
Proof.
  intros generatedRepresentationId generatedOwner emissionRepresentationId emissionOwner
    underlying representationMatches ownerMatches underlyingAccepted
    Hrepresentation Howner Hunderlying.
  split.
  - intro Haccepted.
    apply send_progression_acceptance_requires_all_reflected_facts in Haccepted.
    destruct Haccepted as [HrepresentationFact [HownerFact HunderlyingFact]].
    repeat split.
    + apply (proj1 Hrepresentation). exact HrepresentationFact.
    + apply (proj1 Howner). exact HownerFact.
    + apply (proj1 Hunderlying). exact HunderlyingFact.
  - intros [HrepresentationEq [HownerEq HunderlyingEq]].
    assert (HrepresentationFact : representationMatches = true).
    { apply (proj2 Hrepresentation). exact HrepresentationEq. }
    assert (HownerFact : ownerMatches = true).
    { apply (proj2 Howner). exact HownerEq. }
    assert (HunderlyingFact : underlyingAccepted = true).
    { apply (proj2 Hunderlying). exact HunderlyingEq. }
    rewrite HrepresentationFact, HownerFact, HunderlyingFact.
    reflexivity.
Qed.
