From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ProtocolMessageAdmissibility.

(*
  PHIL-PROT-MSG-001 — representation-neutral implementation correspondence.

  Concrete Haskell recursion discovers the exact semantic-shape and Core-type
  facts, preserves diagnostic paths/details, and remains responsible for
  Ty/SemanticForm/Text representation.  This layer owns the fail-closed
  protocol-specific admission decision over those reflected facts, in the same
  precedence as production:

    revision -> exact type -> exact semantics -> semantic shape -> hard type.

  Ownership transfer remains a separate downstream authority boundary.
*)

Inductive BoundaryMessageContractDecision : Type :=
| BoundaryMessageContractAcceptedDecision
| BoundaryMessageRevisionEmptyDecision
| BoundaryMessageTypeMismatchDecision
| BoundaryMessageSemanticsMismatchDecision
| BoundaryMessageShapeRejectedDecision
| BoundaryMessageHardTypeRejectedDecision.

Definition decideBoundaryMessageContractByFacts
  (revisionNonempty typeMatches semanticsMatches shapeAllows hardTypeAllows : bool)
  : BoundaryMessageContractDecision :=
  if revisionNonempty then
    if typeMatches then
      if semanticsMatches then
        if shapeAllows then
          if hardTypeAllows then
            BoundaryMessageContractAcceptedDecision
          else BoundaryMessageHardTypeRejectedDecision
        else BoundaryMessageShapeRejectedDecision
      else BoundaryMessageSemanticsMismatchDecision
    else BoundaryMessageTypeMismatchDecision
  else BoundaryMessageRevisionEmptyDecision.

Inductive IntrinsicBoundaryMessageDecision : Type :=
| IntrinsicBoundaryMessageAcceptedDecision
| IntrinsicBoundaryMessageRequiresContractDecision.

Definition decideIntrinsicBoundaryMessageByFact
  (intrinsicAllows : bool) : IntrinsicBoundaryMessageDecision :=
  if intrinsicAllows then
    IntrinsicBoundaryMessageAcceptedDecision
  else
    IntrinsicBoundaryMessageRequiresContractDecision.

Theorem exact_boundary_message_facts_accept :
  decideBoundaryMessageContractByFacts true true true true true =
    BoundaryMessageContractAcceptedDecision.
Proof. reflexivity. Qed.

Theorem empty_revision_has_first_precedence :
  forall typeMatches semanticsMatches shapeAllows hardTypeAllows,
    decideBoundaryMessageContractByFacts
      false typeMatches semanticsMatches shapeAllows hardTypeAllows =
      BoundaryMessageRevisionEmptyDecision.
Proof. reflexivity. Qed.

Theorem type_mismatch_has_second_precedence :
  forall semanticsMatches shapeAllows hardTypeAllows,
    decideBoundaryMessageContractByFacts
      true false semanticsMatches shapeAllows hardTypeAllows =
      BoundaryMessageTypeMismatchDecision.
Proof. reflexivity. Qed.

Theorem semantics_mismatch_has_third_precedence :
  forall shapeAllows hardTypeAllows,
    decideBoundaryMessageContractByFacts
      true true false shapeAllows hardTypeAllows =
      BoundaryMessageSemanticsMismatchDecision.
Proof. reflexivity. Qed.

Theorem shape_rejection_has_fourth_precedence :
  forall hardTypeAllows,
    decideBoundaryMessageContractByFacts true true true false hardTypeAllows =
      BoundaryMessageShapeRejectedDecision.
Proof. reflexivity. Qed.

Theorem hard_type_rejection_has_last_precedence :
  decideBoundaryMessageContractByFacts true true true true false =
    BoundaryMessageHardTypeRejectedDecision.
Proof. reflexivity. Qed.

Theorem reflected_boundary_message_decision_is_sound_and_complete :
  forall actualType actualSemantics contract
         revisionNonempty typeMatches semanticsMatches shapeAllows hardTypeAllows,
    (revisionNonempty = true <-> messageContractRevision contract <> 0) ->
    (typeMatches = true <-> messageContractType contract = actualType) ->
    (semanticsMatches = true <->
      messageContractSemantics contract = actualSemantics) ->
    (shapeAllows = true <->
      shapeAdmissible (messageContractShape contract) = true) ->
    (hardTypeAllows = true <-> hardTypeAdmissible actualType = true) ->
    (decideBoundaryMessageContractByFacts
       revisionNonempty typeMatches semanticsMatches shapeAllows hardTypeAllows =
       BoundaryMessageContractAcceptedDecision <->
     MessageContractAccepted actualType actualSemantics contract).
Proof.
  intros actualType actualSemantics contract
    revisionNonempty typeMatches semanticsMatches shapeAllows hardTypeAllows
    Hrevision Htype Hsemantics Hshape Hhard.
  split.
  - intro Hdecision.
    destruct revisionNonempty eqn:HrevisionFact; simpl in Hdecision; try discriminate.
    destruct typeMatches eqn:HtypeFact; simpl in Hdecision; try discriminate.
    destruct semanticsMatches eqn:HsemanticsFact; simpl in Hdecision; try discriminate.
    destruct shapeAllows eqn:HshapeFact; simpl in Hdecision; try discriminate.
    destruct hardTypeAllows eqn:HhardFact; simpl in Hdecision; try discriminate.
    unfold MessageContractAccepted.
    repeat split.
    + apply (proj1 Hrevision). exact HrevisionFact.
    + apply (proj1 Htype). exact HtypeFact.
    + apply (proj1 Hsemantics). exact HsemanticsFact.
    + apply (proj1 Hshape). exact HshapeFact.
    + apply (proj1 Hhard). exact HhardFact.
  - intro Haccepted.
    unfold MessageContractAccepted in Haccepted.
    destruct Haccepted as
      [HrevisionAccepted
        [HtypeAccepted
          [HsemanticsAccepted [HshapeAccepted HhardAccepted]]]].
    apply (proj2 Hrevision) in HrevisionAccepted.
    apply (proj2 Htype) in HtypeAccepted.
    apply (proj2 Hsemantics) in HsemanticsAccepted.
    apply (proj2 Hshape) in HshapeAccepted.
    apply (proj2 Hhard) in HhardAccepted.
    rewrite HrevisionAccepted, HtypeAccepted, HsemanticsAccepted,
      HshapeAccepted, HhardAccepted.
    reflexivity.
Qed.

Theorem reflected_intrinsic_message_decision_is_sound_and_complete :
  forall ty intrinsicAllows,
    (intrinsicAllows = true <-> intrinsicMessageType ty = true) ->
    (decideIntrinsicBoundaryMessageByFact intrinsicAllows =
       IntrinsicBoundaryMessageAcceptedDecision <->
     intrinsicMessageType ty = true).
Proof.
  intros ty intrinsicAllows Hreflection.
  split.
  - intro Hdecision.
    destruct intrinsicAllows eqn:Hintrinsic; simpl in Hdecision; try discriminate.
    apply (proj1 Hreflection).
    exact Hintrinsic.
  - intro Hadmitted.
    apply (proj2 Hreflection) in Hadmitted.
    rewrite Hadmitted.
    reflexivity.
Qed.
