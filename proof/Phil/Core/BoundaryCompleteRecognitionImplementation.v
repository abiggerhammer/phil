From Stdlib Require Import ZArith.
From Phil.Core Require Import BoundaryCompleteRecognition.

Open Scope Z_scope.

(*
  PHIL-BND-COMPLETE-001 — executable implementation correspondence.

  Concrete Haskell Int representation and comparison remain native.  This
  extracted layer owns only the ordered complete-frame extent classification
  over reflected primitive facts.  Exact witness/failure provenance and
  pending-recognition finalization remain predecessor recognition obligations.
*)

Definition decideCompleteExtentByFacts
  (declaredNegative consumedNegative consumedBeforeDeclared
   declaredBeforeConsumed : bool) : ExtentCheck :=
  if declaredNegative then ExtentInvalid
  else if consumedNegative then ExtentInvalid
  else if consumedBeforeDeclared then ExtentTrailing
  else if declaredBeforeConsumed then ExtentPast
  else ExtentComplete.

Definition reflectedCompleteExtentDecision
  (extent : RecognitionExtent) : ExtentCheck :=
  decideCompleteExtentByFacts
    (Z.ltb (declaredFrameBytes extent) 0)
    (Z.ltb (consumedFrameBytes extent) 0)
    (Z.ltb (consumedFrameBytes extent) (declaredFrameBytes extent))
    (Z.ltb (declaredFrameBytes extent) (consumedFrameBytes extent)).

Theorem reflected_complete_extent_decision_exact :
  forall extent,
    reflectedCompleteExtentDecision extent = checkCompleteExtent extent.
Proof.
  intros [declared consumed].
  reflexivity.
Qed.

Theorem reflected_complete_extent_accept_iff_certified_complete :
  forall extent,
    reflectedCompleteExtentDecision extent = ExtentComplete <->
    CompleteExtent extent.
Proof.
  intro extent.
  rewrite reflected_complete_extent_decision_exact.
  apply check_complete_extent_complete_iff.
Qed.

Theorem complete_extent_decision_requires_all_rejection_facts_false :
  forall declaredNegative consumedNegative consumedBeforeDeclared
    declaredBeforeConsumed,
    decideCompleteExtentByFacts
      declaredNegative consumedNegative consumedBeforeDeclared
      declaredBeforeConsumed = ExtentComplete ->
    declaredNegative = false /\
    consumedNegative = false /\
    consumedBeforeDeclared = false /\
    declaredBeforeConsumed = false.
Proof.
  intros declaredNegative consumedNegative consumedBeforeDeclared
    declaredBeforeConsumed.
  destruct declaredNegative, consumedNegative, consumedBeforeDeclared,
    declaredBeforeConsumed; simpl; intro H; try discriminate;
    repeat split; reflexivity.
Qed.

Theorem all_rejection_facts_false_are_sufficient_for_complete_extent :
  decideCompleteExtentByFacts false false false false = ExtentComplete.
Proof.
  reflexivity.
Qed.

Theorem declared_negative_has_first_rejection_precedence :
  forall consumedNegative consumedBeforeDeclared declaredBeforeConsumed,
    decideCompleteExtentByFacts
      true consumedNegative consumedBeforeDeclared declaredBeforeConsumed =
      ExtentInvalid.
Proof.
  reflexivity.
Qed.

Theorem consumed_negative_has_second_rejection_precedence :
  forall consumedBeforeDeclared declaredBeforeConsumed,
    decideCompleteExtentByFacts
      false true consumedBeforeDeclared declaredBeforeConsumed = ExtentInvalid.
Proof.
  reflexivity.
Qed.

Theorem trailing_has_precedence_over_past_after_nonnegative_facts :
  forall declaredBeforeConsumed,
    decideCompleteExtentByFacts false false true declaredBeforeConsumed =
      ExtentTrailing.
Proof.
  reflexivity.
Qed.

Theorem past_is_selected_only_after_nonnegative_nontrailing_facts :
  decideCompleteExtentByFacts false false false true = ExtentPast.
Proof.
  reflexivity.
Qed.
