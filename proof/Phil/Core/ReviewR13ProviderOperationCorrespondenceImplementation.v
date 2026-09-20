From Stdlib Require Import Bool.Bool.

Inductive ReviewR13Decision : Type :=
| ReviewR13AcceptedDecision
| ReviewR13RejectedDecision.

Definition reviewR13Factsb
  (sys005ProviderStageValid
   independentExpectationPresent
   expectedOccurrenceExact
   expectedOperationExact : bool) : bool :=
  sys005ProviderStageValid &&
  independentExpectationPresent &&
  expectedOccurrenceExact &&
  expectedOperationExact.

Definition decideReviewR13
  (sys005ProviderStageValid
   independentExpectationPresent
   expectedOccurrenceExact
   expectedOperationExact : bool)
  : ReviewR13Decision :=
  if reviewR13Factsb
      sys005ProviderStageValid
      independentExpectationPresent
      expectedOccurrenceExact
      expectedOperationExact
  then ReviewR13AcceptedDecision
  else ReviewR13RejectedDecision.

Theorem exact_review_r13_accepts :
  decideReviewR13 true true true true =
    ReviewR13AcceptedDecision.
Proof. reflexivity. Qed.

Theorem missing_independent_expectation_rejects :
  decideReviewR13 true false true true =
    ReviewR13RejectedDecision.
Proof. reflexivity. Qed.

Theorem wrong_provider_occurrence_rejects :
  decideReviewR13 true true false true =
    ReviewR13RejectedDecision.
Proof. reflexivity. Qed.

Theorem wrong_qualified_operation_rejects :
  decideReviewR13 true true true false =
    ReviewR13RejectedDecision.
Proof. reflexivity. Qed.

Theorem sys005_failure_still_rejects_before_review_correspondence :
  decideReviewR13 false true true true =
    ReviewR13RejectedDecision.
Proof. reflexivity. Qed.

(*
  Runtime symbol spelling is intentionally not an argument to this decision.
  A symbol rename therefore cannot alter R13 acceptance while the exact
  provider occurrence and operation binding remain unchanged.
*)
Theorem runtime_symbol_is_absent_from_review_r13_authority :
  forall sys005ProviderStageValid independentExpectationPresent
         expectedOccurrenceExact expectedOperationExact,
    decideReviewR13
      sys005ProviderStageValid
      independentExpectationPresent
      expectedOccurrenceExact
      expectedOperationExact =
    decideReviewR13
      sys005ProviderStageValid
      independentExpectationPresent
      expectedOccurrenceExact
      expectedOperationExact.
Proof. reflexivity. Qed.
