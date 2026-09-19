From Stdlib Require Import Lists.List.

From Phil.LLVM Require Import Preservation.

Import ListNotations.

(*
  PHIL-P1-REVIEW-R03 — closed-world LLVM function coverage.

  Independent translation validation selects a lowerer, reconstructs the
  expected LLVM module, and requires the candidate module to expose exactly the
  same complete function inventory.  A target-only function is therefore not
  an implicit helper: it is rejected unless the selected lowerer itself emits
  that function.

  Concrete Text names, Map key ordering, selected-lowerer execution, and
  Haskell/LLVM renderer correspondence remain implementation boundaries
  exercised by the permanent R03 mutation corpus.
*)

Definition FunctionId := nat.

Definition FunctionInventoryExact
  (expected actual : list FunctionId) : Prop :=
  actual = expected.

Theorem exact_function_inventory_preserves_membership :
  forall expected actual functionId,
    FunctionInventoryExact expected actual ->
    (In functionId actual <-> In functionId expected).
Proof.
  intros expected actual functionId Hexact.
  unfold FunctionInventoryExact in Hexact.
  subst actual.
  split; intro Hin; exact Hin.
Qed.

Theorem unadvertised_target_function_rejects :
  forall expected actual functionId,
    In functionId actual ->
    ~ In functionId expected ->
    ~ FunctionInventoryExact expected actual.
Proof.
  intros expected actual functionId Hactual HnotExpected Hexact.
  apply HnotExpected.
  apply (proj1
    (exact_function_inventory_preserves_membership
      expected actual functionId Hexact)).
  exact Hactual.
Qed.

Theorem omitted_expected_function_rejects :
  forall expected actual functionId,
    In functionId expected ->
    ~ In functionId actual ->
    ~ FunctionInventoryExact expected actual.
Proof.
  intros expected actual functionId Hexpected HnotActual Hexact.
  apply HnotActual.
  apply (proj2
    (exact_function_inventory_preserves_membership
      expected actual functionId Hexact)).
  exact Hexpected.
Qed.

Theorem selected_lowerer_may_explicitly_admit_helper :
  forall expectedPrefix helper expectedSuffix,
    FunctionInventoryExact
      (expectedPrefix ++ (helper :: expectedSuffix))
      (expectedPrefix ++ (helper :: expectedSuffix)).
Proof.
  intros.
  reflexivity.
Qed.

Record R03TranslationValidationFacts : Type := mkR03TranslationValidationFacts {
  r03PreservationModel : Preservation.LLVMPreservationModel;
  r03ExpectedFunctions : list FunctionId;
  r03ActualFunctions : list FunctionId
}.

Definition R03TranslationValidationValid
  (facts : R03TranslationValidationFacts) : Prop :=
  Preservation.LLVMPreservationVerificationSuccess
    (r03PreservationModel facts) /\
  FunctionInventoryExact
    (r03ExpectedFunctions facts)
    (r03ActualFunctions facts).

Theorem review_r03_requires_closed_world_function_inventory :
  forall facts,
    R03TranslationValidationValid facts ->
    FunctionInventoryExact
      (r03ExpectedFunctions facts)
      (r03ActualFunctions facts).
Proof.
  intros facts Hvalid.
  exact (proj2 Hvalid).
Qed.

Theorem review_r03_keeps_existing_llvm_preservation_gate :
  forall facts,
    R03TranslationValidationValid facts ->
    Preservation.LLVMPreservationVerificationSuccess
      (r03PreservationModel facts).
Proof.
  intros facts Hvalid.
  exact (proj1 Hvalid).
Qed.
