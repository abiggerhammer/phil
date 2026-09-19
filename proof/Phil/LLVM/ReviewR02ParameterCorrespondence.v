From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.LLVM Require Import Preservation.

Import ListNotations.

(*
  PHIL-P1-REVIEW-R02 — complete ordered LLVM function-parameter correspondence.

  Independent translation validation must compare the entire ordered parameter
  list produced by the independently selected lowerer against the candidate
  function.  Equality is positional and structural: omission, insertion, name
  drift, type drift, or reordering changes the list and therefore rejects.

  This aggregate boundary composes that exact parameter-list check with the
  existing PHIL-LLVM-PRESERVE-001 conservative translation verification.

  Concrete Text names, LLVMParameterType representation, lowerer selection,
  target-module Map traversal, and Haskell/LLVM renderer correspondence remain
  implementation boundaries exercised by the permanent R02 mutation corpus.
*)

Definition ParameterName := nat.
Definition ParameterType := nat.

Record ParameterFacts : Type := mkParameterFacts {
  parameterName : ParameterName;
  parameterType : ParameterType
}.

Definition ParameterListExact
  (expected actual : list ParameterFacts) : Prop :=
  actual = expected.

Theorem exact_parameter_list_preserves_length :
  forall expected actual,
    ParameterListExact expected actual ->
    length actual = length expected.
Proof.
  intros expected actual Hexact.
  unfold ParameterListExact in Hexact.
  subst actual.
  reflexivity.
Qed.

Theorem exact_parameter_list_preserves_every_position :
  forall expected actual index parameter,
    ParameterListExact expected actual ->
    nth_error expected index = Some parameter ->
    nth_error actual index = Some parameter.
Proof.
  intros expected actual index parameter Hexact Hexpected.
  unfold ParameterListExact in Hexact.
  subst actual.
  exact Hexpected.
Qed.

Theorem exact_parameter_list_preserves_name_at_every_position :
  forall expected actual index expectedParameter actualParameter,
    ParameterListExact expected actual ->
    nth_error expected index = Some expectedParameter ->
    nth_error actual index = Some actualParameter ->
    parameterName actualParameter = parameterName expectedParameter.
Proof.
  intros expected actual index expectedParameter actualParameter
    Hexact Hexpected Hactual.
  pose proof
    (exact_parameter_list_preserves_every_position
      expected actual index expectedParameter Hexact Hexpected) as Hsame.
  rewrite Hactual in Hsame.
  inversion Hsame.
  reflexivity.
Qed.

Theorem exact_parameter_list_preserves_type_at_every_position :
  forall expected actual index expectedParameter actualParameter,
    ParameterListExact expected actual ->
    nth_error expected index = Some expectedParameter ->
    nth_error actual index = Some actualParameter ->
    parameterType actualParameter = parameterType expectedParameter.
Proof.
  intros expected actual index expectedParameter actualParameter
    Hexact Hexpected Hactual.
  pose proof
    (exact_parameter_list_preserves_every_position
      expected actual index expectedParameter Hexact Hexpected) as Hsame.
  rewrite Hactual in Hsame.
  inversion Hsame.
  reflexivity.
Qed.

Theorem parameter_omission_or_insertion_rejects :
  forall expected actual,
    length actual <> length expected ->
    ~ ParameterListExact expected actual.
Proof.
  intros expected actual Hlength Hexact.
  apply Hlength.
  eapply exact_parameter_list_preserves_length.
  exact Hexact.
Qed.

Theorem positional_parameter_name_drift_rejects :
  forall expected actual index expectedParameter actualParameter,
    nth_error expected index = Some expectedParameter ->
    nth_error actual index = Some actualParameter ->
    parameterName actualParameter <> parameterName expectedParameter ->
    ~ ParameterListExact expected actual.
Proof.
  intros expected actual index expectedParameter actualParameter
    Hexpected Hactual Hname Hexact.
  apply Hname.
  eapply exact_parameter_list_preserves_name_at_every_position; eauto.
Qed.

Theorem positional_parameter_type_drift_rejects :
  forall expected actual index expectedParameter actualParameter,
    nth_error expected index = Some expectedParameter ->
    nth_error actual index = Some actualParameter ->
    parameterType actualParameter <> parameterType expectedParameter ->
    ~ ParameterListExact expected actual.
Proof.
  intros expected actual index expectedParameter actualParameter
    Hexpected Hactual Htype Hexact.
  apply Htype.
  eapply exact_parameter_list_preserves_type_at_every_position; eauto.
Qed.

Definition parameterA : ParameterFacts := mkParameterFacts 1 10.
Definition parameterB : ParameterFacts := mkParameterFacts 2 20.

Theorem swapped_distinct_parameters_are_not_exact :
  ~ ParameterListExact
      [parameterA; parameterB]
      [parameterB; parameterA].
Proof.
  unfold ParameterListExact, parameterA, parameterB.
  discriminate.
Qed.

Record R02TranslationValidationFacts : Type := mkR02TranslationValidationFacts {
  r02PreservationModel : Preservation.LLVMPreservationModel;
  r02ExpectedParameters : list ParameterFacts;
  r02ActualParameters : list ParameterFacts
}.

Definition R02TranslationValidationValid
  (facts : R02TranslationValidationFacts) : Prop :=
  Preservation.LLVMPreservationVerificationSuccess
    (r02PreservationModel facts) /\
  ParameterListExact
    (r02ExpectedParameters facts)
    (r02ActualParameters facts).

Theorem review_r02_requires_exact_complete_ordered_parameters :
  forall facts,
    R02TranslationValidationValid facts ->
    ParameterListExact
      (r02ExpectedParameters facts)
      (r02ActualParameters facts).
Proof.
  intros facts Hvalid.
  exact (proj2 Hvalid).
Qed.

Theorem review_r02_keeps_existing_llvm_preservation_gate :
  forall facts,
    R02TranslationValidationValid facts ->
    Preservation.LLVMPreservationVerificationSuccess
      (r02PreservationModel facts).
Proof.
  intros facts Hvalid.
  exact (proj1 Hvalid).
Qed.
