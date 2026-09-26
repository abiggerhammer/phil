From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  Defensive proof-correspondence slice for D-NUM-RESULT-SUBJECT-01.

  Numeric conversion can preserve a mathematical value exactly without proving
  that the value has been attached to the semantic subject required by a later
  dependent consumer.  This model therefore keeps the actual returned numeric
  result, width, magnitude, subject, and consuming operation distinct.

  The native implementation remains responsible for reflecting the authentic
  returned value and dependent consumer into this relation.  This proof does
  not manufacture a subject identity, infer identity from source spelling or
  type equality, restore resource ownership, or change the Phase 1 TCB.
*)

Definition NumericResultId := nat.
Definition NumericConsumerId := nat.
Definition NumericSubjectId := nat.
Definition NumericWidth := nat.
Definition NumericMagnitude := nat.

Record NumericResultSubjectModel : Type :=
  mkNumericResultSubjectModel {
    modelActualNumericResult : NumericResultId -> bool;
    modelResultWidth : NumericResultId -> option NumericWidth;
    modelResultMagnitude : NumericResultId -> option NumericMagnitude;
    modelResultSubject : NumericResultId -> option NumericSubjectId;
    modelConsumerResult : NumericConsumerId -> option NumericResultId;
    modelConsumerWidth : NumericConsumerId -> option NumericWidth;
    modelConsumerMagnitude : NumericConsumerId -> option NumericMagnitude;
    modelConsumerSubject : NumericConsumerId -> option NumericSubjectId;
    modelConsumerConversionExact : NumericConsumerId -> bool;
    modelConsumerAcceptsDependentSubject : NumericConsumerId -> bool
  }.

Definition WeakSameTypedExactNumericUse
  (model : NumericResultSubjectModel) : Prop :=
  forall consumer result,
    modelActualNumericResult model result = true ->
    modelConsumerResult model consumer = Some result ->
    exists width magnitude,
      modelResultWidth model result = Some width /\
      modelResultMagnitude model result = Some magnitude /\
      modelConsumerWidth model consumer = Some width /\
      modelConsumerMagnitude model consumer = Some magnitude /\
      modelConsumerConversionExact model consumer = true /\
      modelConsumerAcceptsDependentSubject model consumer = true.

Definition ExactReturnedNumericSubjectCorrespondence
  (model : NumericResultSubjectModel) : Prop :=
  forall consumer result,
    modelActualNumericResult model result = true ->
    modelConsumerResult model consumer = Some result ->
    exists width magnitude subject,
      modelResultWidth model result = Some width /\
      modelResultMagnitude model result = Some magnitude /\
      modelResultSubject model result = Some subject /\
      modelConsumerWidth model consumer = Some width /\
      modelConsumerMagnitude model consumer = Some magnitude /\
      modelConsumerSubject model consumer = Some subject /\
      modelConsumerConversionExact model consumer = true /\
      modelConsumerAcceptsDependentSubject model consumer = true.

Definition wrongSubjectExactConversionWitness : NumericResultSubjectModel :=
  mkNumericResultSubjectModel
    (fun result => Nat.eqb result 7)
    (fun result => if Nat.eqb result 7 then Some 32 else None)
    (fun result => if Nat.eqb result 7 then Some 7 else None)
    (fun result => if Nat.eqb result 7 then Some 70 else None)
    (fun consumer => if Nat.eqb consumer 1 then Some 7 else None)
    (fun consumer => if Nat.eqb consumer 1 then Some 32 else None)
    (fun consumer => if Nat.eqb consumer 1 then Some 7 else None)
    (fun consumer => if Nat.eqb consumer 1 then Some 71 else None)
    (fun consumer => Nat.eqb consumer 1)
    (fun consumer => Nat.eqb consumer 1).

Theorem wrong_subject_still_has_same_typed_exact_numeric_use :
  WeakSameTypedExactNumericUse wrongSubjectExactConversionWitness.
Proof.
  intros consumer result Hactual Hlink.
  cbn in Hactual.
  apply Nat.eqb_eq in Hactual.
  subst result.
  cbn in Hlink.
  destruct (Nat.eqb consumer 1) eqn:Hconsumer.
  - apply Nat.eqb_eq in Hconsumer.
    subst consumer.
    exists 32, 7.
    repeat split; reflexivity.
  - discriminate Hlink.
Qed.

Theorem exact_conversion_on_unrelated_subject_is_insufficient :
  ~ ExactReturnedNumericSubjectCorrespondence
      wrongSubjectExactConversionWitness.
Proof.
  intro Hcorrespondence.
  pose proof
    (Hcorrespondence 1 7 eq_refl eq_refl)
    as Hexact.
  destruct Hexact as
    [width [magnitude [subject
      [Hwidth [Hmagnitude [Hsubject
        [HconsumerWidth [HconsumerMagnitude
          [HconsumerSubject [Hconversion Haccepts]]]]]]]]]].
  cbn in Hwidth, Hmagnitude, Hsubject,
    HconsumerWidth, HconsumerMagnitude, HconsumerSubject.
  inversion Hwidth; subst width.
  inversion Hmagnitude; subst magnitude.
  inversion Hsubject; subst subject.
  discriminate HconsumerSubject.
Qed.

Definition exactReturnedSubjectWitness : NumericResultSubjectModel :=
  mkNumericResultSubjectModel
    (fun result => Nat.eqb result 7)
    (fun result => if Nat.eqb result 7 then Some 32 else None)
    (fun result => if Nat.eqb result 7 then Some 7 else None)
    (fun result => if Nat.eqb result 7 then Some 70 else None)
    (fun consumer => if Nat.eqb consumer 1 then Some 7 else None)
    (fun consumer => if Nat.eqb consumer 1 then Some 32 else None)
    (fun consumer => if Nat.eqb consumer 1 then Some 7 else None)
    (fun consumer => if Nat.eqb consumer 1 then Some 70 else None)
    (fun consumer => Nat.eqb consumer 1)
    (fun consumer => Nat.eqb consumer 1).

Theorem exact_returned_subject_reaches_dependent_consumer :
  ExactReturnedNumericSubjectCorrespondence exactReturnedSubjectWitness.
Proof.
  intros consumer result Hactual Hlink.
  cbn in Hactual.
  apply Nat.eqb_eq in Hactual.
  subst result.
  cbn in Hlink.
  destruct (Nat.eqb consumer 1) eqn:Hconsumer.
  - apply Nat.eqb_eq in Hconsumer.
    subst consumer.
    exists 32, 7, 70.
    repeat split; reflexivity.
  - discriminate Hlink.
Qed.

Theorem numeric_result_subject_boundary_distinguishes_value_and_identity :
  WeakSameTypedExactNumericUse wrongSubjectExactConversionWitness /\
  ~ ExactReturnedNumericSubjectCorrespondence
      wrongSubjectExactConversionWitness /\
  ExactReturnedNumericSubjectCorrespondence exactReturnedSubjectWitness.
Proof.
  split.
  - exact wrong_subject_still_has_same_typed_exact_numeric_use.
  - split.
    + exact exact_conversion_on_unrelated_subject_is_insufficient.
    + exact exact_returned_subject_reaches_dependent_consumer.
Qed.
