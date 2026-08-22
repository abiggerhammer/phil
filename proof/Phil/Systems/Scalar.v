From Stdlib Require Import Arith.PeanoNat.

From Phil.Core Require Import Scalar.

(*
  PHIL-SYS-SCALAR-001 — proof-oriented model of the scalar-specific checks in
  Phil.Systems.Verify.

  The concrete verifier checks Data.Map identities and enumerates operations and
  terminators.  This normalized model removes container mechanics and captures
  the authority-relevant conditions:

  - a scalar literal output must name an existing TypedScalar value whose type
    is exactly the literal's intrinsic type;
  - the literal itself must satisfy the intrinsic Core range rule;
  - a scalar return must name an existing TypedScalar value;
  - all scalar-returning exits of one function agree on one scalar type.

  Correspondence to concrete Data.Map lookup/enumeration remains an
  implementation boundary.
*)

Definition ValueId := nat.
Definition ReturnSiteId := nat.

Record SystemsScalarModel : Type := mkSystemsScalarModel {
  systemsLiteralAt : ValueId -> option ScalarLiteral;
  systemsValueType : ValueId -> option ScalarType;
  systemsReturnValue : ReturnSiteId -> option ValueId
}.

Definition SystemsScalarVerificationSuccess
  (model : SystemsScalarModel) : Prop :=
  (forall value literal,
    systemsLiteralAt model value = Some literal ->
    ScalarLiteralValid literal /\
    systemsValueType model value = Some (scalarLiteralType literal)) /\
  (forall site value,
    systemsReturnValue model site = Some value ->
    exists scalarType,
      systemsValueType model value = Some scalarType) /\
  (forall leftSite rightSite leftValue rightValue leftType rightType,
    systemsReturnValue model leftSite = Some leftValue ->
    systemsReturnValue model rightSite = Some rightValue ->
    systemsValueType model leftValue = Some leftType ->
    systemsValueType model rightValue = Some rightType ->
    leftType = rightType).

Theorem verified_systems_literal_is_valid_and_exactly_typed :
  forall model value literal,
    SystemsScalarVerificationSuccess model ->
    systemsLiteralAt model value = Some literal ->
    ScalarLiteralValid literal /\
    systemsValueType model value = Some (scalarLiteralType literal).
Proof.
  intros model value literal Hverified Hliteral.
  destruct Hverified as [Hliterals _].
  apply Hliterals.
  exact Hliteral.
Qed.

Theorem verified_systems_return_names_scalar_value :
  forall model site value,
    SystemsScalarVerificationSuccess model ->
    systemsReturnValue model site = Some value ->
    exists scalarType,
      systemsValueType model value = Some scalarType.
Proof.
  intros model site value Hverified Hreturn.
  destruct Hverified as [_ [Hreturns _]].
  apply Hreturns.
  exact Hreturn.
Qed.

Theorem verified_systems_scalar_returns_have_one_type :
  forall model leftSite rightSite leftValue rightValue leftType rightType,
    SystemsScalarVerificationSuccess model ->
    systemsReturnValue model leftSite = Some leftValue ->
    systemsReturnValue model rightSite = Some rightValue ->
    systemsValueType model leftValue = Some leftType ->
    systemsValueType model rightValue = Some rightType ->
    leftType = rightType.
Proof.
  intros model leftSite rightSite leftValue rightValue leftType rightType
    Hverified HleftReturn HrightReturn HleftType HrightType.
  destruct Hverified as [_ [_ Hconsistent]].
  eapply Hconsistent; eauto.
Qed.

Theorem missing_scalar_literal_output_is_rejected :
  forall model value literal,
    systemsLiteralAt model value = Some literal ->
    systemsValueType model value = None ->
    ~ SystemsScalarVerificationSuccess model.
Proof.
  intros model value literal Hliteral Hmissing Hverified.
  pose proof
    (verified_systems_literal_is_valid_and_exactly_typed
      model value literal Hverified Hliteral) as Hexact.
  destruct Hexact as [_ Htype].
  rewrite Hmissing in Htype.
  discriminate.
Qed.

Theorem mismatched_scalar_literal_type_is_rejected :
  forall model value literal actualType,
    systemsLiteralAt model value = Some literal ->
    systemsValueType model value = Some actualType ->
    actualType <> scalarLiteralType literal ->
    ~ SystemsScalarVerificationSuccess model.
Proof.
  intros model value literal actualType Hliteral Hactual Hmismatch Hverified.
  pose proof
    (verified_systems_literal_is_valid_and_exactly_typed
      model value literal Hverified Hliteral) as Hexact.
  destruct Hexact as [_ Hexpected].
  rewrite Hactual in Hexpected.
  inversion Hexpected.
  contradiction.
Qed.

Theorem out_of_range_scalar_literal_is_rejected :
  forall model value literal,
    systemsLiteralAt model value = Some literal ->
    ~ ScalarLiteralValid literal ->
    ~ SystemsScalarVerificationSuccess model.
Proof.
  intros model value literal Hliteral Hinvalid Hverified.
  pose proof
    (verified_systems_literal_is_valid_and_exactly_typed
      model value literal Hverified Hliteral) as Hexact.
  destruct Hexact as [Hvalid _].
  contradiction.
Qed.

Theorem non_scalar_return_is_rejected :
  forall model site value,
    systemsReturnValue model site = Some value ->
    systemsValueType model value = None ->
    ~ SystemsScalarVerificationSuccess model.
Proof.
  intros model site value Hreturn Hmissing Hverified.
  pose proof
    (verified_systems_return_names_scalar_value
      model site value Hverified Hreturn) as Hscalar.
  destruct Hscalar as [scalarType Htype].
  rewrite Hmissing in Htype.
  discriminate.
Qed.

Theorem mismatched_scalar_return_types_are_rejected :
  forall model leftSite rightSite leftValue rightValue leftType rightType,
    systemsReturnValue model leftSite = Some leftValue ->
    systemsReturnValue model rightSite = Some rightValue ->
    systemsValueType model leftValue = Some leftType ->
    systemsValueType model rightValue = Some rightType ->
    leftType <> rightType ->
    ~ SystemsScalarVerificationSuccess model.
Proof.
  intros model leftSite rightSite leftValue rightValue leftType rightType
    HleftReturn HrightReturn HleftType HrightType Hmismatch Hverified.
  apply Hmismatch.
  eapply verified_systems_scalar_returns_have_one_type; eauto.
Qed.
