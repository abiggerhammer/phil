From Phil.Core Require Import Scalar.

(*
  PHIL-SURF-SYS-PROJ-001 — proof-oriented model of the independent
  Surface -> Systems projection validator introduced by PR #36.

  The concrete runnable fragment first checks the Surface component under its
  contextual result judgment, lowers it, verifies Systems, verifies scalar
  dataflow, and then independently reconstructs the expected source projection.
  This proof models that final semantic correspondence gate.

  In particular, successful projection validation requires:

  - source integer literals to be intrinsically valid at the contextual scalar
    type;
  - source aliases to resolve to the same value identity as the aliased binding;
  - every target scalar definition to have the contextual scalar type;
  - every source named literal to occur at the same target value identity with
    exactly the same literal;
  - a variable return to preserve the exact expected value identity;
  - a direct literal return to preserve the exact returned literal value;
  - no invented scalar definitions, except the one definition permitted to
    realize a direct literal return.

  Concrete parsing/checking, Text/ValueId correspondence, Data.Map duplicate
  normalization, Systems container enumeration, and correspondence from this
  normalized model to the Haskell validator remain implementation boundaries.
*)

Definition ProjectionValueId := nat.
Definition BindingId := nat.

Inductive ExpectedScalarReturn : Type :=
| ExpectedReturnValue : ProjectionValueId -> ExpectedScalarReturn
| ExpectedReturnLiteral : ScalarLiteral -> ExpectedScalarReturn.

Record SurfaceScalarProjectionModel : Type := mkSurfaceScalarProjectionModel {
  projectionScalarType : ScalarType;
  projectionNamedLiteralAt : ProjectionValueId -> option ScalarLiteral;
  projectionBindingValue : BindingId -> option ProjectionValueId;
  projectionAliasOf : BindingId -> option BindingId;
  projectionReturn : ExpectedScalarReturn
}.

Record SystemsScalarProjectionModel : Type := mkSystemsScalarProjectionModel {
  targetScalarLiteralAt : ProjectionValueId -> option ScalarLiteral;
  targetScalarTypeAt : ProjectionValueId -> option ScalarType;
  targetScalarReturn : option ProjectionValueId
}.

Definition RunnableScalarJudgment
  (source : SurfaceScalarProjectionModel) : Prop :=
  (forall value literal,
    projectionNamedLiteralAt source value = Some literal ->
    ScalarLiteralValid literal /\
    scalarLiteralType literal = projectionScalarType source) /\
  (forall alias sourceBinding,
    projectionAliasOf source alias = Some sourceBinding ->
    exists value,
      projectionBindingValue source sourceBinding = Some value /\
      projectionBindingValue source alias = Some value).

Definition TargetScalarSetExact
  (target : SystemsScalarProjectionModel) : Prop :=
  forall value,
    (exists literal,
      targetScalarLiteralAt target value = Some literal) <->
    (exists scalarType,
      targetScalarTypeAt target value = Some scalarType).

Definition SurfaceSystemsProjectionSuccess
  (source : SurfaceScalarProjectionModel)
  (target : SystemsScalarProjectionModel) : Prop :=
  RunnableScalarJudgment source /\
  TargetScalarSetExact target /\
  (forall value actualType,
    targetScalarTypeAt target value = Some actualType ->
    actualType = projectionScalarType source) /\
  (forall value expectedLiteral,
    projectionNamedLiteralAt source value = Some expectedLiteral ->
    targetScalarLiteralAt target value = Some expectedLiteral) /\
  match projectionReturn source with
  | ExpectedReturnValue expectedValue =>
      targetScalarReturn target = Some expectedValue /\
      forall value literal,
        targetScalarLiteralAt target value = Some literal ->
        projectionNamedLiteralAt source value = Some literal
  | ExpectedReturnLiteral expectedLiteral =>
      exists returnedValue,
        targetScalarReturn target = Some returnedValue /\
        targetScalarLiteralAt target returnedValue = Some expectedLiteral /\
        forall value literal,
          targetScalarLiteralAt target value = Some literal ->
          projectionNamedLiteralAt source value = Some literal \/
          (value = returnedValue /\ literal = expectedLiteral)
  end.

Theorem verified_projection_has_runnable_source_judgment :
  forall source target,
    SurfaceSystemsProjectionSuccess source target ->
    RunnableScalarJudgment source.
Proof.
  intros source target Hverified.
  destruct Hverified as [Hsource _].
  exact Hsource.
Qed.

Theorem verified_named_literal_preserves_identity_type_and_value :
  forall source target value literal,
    SurfaceSystemsProjectionSuccess source target ->
    projectionNamedLiteralAt source value = Some literal ->
    ScalarLiteralValid literal /\
    scalarLiteralType literal = projectionScalarType source /\
    targetScalarLiteralAt target value = Some literal.
Proof.
  intros source target value literal Hverified HsourceLiteral.
  destruct Hverified as [Hsource [_ [_ [Hliterals _]]]].
  destruct Hsource as [HsourceLiterals _].
  pose proof (HsourceLiterals value literal HsourceLiteral) as Hvalid.
  destruct Hvalid as [Hrange Htype].
  split.
  - exact Hrange.
  - split.
    + exact Htype.
    + apply Hliterals.
      exact HsourceLiteral.
Qed.

Theorem verified_target_scalar_has_contextual_type :
  forall source target value actualType,
    SurfaceSystemsProjectionSuccess source target ->
    targetScalarTypeAt target value = Some actualType ->
    actualType = projectionScalarType source.
Proof.
  intros source target value actualType Hverified HtargetType.
  destruct Hverified as [_ [_ [Htypes _]]].
  apply Htypes with (value := value).
  exact HtargetType.
Qed.

Theorem verified_target_definition_has_scalar_value_entry :
  forall source target value literal,
    SurfaceSystemsProjectionSuccess source target ->
    targetScalarLiteralAt target value = Some literal ->
    exists scalarType,
      targetScalarTypeAt target value = Some scalarType.
Proof.
  intros source target value literal Hverified Hdefinition.
  destruct Hverified as [_ [Hset _]].
  apply (proj1 (Hset value)).
  exists literal.
  exact Hdefinition.
Qed.

Theorem verified_surface_alias_reuses_value_identity :
  forall source target alias sourceBinding,
    SurfaceSystemsProjectionSuccess source target ->
    projectionAliasOf source alias = Some sourceBinding ->
    exists value,
      projectionBindingValue source sourceBinding = Some value /\
      projectionBindingValue source alias = Some value.
Proof.
  intros source target alias sourceBinding Hverified Halias.
  pose proof
    (verified_projection_has_runnable_source_judgment
      source target Hverified) as Hsource.
  destruct Hsource as [_ Haliases].
  apply Haliases with (alias := alias) (sourceBinding := sourceBinding).
  exact Halias.
Qed.

Theorem verified_variable_return_preserves_exact_identity :
  forall source target expectedValue,
    SurfaceSystemsProjectionSuccess source target ->
    projectionReturn source = ExpectedReturnValue expectedValue ->
    targetScalarReturn target = Some expectedValue.
Proof.
  intros source target expectedValue Hverified Hreturn.
  destruct Hverified as [_ [_ [_ [_ Hprojection]]]].
  rewrite Hreturn in Hprojection.
  destruct Hprojection as [Hexact _].
  exact Hexact.
Qed.

Theorem verified_direct_literal_return_preserves_exact_value :
  forall source target expectedLiteral,
    SurfaceSystemsProjectionSuccess source target ->
    projectionReturn source = ExpectedReturnLiteral expectedLiteral ->
    exists returnedValue,
      targetScalarReturn target = Some returnedValue /\
      targetScalarLiteralAt target returnedValue = Some expectedLiteral.
Proof.
  intros source target expectedLiteral Hverified Hreturn.
  destruct Hverified as [_ [_ [_ [_ Hprojection]]]].
  rewrite Hreturn in Hprojection.
  destruct Hprojection as
    [returnedValue [HtargetReturn [HtargetLiteral _]]].
  exists returnedValue.
  split.
  - exact HtargetReturn.
  - exact HtargetLiteral.
Qed.

Theorem verified_variable_return_has_no_invented_scalar_definition :
  forall source target expectedValue value literal,
    SurfaceSystemsProjectionSuccess source target ->
    projectionReturn source = ExpectedReturnValue expectedValue ->
    targetScalarLiteralAt target value = Some literal ->
    projectionNamedLiteralAt source value = Some literal.
Proof.
  intros source target expectedValue value literal Hverified Hreturn Hdefinition.
  destruct Hverified as [_ [_ [_ [_ Hprojection]]]].
  rewrite Hreturn in Hprojection.
  destruct Hprojection as [_ HnoInvented].
  apply HnoInvented.
  exact Hdefinition.
Qed.

Theorem source_literal_drift_is_rejected :
  forall source target value expectedLiteral actualLiteral,
    projectionNamedLiteralAt source value = Some expectedLiteral ->
    targetScalarLiteralAt target value = Some actualLiteral ->
    actualLiteral <> expectedLiteral ->
    ~ SurfaceSystemsProjectionSuccess source target.
Proof.
  intros source target value expectedLiteral actualLiteral
    HsourceLiteral HtargetLiteral Hmismatch Hverified.
  pose proof
    (verified_named_literal_preserves_identity_type_and_value
      source target value expectedLiteral Hverified HsourceLiteral) as Hexact.
  destruct Hexact as [_ [_ HexpectedTarget]].
  rewrite HtargetLiteral in HexpectedTarget.
  inversion HexpectedTarget.
  contradiction.
Qed.

Theorem scalar_type_drift_is_rejected :
  forall source target value actualType,
    targetScalarTypeAt target value = Some actualType ->
    actualType <> projectionScalarType source ->
    ~ SurfaceSystemsProjectionSuccess source target.
Proof.
  intros source target value actualType HtargetType Hmismatch Hverified.
  apply Hmismatch.
  exact
    (verified_target_scalar_has_contextual_type
      source target value actualType Hverified HtargetType).
Qed.

Theorem variable_return_target_drift_is_rejected :
  forall source target expectedValue actualValue,
    projectionReturn source = ExpectedReturnValue expectedValue ->
    targetScalarReturn target = Some actualValue ->
    actualValue <> expectedValue ->
    ~ SurfaceSystemsProjectionSuccess source target.
Proof.
  intros source target expectedValue actualValue HsourceReturn HtargetReturn
    Hmismatch Hverified.
  pose proof
    (verified_variable_return_preserves_exact_identity
      source target expectedValue Hverified HsourceReturn) as Hexact.
  rewrite HtargetReturn in Hexact.
  inversion Hexact.
  contradiction.
Qed.

Theorem direct_literal_return_value_drift_is_rejected :
  forall source target expectedLiteral returnedValue actualLiteral,
    projectionReturn source = ExpectedReturnLiteral expectedLiteral ->
    targetScalarReturn target = Some returnedValue ->
    targetScalarLiteralAt target returnedValue = Some actualLiteral ->
    actualLiteral <> expectedLiteral ->
    ~ SurfaceSystemsProjectionSuccess source target.
Proof.
  intros source target expectedLiteral returnedValue actualLiteral
    HsourceReturn HtargetReturn HactualLiteral Hmismatch Hverified.
  pose proof
    (verified_direct_literal_return_preserves_exact_value
      source target expectedLiteral Hverified HsourceReturn) as Hpreserved.
  destruct Hpreserved as
    [verifiedReturn [HverifiedReturn HverifiedLiteral]].
  rewrite HtargetReturn in HverifiedReturn.
  inversion HverifiedReturn.
  subst verifiedReturn.
  rewrite HactualLiteral in HverifiedLiteral.
  inversion HverifiedLiteral.
  contradiction.
Qed.

Theorem invented_definition_on_variable_return_is_rejected :
  forall source target expectedValue value literal,
    projectionReturn source = ExpectedReturnValue expectedValue ->
    targetScalarLiteralAt target value = Some literal ->
    projectionNamedLiteralAt source value <> Some literal ->
    ~ SurfaceSystemsProjectionSuccess source target.
Proof.
  intros source target expectedValue value literal Hreturn Hdefinition
    Hinvented Hverified.
  apply Hinvented.
  exact
    (verified_variable_return_has_no_invented_scalar_definition
      source target expectedValue value literal
      Hverified Hreturn Hdefinition).
Qed.
