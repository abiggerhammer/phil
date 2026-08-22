From Stdlib Require Import Arith.PeanoNat.

From Phil.Core Require Import Scalar.
From Phil.Systems Require Import Scalar.

(*
  PHIL-LLVM-SCALAR-001 — scalar specialization of the ordinary-projection
  boundary in Phil.LLVM.Verify.

  The Haskell lowerer carries Systems ValueId text directly into LLVM SSA names,
  carries ScalarLiteral unchanged into LLVMScalarLiteral, and derives
  LLVMReturnScalar from the exact TypedScalar role of the returned Systems
  value.  The ordinary-projection verifier compares those operations and
  terminators structurally.

  This normalized model uses the same opaque nat identifier for the Systems
  value and LLVM SSA name.  That shared identifier models the exact
  `unValueId` carry-through; concrete Text rendering/escaping, LLVM syntax,
  Haskell lowerer correspondence, and LLVM integer semantics remain explicit
  implementation/external-tool boundaries.
*)

Record LLVMScalarProjectionModel : Type := mkLLVMScalarProjectionModel {
  llvmScalarSource : SystemsScalarModel;
  llvmTargetLiteralAt : ValueId -> option ScalarLiteral;
  llvmTargetReturnValue : ReturnSiteId -> option ValueId;
  llvmTargetReturnType : ReturnSiteId -> option ScalarType
}.

Definition sourceReturnType
  (source : SystemsScalarModel)
  (site : ReturnSiteId) : option ScalarType :=
  match systemsReturnValue source site with
  | None => None
  | Some value => systemsValueType source value
  end.

Definition LLVMScalarPreservationSuccess
  (model : LLVMScalarProjectionModel) : Prop :=
  SystemsScalarVerificationSuccess (llvmScalarSource model) /\
  (forall value,
    llvmTargetLiteralAt model value =
      systemsLiteralAt (llvmScalarSource model) value) /\
  (forall site,
    llvmTargetReturnValue model site =
      systemsReturnValue (llvmScalarSource model) site) /\
  (forall site,
    llvmTargetReturnType model site =
      sourceReturnType (llvmScalarSource model) site).

Theorem verified_llvm_scalar_source_is_systems_verified :
  forall model,
    LLVMScalarPreservationSuccess model ->
    SystemsScalarVerificationSuccess (llvmScalarSource model).
Proof.
  intros model Hverified.
  destruct Hverified as [Hsystems _].
  exact Hsystems.
Qed.

Theorem verified_llvm_scalar_literal_preserves_name_type_and_value :
  forall model value literal,
    LLVMScalarPreservationSuccess model ->
    systemsLiteralAt (llvmScalarSource model) value = Some literal ->
    llvmTargetLiteralAt model value = Some literal.
Proof.
  intros model value literal Hverified Hsource.
  destruct Hverified as [_ [Hliterals _]].
  rewrite Hliterals.
  exact Hsource.
Qed.

Theorem verified_llvm_uint_preserves_exact_width_and_value :
  forall model value width number,
    LLVMScalarPreservationSuccess model ->
    systemsLiteralAt (llvmScalarSource model) value =
      Some (ScalarUIntLiteral width number) ->
    llvmTargetLiteralAt model value =
      Some (ScalarUIntLiteral width number).
Proof.
  intros model value width number Hverified Hsource.
  eapply verified_llvm_scalar_literal_preserves_name_type_and_value; eauto.
Qed.

Theorem verified_llvm_uint_remains_in_range :
  forall model value width number,
    LLVMScalarPreservationSuccess model ->
    systemsLiteralAt (llvmScalarSource model) value =
      Some (ScalarUIntLiteral width number) ->
    number < Nat.pow 2 width.
Proof.
  intros model value width number Hverified Hsource.
  pose proof
    (verified_llvm_scalar_source_is_systems_verified model Hverified)
    as Hsystems.
  pose proof
    (verified_systems_literal_is_valid_and_exactly_typed
      (llvmScalarSource model)
      value
      (ScalarUIntLiteral width number)
      Hsystems
      Hsource) as Hliteral.
  destruct Hliteral as [Hvalid _].
  eapply valid_uint_is_below_modulus.
  exact Hvalid.
Qed.

Theorem verified_llvm_scalar_return_preserves_identity_and_type :
  forall model site value scalarType,
    LLVMScalarPreservationSuccess model ->
    systemsReturnValue (llvmScalarSource model) site = Some value ->
    systemsValueType (llvmScalarSource model) value = Some scalarType ->
    llvmTargetReturnValue model site = Some value /\
    llvmTargetReturnType model site = Some scalarType.
Proof.
  intros model site value scalarType Hverified Hreturn Htype.
  destruct Hverified as [_ [_ [HreturnValue HreturnType]]].
  split.
  - rewrite HreturnValue. exact Hreturn.
  - rewrite HreturnType.
    unfold sourceReturnType.
    rewrite Hreturn.
    exact Htype.
Qed.

Theorem moved_scalar_ssa_name_is_rejected :
  forall model value literal,
    systemsLiteralAt (llvmScalarSource model) value = Some literal ->
    llvmTargetLiteralAt model value = None ->
    ~ LLVMScalarPreservationSuccess model.
Proof.
  intros model value literal Hsource Hmissing Hverified.
  pose proof
    (verified_llvm_scalar_literal_preserves_name_type_and_value
      model value literal Hverified Hsource) as Htarget.
  rewrite Hmissing in Htarget.
  discriminate.
Qed.

Theorem scalar_width_drift_is_rejected :
  forall model value sourceWidth targetWidth number,
    systemsLiteralAt (llvmScalarSource model) value =
      Some (ScalarUIntLiteral sourceWidth number) ->
    llvmTargetLiteralAt model value =
      Some (ScalarUIntLiteral targetWidth number) ->
    sourceWidth <> targetWidth ->
    ~ LLVMScalarPreservationSuccess model.
Proof.
  intros model value sourceWidth targetWidth number
    Hsource Htarget Hwidth Hverified.
  pose proof
    (verified_llvm_uint_preserves_exact_width_and_value
      model value sourceWidth number Hverified Hsource) as Hexact.
  rewrite Htarget in Hexact.
  inversion Hexact; subst.
  apply Hwidth.
  reflexivity.
Qed.

Theorem scalar_value_drift_is_rejected :
  forall model value width sourceValue targetValue,
    systemsLiteralAt (llvmScalarSource model) value =
      Some (ScalarUIntLiteral width sourceValue) ->
    llvmTargetLiteralAt model value =
      Some (ScalarUIntLiteral width targetValue) ->
    sourceValue <> targetValue ->
    ~ LLVMScalarPreservationSuccess model.
Proof.
  intros model value width sourceValue targetValue
    Hsource Htarget Hvalue Hverified.
  pose proof
    (verified_llvm_uint_preserves_exact_width_and_value
      model value width sourceValue Hverified Hsource) as Hexact.
  rewrite Htarget in Hexact.
  inversion Hexact; subst.
  apply Hvalue.
  reflexivity.
Qed.

Theorem scalar_return_identity_drift_is_rejected :
  forall model site sourceValue targetValue scalarType,
    systemsReturnValue (llvmScalarSource model) site = Some sourceValue ->
    systemsValueType (llvmScalarSource model) sourceValue = Some scalarType ->
    llvmTargetReturnValue model site = Some targetValue ->
    sourceValue <> targetValue ->
    ~ LLVMScalarPreservationSuccess model.
Proof.
  intros model site sourceValue targetValue scalarType
    HsourceReturn HsourceType HtargetReturn Hmismatch Hverified.
  pose proof
    (verified_llvm_scalar_return_preserves_identity_and_type
      model site sourceValue scalarType Hverified HsourceReturn HsourceType)
    as Hexact.
  destruct Hexact as [Hidentity _].
  rewrite HtargetReturn in Hidentity.
  inversion Hidentity; subst.
  apply Hmismatch.
  reflexivity.
Qed.

Theorem scalar_return_type_drift_is_rejected :
  forall model site value sourceType targetType,
    systemsReturnValue (llvmScalarSource model) site = Some value ->
    systemsValueType (llvmScalarSource model) value = Some sourceType ->
    llvmTargetReturnType model site = Some targetType ->
    sourceType <> targetType ->
    ~ LLVMScalarPreservationSuccess model.
Proof.
  intros model site value sourceType targetType
    HsourceReturn HsourceType HtargetType Hmismatch Hverified.
  pose proof
    (verified_llvm_scalar_return_preserves_identity_and_type
      model site value sourceType Hverified HsourceReturn HsourceType)
    as Hexact.
  destruct Hexact as [_ Htype].
  rewrite HtargetType in Htype.
  inversion Htype; subst.
  apply Hmismatch.
  reflexivity.
Qed.
