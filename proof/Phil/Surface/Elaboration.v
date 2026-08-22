From Stdlib Require Import Lists.List Bool.Bool.
Import ListNotations.

(*
  Proof-oriented model of Phil.Surface.Elaborate.

  The surface parser/Megaparsec implementation is deliberately outside this
  proof: parsed surface nodes and source spans are inputs.  The authority-bearing
  claim here is narrower and more useful: once given a surface fragment, the
  elaborator either maps supported syntax to the designated Core structure or
  rejects when proof-relevant information would have to be guessed.

  Two already-checked Core services are represented as explicit function
  arguments rather than axioms:

  - proposition canonicalization;
  - expected-Nat elaboration for dependent indices.

  In the Haskell implementation those are supplied by Phil.Core.Focusing.  The
  corresponding authority boundary is discharged separately by PHIL-FOCUS-*.
  Keeping that dependency explicit also prevents accidental theorem coupling
  through a shared proof namespace.
*)

(* -------------------------------------------------------------------------- *)
(* Surface refinement expressions -> Core refinement terms.                    *)
(* -------------------------------------------------------------------------- *)

Inductive ProjectionSort : Type :=
| ProjectionNat : ProjectionSort
| ProjectionUInt : nat -> ProjectionSort
| ProjectionBool : ProjectionSort
| ProjectionOther : nat -> ProjectionSort.

Inductive BinaryOperator : Type :=
| SurfaceAdd : BinaryOperator
| SurfaceSubtract : BinaryOperator
| SurfaceMultiply : BinaryOperator.

Inductive CallKind : Type :=
| LenCall : CallKind
| ToNatCall : CallKind
| OtherCall : nat -> CallKind.

Inductive SurfaceExpression : Type :=
| SurfaceVariable : nat -> SurfaceExpression
| SurfaceInteger : nat -> SurfaceExpression
| SurfaceBoolean : bool -> SurfaceExpression
| SurfaceUnit : SurfaceExpression
| SurfaceField : SurfaceExpression -> nat -> SurfaceExpression
| SurfaceCall : CallKind -> SurfaceExpression -> SurfaceExpression
| SurfaceBinary : BinaryOperator -> SurfaceExpression -> SurfaceExpression -> SurfaceExpression
| SurfaceTuple : nat -> SurfaceExpression
| SurfaceUnsupported : nat -> SurfaceExpression.

Inductive CoreTerm : Type :=
| CoreVar : nat -> CoreTerm
| CoreNat : nat -> CoreTerm
| CoreBool : bool -> CoreTerm
| CoreField : CoreTerm -> nat -> ProjectionSort -> CoreTerm
| CoreLen : CoreTerm -> CoreTerm
| CoreToNat : CoreTerm -> CoreTerm
| CoreAdd : CoreTerm -> CoreTerm -> CoreTerm
| CoreSub : CoreTerm -> CoreTerm -> CoreTerm
| CoreScale : nat -> CoreTerm -> CoreTerm.

Fixpoint projectionPath (expression : SurfaceExpression) : option (list nat) :=
  match expression with
  | SurfaceVariable name => Some [name]
  | SurfaceField base field =>
      match projectionPath base with
      | Some path => Some (path ++ [field])
      | None => None
      end
  | _ => None
  end.

Definition ProjectionEnvironment := list nat -> option ProjectionSort.

Definition integerLiteral (expression : SurfaceExpression) : option nat :=
  match expression with
  | SurfaceInteger value => Some value
  | _ => None
  end.

Fixpoint elaborateRefTerm
  (projections : ProjectionEnvironment)
  (expression : SurfaceExpression) : option CoreTerm :=
  match expression with
  | SurfaceVariable name => Some (CoreVar name)
  | SurfaceInteger literal => Some (CoreNat literal)
  | SurfaceBoolean value => Some (CoreBool value)
  | SurfaceUnit => None
  | SurfaceField base field =>
      match elaborateRefTerm projections base, projectionPath base with
      | Some baseTerm, Some basePath =>
          match projections (basePath ++ [field]) with
          | Some resultSort => Some (CoreField baseTerm field resultSort)
          | None => None
          end
      | _, _ => None
      end
  | SurfaceCall LenCall value =>
      match elaborateRefTerm projections value with
      | Some value' => Some (CoreLen value')
      | None => None
      end
  | SurfaceCall ToNatCall value =>
      match elaborateRefTerm projections value with
      | Some value' => Some (CoreToNat value')
      | None => None
      end
  | SurfaceCall (OtherCall _) _ => None
  | SurfaceBinary SurfaceAdd lhs rhs =>
      match elaborateRefTerm projections lhs,
            elaborateRefTerm projections rhs with
      | Some lhs', Some rhs' => Some (CoreAdd lhs' rhs')
      | _, _ => None
      end
  | SurfaceBinary SurfaceSubtract lhs rhs =>
      match elaborateRefTerm projections lhs,
            elaborateRefTerm projections rhs with
      | Some lhs', Some rhs' => Some (CoreSub lhs' rhs')
      | _, _ => None
      end
  | SurfaceBinary SurfaceMultiply lhs rhs =>
      match integerLiteral lhs, integerLiteral rhs with
      | Some coefficient, _ =>
          match elaborateRefTerm projections rhs with
          | Some rhs' => Some (CoreScale coefficient rhs')
          | None => None
          end
      | None, Some coefficient =>
          match elaborateRefTerm projections lhs with
          | Some lhs' => Some (CoreScale coefficient lhs')
          | None => None
          end
      | None, None => None
      end
  | SurfaceTuple _ => None
  | SurfaceUnsupported _ => None
  end.

(* PHIL-SURFACE-ELAB-001: direct supported constructors are not reinterpreted. *)
Theorem variable_elaborates_exactly :
  forall projections name,
    elaborateRefTerm projections (SurfaceVariable name) = Some (CoreVar name).
Proof. reflexivity. Qed.

Theorem boolean_elaborates_exactly :
  forall projections value,
    elaborateRefTerm projections (SurfaceBoolean value) = Some (CoreBool value).
Proof. reflexivity. Qed.

Theorem addition_elaborates_exactly :
  forall projections lhs rhs lhs' rhs',
    elaborateRefTerm projections lhs = Some lhs' ->
    elaborateRefTerm projections rhs = Some rhs' ->
    elaborateRefTerm projections (SurfaceBinary SurfaceAdd lhs rhs) =
      Some (CoreAdd lhs' rhs').
Proof.
  intros projections lhs rhs lhs' rhs' Hlhs Hrhs.
  simpl. rewrite Hlhs, Hrhs. reflexivity.
Qed.

Theorem field_elaboration_uses_exact_declared_projection_sort :
  forall projections base field base' basePath resultSort,
    elaborateRefTerm projections base = Some base' ->
    projectionPath base = Some basePath ->
    projections (basePath ++ [field]) = Some resultSort ->
    elaborateRefTerm projections (SurfaceField base field) =
      Some (CoreField base' field resultSort).
Proof.
  intros projections base field base' basePath resultSort Hbase Hpath Hsort.
  simpl. rewrite Hbase, Hpath, Hsort. reflexivity.
Qed.

Theorem literal_left_multiplication_is_exact_scale :
  forall projections coefficient rhs rhs',
    elaborateRefTerm projections rhs = Some rhs' ->
    elaborateRefTerm projections
      (SurfaceBinary SurfaceMultiply (SurfaceInteger coefficient) rhs) =
      Some (CoreScale coefficient rhs').
Proof.
  intros projections coefficient rhs rhs' Hrhs.
  simpl. rewrite Hrhs. reflexivity.
Qed.

(* PHIL-SURFACE-FAIL-001: no projection sort means no guessed Core field sort. *)
Theorem unknown_projection_sort_rejects :
  forall projections base field base' basePath,
    elaborateRefTerm projections base = Some base' ->
    projectionPath base = Some basePath ->
    projections (basePath ++ [field]) = None ->
    elaborateRefTerm projections (SurfaceField base field) = None.
Proof.
  intros projections base field base' basePath Hbase Hpath Hmissing.
  simpl. rewrite Hbase, Hpath, Hmissing. reflexivity.
Qed.

(* PHIL-SURFACE-FAIL-001: Phase 0 multiplication cannot invent bilinear meaning. *)
Theorem symbolic_multiplication_rejects :
  forall projections lhs rhs,
    integerLiteral lhs = None ->
    integerLiteral rhs = None ->
    elaborateRefTerm projections (SurfaceBinary SurfaceMultiply lhs rhs) = None.
Proof.
  intros projections lhs rhs Hlhs Hrhs.
  simpl. rewrite Hlhs, Hrhs. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Surface propositions delegate canonicalization exactly once.                *)
(* -------------------------------------------------------------------------- *)

Inductive SurfaceProposition : Type :=
| SurfaceTruth : SurfaceProposition
| SurfaceFalsehood : SurfaceProposition
| SurfaceEqual : SurfaceExpression -> SurfaceExpression -> SurfaceProposition
| SurfaceNotEqual : SurfaceExpression -> SurfaceExpression -> SurfaceProposition
| SurfaceLessThan : SurfaceExpression -> SurfaceExpression -> SurfaceProposition
| SurfaceLessEqual : SurfaceExpression -> SurfaceExpression -> SurfaceProposition
| SurfaceGreaterThan : SurfaceExpression -> SurfaceExpression -> SurfaceProposition
| SurfaceGreaterEqual : SurfaceExpression -> SurfaceExpression -> SurfaceProposition
| SurfaceMember : SurfaceExpression -> SurfaceExpression -> SurfaceProposition
| SurfaceDisjoint : SurfaceExpression -> SurfaceExpression -> SurfaceProposition
| SurfaceAtom : nat -> list SurfaceExpression -> SurfaceProposition
| SurfaceConjunction : SurfaceProposition -> SurfaceProposition -> SurfaceProposition
| SurfaceDisjunction : SurfaceProposition -> SurfaceProposition -> SurfaceProposition
| SurfaceNegation : SurfaceProposition -> SurfaceProposition.

Inductive CoreProposition : Type :=
| CoreTruth : CoreProposition
| CoreFalsehood : CoreProposition
| CoreEqual : CoreTerm -> CoreTerm -> CoreProposition
| CoreNotEqual : CoreTerm -> CoreTerm -> CoreProposition
| CoreLessThan : CoreTerm -> CoreTerm -> CoreProposition
| CoreLessEqual : CoreTerm -> CoreTerm -> CoreProposition
| CoreMember : CoreTerm -> CoreTerm -> CoreProposition
| CoreDisjoint : CoreTerm -> CoreTerm -> CoreProposition
| CoreAtom : nat -> list CoreTerm -> CoreProposition
| CoreConjunction : CoreProposition -> CoreProposition -> CoreProposition
| CoreDisjunction : CoreProposition -> CoreProposition -> CoreProposition
| CoreNegation : CoreProposition -> CoreProposition.

Fixpoint elaborateTermList
  (projections : ProjectionEnvironment)
  (expressions : list SurfaceExpression) : option (list CoreTerm) :=
  match expressions with
  | [] => Some []
  | expression :: rest =>
      match elaborateRefTerm projections expression,
            elaborateTermList projections rest with
      | Some expression', Some rest' => Some (expression' :: rest')
      | _, _ => None
      end
  end.

Fixpoint rawElaborateProposition
  (projections : ProjectionEnvironment)
  (proposition : SurfaceProposition) : option CoreProposition :=
  match proposition with
  | SurfaceTruth => Some CoreTruth
  | SurfaceFalsehood => Some CoreFalsehood
  | SurfaceEqual lhs rhs =>
      match elaborateRefTerm projections lhs, elaborateRefTerm projections rhs with
      | Some lhs', Some rhs' => Some (CoreEqual lhs' rhs')
      | _, _ => None
      end
  | SurfaceNotEqual lhs rhs =>
      match elaborateRefTerm projections lhs, elaborateRefTerm projections rhs with
      | Some lhs', Some rhs' => Some (CoreNotEqual lhs' rhs')
      | _, _ => None
      end
  | SurfaceLessThan lhs rhs =>
      match elaborateRefTerm projections lhs, elaborateRefTerm projections rhs with
      | Some lhs', Some rhs' => Some (CoreLessThan lhs' rhs')
      | _, _ => None
      end
  | SurfaceLessEqual lhs rhs =>
      match elaborateRefTerm projections lhs, elaborateRefTerm projections rhs with
      | Some lhs', Some rhs' => Some (CoreLessEqual lhs' rhs')
      | _, _ => None
      end
  | SurfaceGreaterThan lhs rhs =>
      match elaborateRefTerm projections lhs, elaborateRefTerm projections rhs with
      | Some lhs', Some rhs' => Some (CoreLessThan rhs' lhs')
      | _, _ => None
      end
  | SurfaceGreaterEqual lhs rhs =>
      match elaborateRefTerm projections lhs, elaborateRefTerm projections rhs with
      | Some lhs', Some rhs' => Some (CoreLessEqual rhs' lhs')
      | _, _ => None
      end
  | SurfaceMember value collection =>
      match elaborateRefTerm projections value,
            elaborateRefTerm projections collection with
      | Some value', Some collection' => Some (CoreMember value' collection')
      | _, _ => None
      end
  | SurfaceDisjoint lhs rhs =>
      match elaborateRefTerm projections lhs, elaborateRefTerm projections rhs with
      | Some lhs', Some rhs' => Some (CoreDisjoint lhs' rhs')
      | _, _ => None
      end
  | SurfaceAtom claim arguments =>
      match elaborateTermList projections arguments with
      | Some arguments' => Some (CoreAtom claim arguments')
      | None => None
      end
  | SurfaceConjunction lhs rhs =>
      match rawElaborateProposition projections lhs,
            rawElaborateProposition projections rhs with
      | Some lhs', Some rhs' => Some (CoreConjunction lhs' rhs')
      | _, _ => None
      end
  | SurfaceDisjunction lhs rhs =>
      match rawElaborateProposition projections lhs,
            rawElaborateProposition projections rhs with
      | Some lhs', Some rhs' => Some (CoreDisjunction lhs' rhs')
      | _, _ => None
      end
  | SurfaceNegation inner =>
      match rawElaborateProposition projections inner with
      | Some inner' => Some (CoreNegation inner')
      | None => None
      end
  end.

Definition PropositionCanonicalizer := CoreProposition -> CoreProposition.

Definition elaborateProposition
  (canonicalize : PropositionCanonicalizer)
  (projections : ProjectionEnvironment)
  (proposition : SurfaceProposition) : option CoreProposition :=
  match rawElaborateProposition projections proposition with
  | Some raw => Some (canonicalize raw)
  | None => None
  end.

(* PHIL-SURFACE-ELAB-001: the surface layer does not substitute for focusing. *)
Theorem proposition_elaboration_delegates_exact_canonicalization :
  forall canonicalize projections proposition raw,
    rawElaborateProposition projections proposition = Some raw ->
    elaborateProposition canonicalize projections proposition =
      Some (canonicalize raw).
Proof.
  intros canonicalize projections proposition raw Hraw.
  unfold elaborateProposition. rewrite Hraw. reflexivity.
Qed.

Theorem greater_than_has_designated_core_orientation :
  forall projections lhs rhs lhs' rhs',
    elaborateRefTerm projections lhs = Some lhs' ->
    elaborateRefTerm projections rhs = Some rhs' ->
    rawElaborateProposition projections (SurfaceGreaterThan lhs rhs) =
      Some (CoreLessThan rhs' lhs').
Proof.
  intros projections lhs rhs lhs' rhs' Hlhs Hrhs.
  simpl. rewrite Hlhs, Hrhs. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Surface types and values.                                                   *)
(* -------------------------------------------------------------------------- *)

Inductive IdentityExpression : Type :=
| IdentityName : nat -> IdentityExpression
| IdentityNonName : nat -> IdentityExpression.

Inductive OpaqueArgumentKey : Type :=
| OpaqueNameKey : nat -> OpaqueArgumentKey
| OpaqueIntegerKey : nat -> OpaqueArgumentKey
| OpaqueBoolKey : bool -> OpaqueArgumentKey
| OpaqueUnitKey : OpaqueArgumentKey
| OpaqueStructuredKey : nat -> OpaqueArgumentKey.

Inductive SurfaceOpaqueArgument : Type :=
| SupportedOpaqueArgument : OpaqueArgumentKey -> SurfaceOpaqueArgument
| UnsupportedOpaqueArgument : nat -> SurfaceOpaqueArgument.

Fixpoint renderOpaqueArguments
  (arguments : list SurfaceOpaqueArgument) : option (list OpaqueArgumentKey) :=
  match arguments with
  | [] => Some []
  | SupportedOpaqueArgument key :: rest =>
      match renderOpaqueArguments rest with
      | Some rest' => Some (key :: rest')
      | None => None
      end
  | UnsupportedOpaqueArgument _ :: _ => None
  end.

Inductive ContainsUnsupportedOpaque : list SurfaceOpaqueArgument -> Prop :=
| UnsupportedOpaque_here :
    forall code rest,
      ContainsUnsupportedOpaque (UnsupportedOpaqueArgument code :: rest)
| UnsupportedOpaque_later :
    forall key rest,
      ContainsUnsupportedOpaque rest ->
      ContainsUnsupportedOpaque (SupportedOpaqueArgument key :: rest).

Inductive SurfaceType : Type :=
| SurfaceUnitType : SurfaceType
| SurfaceBoolType : SurfaceType
| SurfaceUIntType : nat -> SurfaceType
| SurfaceBytesType : SurfaceExpression -> SurfaceType
| SurfaceFrameType : nat -> SurfaceType
| SurfaceProofType : SurfaceProposition -> SurfaceType
| SurfaceValidatedType : nat -> IdentityExpression -> IdentityExpression -> SurfaceType
| SurfaceNamedType : nat -> list SurfaceOpaqueArgument -> SurfaceType.

Inductive CoreType : Type :=
| CoreUnitType : CoreType
| CoreBoolType : CoreType
| CoreUIntType : nat -> CoreType
| CoreBytesType : CoreTerm -> CoreType
| CoreFrameType : nat -> CoreType
| CoreProofType : CoreProposition -> CoreType
| CoreValidatedType : nat -> nat -> nat -> CoreType
| CoreOpaqueType : nat -> list OpaqueArgumentKey -> CoreType
| CoreRefinedType : nat -> CoreType -> CoreType.

Definition NatIndexElaborator := CoreTerm -> option CoreTerm.

Definition identityName (identity : IdentityExpression) : option nat :=
  match identity with
  | IdentityName name => Some name
  | IdentityNonName _ => None
  end.

Definition elaborateType
  (canonicalize : PropositionCanonicalizer)
  (natIndex : NatIndexElaborator)
  (projections : ProjectionEnvironment)
  (surfaceType : SurfaceType) : option CoreType :=
  match surfaceType with
  | SurfaceUnitType => Some CoreUnitType
  | SurfaceBoolType => Some CoreBoolType
  | SurfaceUIntType width => Some (CoreUIntType width)
  | SurfaceBytesType index =>
      match elaborateRefTerm projections index with
      | Some rawIndex =>
          match natIndex rawIndex with
          | Some index' => Some (CoreBytesType index')
          | None => None
          end
      | None => None
      end
  | SurfaceFrameType grammar => Some (CoreFrameType grammar)
  | SurfaceProofType proposition =>
      match elaborateProposition canonicalize projections proposition with
      | Some proposition' => Some (CoreProofType proposition')
      | None => None
      end
  | SurfaceValidatedType claim context subject =>
      match identityName context, identityName subject with
      | Some contextName, Some subjectName =>
          Some (CoreValidatedType claim contextName subjectName)
      | _, _ => None
      end
  | SurfaceNamedType name arguments =>
      match renderOpaqueArguments arguments with
      | Some rendered => Some (CoreOpaqueType name rendered)
      | None => None
      end
  end.

(* PHIL-SURFACE-ELAB-001: dependent indices use exactly the supplied focusing boundary. *)
Theorem bytes_type_delegates_exact_nat_index_elaboration :
  forall canonicalize natIndex projections index rawIndex index',
    elaborateRefTerm projections index = Some rawIndex ->
    natIndex rawIndex = Some index' ->
    elaborateType canonicalize natIndex projections (SurfaceBytesType index) =
      Some (CoreBytesType index').
Proof.
  intros canonicalize natIndex projections index rawIndex index' Hraw Hnat.
  simpl. rewrite Hraw, Hnat. reflexivity.
Qed.

Theorem proof_type_uses_exact_canonical_proposition :
  forall canonicalize natIndex projections proposition proposition',
    elaborateProposition canonicalize projections proposition = Some proposition' ->
    elaborateType canonicalize natIndex projections (SurfaceProofType proposition) =
      Some (CoreProofType proposition').
Proof.
  intros canonicalize natIndex projections proposition proposition' Hprop.
  simpl. rewrite Hprop. reflexivity.
Qed.

Theorem validated_type_preserves_exact_identities :
  forall canonicalize natIndex projections claim context subject,
    elaborateType canonicalize natIndex projections
      (SurfaceValidatedType claim (IdentityName context) (IdentityName subject)) =
      Some (CoreValidatedType claim context subject).
Proof. reflexivity. Qed.

(* PHIL-SURFACE-FAIL-001: validation provenance identities are never synthesized. *)
Theorem non_name_validation_context_rejects :
  forall canonicalize natIndex projections claim code subject,
    elaborateType canonicalize natIndex projections
      (SurfaceValidatedType claim (IdentityNonName code) subject) = None.
Proof.
  intros canonicalize natIndex projections claim code subject.
  destruct subject; reflexivity.
Qed.

Theorem non_name_validation_subject_rejects :
  forall canonicalize natIndex projections claim context code,
    elaborateType canonicalize natIndex projections
      (SurfaceValidatedType claim context (IdentityNonName code)) = None.
Proof.
  intros canonicalize natIndex projections claim context code.
  destruct context; reflexivity.
Qed.

Lemma unsupported_opaque_argument_prevents_rendering :
  forall arguments,
    ContainsUnsupportedOpaque arguments ->
    renderOpaqueArguments arguments = None.
Proof.
  intros arguments Hunsupported.
  induction Hunsupported.
  - reflexivity.
  - simpl. rewrite IHHunsupported. reflexivity.
Qed.

(* PHIL-SURFACE-FAIL-001: unsupported opaque index syntax cannot collapse into a guessed identity. *)
Theorem unsupported_opaque_type_argument_rejects :
  forall canonicalize natIndex projections name arguments,
    ContainsUnsupportedOpaque arguments ->
    elaborateType canonicalize natIndex projections (SurfaceNamedType name arguments) = None.
Proof.
  intros canonicalize natIndex projections name arguments Hunsupported.
  simpl.
  rewrite (unsupported_opaque_argument_prevents_rendering arguments Hunsupported).
  reflexivity.
Qed.

Inductive SurfaceValue : Type :=
| SurfaceValueVariable : nat -> SurfaceValue
| SurfaceValueBoolean : bool -> SurfaceValue
| SurfaceValueUnit : SurfaceValue
| SurfaceValueInteger : nat -> SurfaceValue
| SurfaceValueUnsupported : nat -> SurfaceValue.

Inductive CoreValue : Type :=
| CoreValueVariable : nat -> CoreValue
| CoreValueBoolean : bool -> CoreValue
| CoreValueUnit : CoreValue
| CoreValueUInt : nat -> nat -> CoreValue.

Fixpoint expectedUIntWidthType (expected : CoreType) : option nat :=
  match expected with
  | CoreUIntType width => Some width
  | CoreRefinedType _ base => expectedUIntWidthType base
  | _ => None
  end.

Definition expectedUIntWidth (expected : option CoreType) : option nat :=
  match expected with
  | Some expectedType => expectedUIntWidthType expectedType
  | None => None
  end.

Definition elaborateValue
  (expected : option CoreType)
  (value : SurfaceValue) : option CoreValue :=
  match value with
  | SurfaceValueVariable name => Some (CoreValueVariable name)
  | SurfaceValueBoolean boolean => Some (CoreValueBoolean boolean)
  | SurfaceValueUnit => Some CoreValueUnit
  | SurfaceValueInteger literal =>
      match expectedUIntWidth expected with
      | Some width => Some (CoreValueUInt width literal)
      | None => None
      end
  | SurfaceValueUnsupported _ => None
  end.

Theorem expected_uint_literal_elaborates_exact_width :
  forall width literal,
    elaborateValue (Some (CoreUIntType width)) (SurfaceValueInteger literal) =
      Some (CoreValueUInt width literal).
Proof. reflexivity. Qed.

Theorem refined_expected_uint_literal_preserves_base_width :
  forall tag width literal,
    elaborateValue (Some (CoreRefinedType tag (CoreUIntType width)))
      (SurfaceValueInteger literal) =
      Some (CoreValueUInt width literal).
Proof. reflexivity. Qed.

(* PHIL-SURFACE-FAIL-001: an untyped integer never causes a width guess. *)
Theorem ambiguous_integer_literal_rejects :
  forall literal,
    elaborateValue None (SurfaceValueInteger literal) = None.
Proof. reflexivity. Qed.
