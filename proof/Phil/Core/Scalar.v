From Stdlib Require Import Arith.PeanoNat Bool.Bool.

(*
  PHIL-CORE-SCALAR-001 — proof-oriented model of Phil.Core.Scalar.

  Scalar literals are self-describing: Bool values carry Bool type and UInt
  values carry their width.  Validity is intrinsic rather than supplied by an
  ambient representation convention.  The Haskell implementation represents
  widths with Int and values with Integer; correspondence from those concrete
  host representations to the naturals used here remains an implementation
  boundary.
*)

Inductive ScalarType : Type :=
| ScalarBoolType
| ScalarUIntType : nat -> ScalarType.

Inductive ScalarLiteral : Type :=
| ScalarBoolLiteral : bool -> ScalarLiteral
| ScalarUIntLiteral : nat -> nat -> ScalarLiteral.

Definition scalarLiteralType (literal : ScalarLiteral) : ScalarType :=
  match literal with
  | ScalarBoolLiteral _ => ScalarBoolType
  | ScalarUIntLiteral width _ => ScalarUIntType width
  end.

Definition ScalarLiteralValid (literal : ScalarLiteral) : Prop :=
  match literal with
  | ScalarBoolLiteral _ => True
  | ScalarUIntLiteral width value =>
      0 < width /\ value < Nat.pow 2 width
  end.

Theorem scalar_literal_has_intrinsic_type :
  forall literal,
    exists scalarType,
      scalarLiteralType literal = scalarType.
Proof.
  intros literal.
  exists (scalarLiteralType literal).
  reflexivity.
Qed.

Theorem scalar_literal_type_is_deterministic :
  forall literal left right,
    scalarLiteralType literal = left ->
    scalarLiteralType literal = right ->
    left = right.
Proof.
  intros literal left right Hleft Hright.
  rewrite <- Hleft.
  exact Hright.
Qed.

Theorem boolean_literals_are_valid :
  forall value,
    ScalarLiteralValid (ScalarBoolLiteral value).
Proof.
  intros value.
  simpl.
  exact I.
Qed.

Theorem valid_uint_has_positive_width :
  forall width value,
    ScalarLiteralValid (ScalarUIntLiteral width value) ->
    0 < width.
Proof.
  intros width value Hvalid.
  simpl in Hvalid.
  destruct Hvalid as [Hwidth _].
  exact Hwidth.
Qed.

Theorem valid_uint_is_below_modulus :
  forall width value,
    ScalarLiteralValid (ScalarUIntLiteral width value) ->
    value < Nat.pow 2 width.
Proof.
  intros width value Hvalid.
  simpl in Hvalid.
  destruct Hvalid as [_ Hrange].
  exact Hrange.
Qed.

Theorem zero_width_uint_is_invalid :
  forall value,
    ~ ScalarLiteralValid (ScalarUIntLiteral 0 value).
Proof.
  intros value Hvalid.
  simpl in Hvalid.
  destruct Hvalid as [Hwidth _].
  exact (Nat.lt_irrefl 0 Hwidth).
Qed.

Theorem uint_at_modulus_is_invalid :
  forall width,
    ~ ScalarLiteralValid
        (ScalarUIntLiteral width (Nat.pow 2 width)).
Proof.
  intros width Hvalid.
  simpl in Hvalid.
  destruct Hvalid as [_ Hrange].
  exact (Nat.lt_irrefl (Nat.pow 2 width) Hrange).
Qed.
