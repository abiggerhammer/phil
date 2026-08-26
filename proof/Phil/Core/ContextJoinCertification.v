From Stdlib Require Import Lists.List.
Import ListNotations.

From Phil.Core Require Import Context ContextJoin.

(*
  PHIL-CTX-JOIN-001 certification wrapper.

  The semantic model itself landed with the Phase 1 control-state projection.
  This file introduces no second join semantics: each certified theorem below
  is discharged directly by the corresponding theorem in ContextJoin.v.
*)

Theorem certified_context_join_inputs_have_no_loans :
  forall contexts joined,
    ContextJoinSuccess contexts joined ->
    Forall NoLoans contexts.
Proof.
  exact context_join_inputs_have_no_loans.
Qed.

Theorem certified_context_join_output_has_no_loans :
  forall contexts joined,
    ContextJoinSuccess contexts joined ->
    NoLoans joined.
Proof.
  exact context_join_output_has_no_loans.
Qed.

Theorem certified_context_join_unrestricted_converges :
  forall contexts joined context,
    ContextJoinSuccess contexts joined ->
    In context contexts ->
    SameBindingMap
      (unrestrictedBindings joined)
      (unrestrictedBindings context).
Proof.
  exact context_join_unrestricted_converges.
Qed.

Theorem certified_context_join_linear_converges :
  forall contexts joined context,
    ContextJoinSuccess contexts joined ->
    In context contexts ->
    SameBindingMap
      (linearBindings joined)
      (linearBindings context).
Proof.
  exact context_join_linear_converges.
Qed.

Theorem certified_context_join_affine_some_exact :
  forall first rest joined name ty,
    ContextJoinSuccess (first :: rest) joined ->
    (affineBindings joined name = Some ty <->
      affineBindings first name = Some ty /\
      Forall (fun context => affineBindings context name = Some ty) rest).
Proof.
  exact context_join_affine_some_exact.
Qed.

Theorem certified_context_join_affine_retained_is_common :
  forall first rest joined name ty context,
    ContextJoinSuccess (first :: rest) joined ->
    affineBindings joined name = Some ty ->
    In context (first :: rest) ->
    affineBindings context name = Some ty.
Proof.
  exact context_join_affine_retained_is_common.
Qed.
