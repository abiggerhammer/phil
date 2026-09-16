From Phil.Core Require Import Syntax Context.

(*
  PHIL-RES-BIND-MODE-001 — checked type/mode authority for ordinary owning
  bindings.

  The implementation may carry a type and a structural mode separately, but
  neither is authoritative on its own.  A successful ordinary binding must
  agree exactly with the already-checked type/mode contract, after which the
  existing Context insertion theorem owns exact zone placement.

  This proof does not derive a mode from an arbitrary type.  That relation is
  established by the competent type/resource checker that produces the
  CheckedTypeMode contract.  Nor does it change duplicate-binding behavior in
  Context.insertBinding.
*)

Inductive BindingOrigin : Type :=
| TermParameterBinding
| LetBinding
| OwningPatternBinding
| EntryValueBinding
| SuccessorBinding.

Record CheckedTypeMode : Type := mkCheckedTypeMode {
  checkedBindingType : Ty;
  checkedBindingMode : Mode
}.

Definition ExactBindingZone
  (mode : Mode) (name : Name) (ty : Ty) (context : ResourceContext) : Prop :=
  match mode with
  | Unrestricted =>
      unrestrictedBindings context name = Some ty /\
      affineBindings context name = None /\
      linearBindings context name = None
  | Affine =>
      unrestrictedBindings context name = None /\
      affineBindings context name = Some ty /\
      linearBindings context name = None
  | Linear =>
      unrestrictedBindings context name = None /\
      affineBindings context name = None /\
      linearBindings context name = Some ty
  end.

Record CertifiedCheckedBindingInsertion
  (origin : BindingOrigin)
  (checked : CheckedTypeMode)
  (suppliedMode : Mode)
  (name : Name)
  (suppliedType : Ty)
  (context next : ResourceContext) : Prop := mkCertifiedCheckedBindingInsertion {
  certified_checked_binding_type_exact :
    suppliedType = checkedBindingType checked;
  certified_checked_binding_mode_exact :
    suppliedMode = checkedBindingMode checked;
  certified_checked_binding_context_inserted :
    insertBinding
      (checkedBindingMode checked)
      name
      suppliedType
      context = Inserted next
}.

Theorem certified_checked_binding_uses_exact_checked_zone :
  forall origin checked suppliedMode name suppliedType context next,
    CertifiedCheckedBindingInsertion
      origin checked suppliedMode name suppliedType context next ->
    ExactBindingZone
      (checkedBindingMode checked)
      name
      (checkedBindingType checked)
      next.
Proof.
  intros origin checked suppliedMode name suppliedType context next Hcert.
  destruct Hcert as [Htype Hmode Hinsert].
  subst suppliedType.
  pose proof
    (insertBinding_success_exact
      (checkedBindingMode checked)
      name
      (checkedBindingType checked)
      context
      next
      Hinsert) as Hcontext.
  destruct Hcontext as [_ [_ [_ [Hzone _]]]].
  exact Hzone.
Qed.

Theorem checked_binding_type_mismatch_cannot_accept :
  forall origin checked suppliedMode name suppliedType context next,
    suppliedType <> checkedBindingType checked ->
    ~ CertifiedCheckedBindingInsertion
        origin checked suppliedMode name suppliedType context next.
Proof.
  intros origin checked suppliedMode name suppliedType context next Hneq Hcert.
  apply Hneq.
  exact (certified_checked_binding_type_exact
    origin checked suppliedMode name suppliedType context next Hcert).
Qed.

Theorem checked_binding_mode_mismatch_cannot_reclassify :
  forall origin checked suppliedMode name suppliedType context next,
    suppliedMode <> checkedBindingMode checked ->
    ~ CertifiedCheckedBindingInsertion
        origin checked suppliedMode name suppliedType context next.
Proof.
  intros origin checked suppliedMode name suppliedType context next Hneq Hcert.
  apply Hneq.
  exact (certified_checked_binding_mode_exact
    origin checked suppliedMode name suppliedType context next Hcert).
Qed.

Theorem checked_binding_origin_does_not_reclassify :
  forall originA originB checked suppliedMode name suppliedType context next,
    CertifiedCheckedBindingInsertion
      originA checked suppliedMode name suppliedType context next <->
    CertifiedCheckedBindingInsertion
      originB checked suppliedMode name suppliedType context next.
Proof.
  intros originA originB checked suppliedMode name suppliedType context next.
  split.
  - intros Hcert.
    destruct Hcert as [Htype Hmode Hinsert].
    constructor; assumption.
  - intros Hcert.
    destruct Hcert as [Htype Hmode Hinsert].
    constructor; assumption.
Qed.
