From Stdlib Require Import Strings.String Bool.Bool.

From Phil.Core Require Import Syntax.

(*
  Proof-oriented model of the binding-map fragment of Phil.Core.Context.

  The implementation uses finite maps and a finite set. The proofs here model
  those extensionally as lookup functions. This exposes exactly the observations
  needed for structural ownership proofs without committing the metatheory to a
  particular finite-map representation.
*)

Definition BindingMap := Name -> option Ty.
Definition LoanSet := Name -> bool.

Record ResourceContext : Type := mkResourceContext
  { unrestrictedBindings : BindingMap
  ; affineBindings : BindingMap
  ; linearBindings : BindingMap
  ; sharedLoans : LoanSet
  }.

Inductive CheckError : Type :=
| DuplicateBinding : Name -> CheckError
| OwnerBorrowed : Name -> CheckError
| UnknownLinearBinding : Name -> CheckError.

Definition bindingPresent (name : Name) (bindings : BindingMap) : bool :=
  match bindings name with
  | Some _ => true
  | None => false
  end.

Definition bindingExists (name : Name) (context : ResourceContext) : bool :=
  bindingPresent name (unrestrictedBindings context)
    || bindingPresent name (affineBindings context)
    || bindingPresent name (linearBindings context).

Definition insertBindingMap
  (name : Name) (ty : Ty) (bindings : BindingMap) : BindingMap :=
  fun candidate =>
    if String.eqb candidate name then Some ty else bindings candidate.

Inductive InsertResult : Type :=
| InsertError : CheckError -> InsertResult
| Inserted : ResourceContext -> InsertResult.

Definition insertBinding
  (mode : Mode) (name : Name) (ty : Ty) (context : ResourceContext)
  : InsertResult :=
  if bindingExists name context then
    InsertError (DuplicateBinding name)
  else
    Inserted
      (match mode with
       | Unrestricted =>
           mkResourceContext
             (insertBindingMap name ty (unrestrictedBindings context))
             (affineBindings context)
             (linearBindings context)
             (sharedLoans context)
       | Affine =>
           mkResourceContext
             (unrestrictedBindings context)
             (insertBindingMap name ty (affineBindings context))
             (linearBindings context)
             (sharedLoans context)
       | Linear =>
           mkResourceContext
             (unrestrictedBindings context)
             (affineBindings context)
             (insertBindingMap name ty (linearBindings context))
             (sharedLoans context)
       end).

(*
  PHIL-CTX-BIND-001.

  A successful insertion is globally fresh at the inserted name, installs the
  binding in exactly the selected structural map, preserves all unrelated name
  lookups, and leaves the active-loan set unchanged.
*)
Theorem insertBinding_success_exact :
  forall (mode : Mode) (name : Name) (ty : Ty)
         (context next : ResourceContext),
    insertBinding mode name ty context = Inserted next ->
    unrestrictedBindings context name = None /\
    affineBindings context name = None /\
    linearBindings context name = None /\
    (match mode with
     | Unrestricted =>
         unrestrictedBindings next name = Some ty /\
         affineBindings next name = None /\
         linearBindings next name = None
     | Affine =>
         unrestrictedBindings next name = None /\
         affineBindings next name = Some ty /\
         linearBindings next name = None
     | Linear =>
         unrestrictedBindings next name = None /\
         affineBindings next name = None /\
         linearBindings next name = Some ty
     end) /\
    (forall other : Name,
      String.eqb other name = false ->
      unrestrictedBindings next other = unrestrictedBindings context other /\
      affineBindings next other = affineBindings context other /\
      linearBindings next other = linearBindings context other) /\
    sharedLoans next = sharedLoans context.
Proof.
  intros mode name ty context next Hinsert.
  unfold insertBinding, bindingExists, bindingPresent in Hinsert.
  destruct (unrestrictedBindings context name) as [unrestrictedTy |] eqn:Hunrestricted;
  destruct (affineBindings context name) as [affineTy |] eqn:Haffine;
  destruct (linearBindings context name) as [linearTy |] eqn:Hlinear;
  simpl in Hinsert; try discriminate.
  destruct mode.
  - inversion Hinsert; subst next; clear Hinsert.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [reflexivity |].
    split.
    + simpl.
      split.
      * unfold insertBindingMap. now rewrite String.eqb_refl.
      * split.
        -- exact Haffine.
        -- exact Hlinear.
    + split.
      * intros other Hother.
        simpl.
        split.
        -- unfold insertBindingMap. now rewrite Hother.
        -- split; reflexivity.
      * reflexivity.
  - inversion Hinsert; subst next; clear Hinsert.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [reflexivity |].
    split.
    + simpl.
      split.
      * exact Hunrestricted.
      * split.
        -- unfold insertBindingMap. now rewrite String.eqb_refl.
        -- exact Hlinear.
    + split.
      * intros other Hother.
        simpl.
        split; [reflexivity |].
        split.
        -- unfold insertBindingMap. now rewrite Hother.
        -- reflexivity.
      * reflexivity.
  - inversion Hinsert; subst next; clear Hinsert.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [reflexivity |].
    split.
    + simpl.
      split.
      * exact Hunrestricted.
      * split.
        -- exact Haffine.
        -- unfold insertBindingMap. now rewrite String.eqb_refl.
    + split.
      * intros other Hother.
        simpl.
        split; [reflexivity |].
        split; [reflexivity |].
        unfold insertBindingMap. now rewrite Hother.
      * reflexivity.
Qed.

Corollary insertBinding_success_name_was_fresh :
  forall (mode : Mode) (name : Name) (ty : Ty)
         (context next : ResourceContext),
    insertBinding mode name ty context = Inserted next ->
    unrestrictedBindings context name = None /\
    affineBindings context name = None /\
    linearBindings context name = None.
Proof.
  intros mode name ty context next Hinsert.
  pose proof (insertBinding_success_exact mode name ty context next Hinsert) as H.
  destruct H as [Hunrestricted [Haffine [Hlinear _]]].
  repeat split; assumption.
Qed.

Corollary insertBinding_success_preserves_other_names :
  forall (mode : Mode) (name other : Name) (ty : Ty)
         (context next : ResourceContext),
    insertBinding mode name ty context = Inserted next ->
    String.eqb other name = false ->
    unrestrictedBindings next other = unrestrictedBindings context other /\
    affineBindings next other = affineBindings context other /\
    linearBindings next other = linearBindings context other.
Proof.
  intros mode name other ty context next Hinsert Hother.
  pose proof (insertBinding_success_exact mode name ty context next Hinsert) as H.
  destruct H as [_ [_ [_ [_ [Hpreserved _]]]]].
  apply Hpreserved.
  exact Hother.
Qed.

Inductive ConsumeResult : Type :=
| ConsumeError : CheckError -> ConsumeResult
| Consumed : Ty -> ResourceContext -> ConsumeResult.

Definition deleteBinding (name : Name) (bindings : BindingMap) : BindingMap :=
  fun candidate =>
    if String.eqb candidate name then None else bindings candidate.

Definition consumeLinear (name : Name) (context : ResourceContext) : ConsumeResult :=
  if sharedLoans context name then
    ConsumeError (OwnerBorrowed name)
  else
    match linearBindings context name with
    | None => ConsumeError (UnknownLinearBinding name)
    | Some ty =>
        Consumed ty
          (mkResourceContext
            (unrestrictedBindings context)
            (affineBindings context)
            (deleteBinding name (linearBindings context))
            (sharedLoans context))
    end.

(* PHIL-CTX-LIN-001 *)
Theorem consumeLinear_success_exact :
  forall (name : Name) (context next : ResourceContext) (ty : Ty),
    consumeLinear name context = Consumed ty next ->
    linearBindings context name = Some ty /\
    linearBindings next name = None /\
    (forall other : Name,
      String.eqb other name = false ->
      linearBindings next other = linearBindings context other) /\
    unrestrictedBindings next = unrestrictedBindings context /\
    affineBindings next = affineBindings context /\
    sharedLoans next = sharedLoans context.
Proof.
  intros name context next ty Hconsume.
  unfold consumeLinear in Hconsume.
  destruct (sharedLoans context name) eqn:Hloan.
  - discriminate.
  - destruct (linearBindings context name) as [found |] eqn:Hfound.
    + inversion Hconsume; subst; clear Hconsume.
      split.
      * reflexivity.
      * split.
        -- simpl. unfold deleteBinding. now rewrite String.eqb_refl.
        -- split.
           ++ intros other Hother.
              simpl. unfold deleteBinding. now rewrite Hother.
           ++ split.
              ** reflexivity.
              ** split; reflexivity.
    + discriminate.
Qed.

Corollary consumeLinear_success_consumes_owner :
  forall (name : Name) (context next : ResourceContext) (ty : Ty),
    consumeLinear name context = Consumed ty next ->
    linearBindings next name = None.
Proof.
  intros name context next ty Hconsume.
  pose proof (consumeLinear_success_exact name context next ty Hconsume) as H.
  destruct H as [_ [Hconsumed _]].
  exact Hconsumed.
Qed.

Corollary consumeLinear_success_preserves_other_linear :
  forall (name other : Name) (context next : ResourceContext) (ty : Ty),
    consumeLinear name context = Consumed ty next ->
    String.eqb other name = false ->
    linearBindings next other = linearBindings context other.
Proof.
  intros name other context next ty Hconsume Hother.
  pose proof (consumeLinear_success_exact name context next ty Hconsume) as H.
  destruct H as [_ [_ [Hpreserved _]]].
  apply Hpreserved.
  exact Hother.
Qed.
