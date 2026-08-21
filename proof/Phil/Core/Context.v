From Coq Require Import Strings.String.

From Phil.Core Require Import Syntax.

(*
  Proof-oriented model of the successful consumeLinear path in
  Phil.Core.Context.

  The implementation uses finite maps and a finite set. For this theorem we
  model those extensionally as lookup functions. This is sufficient to state
  and prove the observable successful-consumption invariant without assuming a
  particular map implementation.
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
| OwnerBorrowed : Name -> CheckError
| UnknownLinearBinding : Name -> CheckError.

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
      * exact Hfound.
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
  tauto.
Qed.

Corollary consumeLinear_success_preserves_other_linear :
  forall (name other : Name) (context next : ResourceContext) (ty : Ty),
    consumeLinear name context = Consumed ty next ->
    String.eqb other name = false ->
    linearBindings next other = linearBindings context other.
Proof.
  intros name other context next ty Hconsume Hother.
  pose proof (consumeLinear_success_exact name context next ty Hconsume) as H.
  tauto.
Qed.
