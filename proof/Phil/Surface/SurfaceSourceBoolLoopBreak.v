From Stdlib Require Import Strings.String Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context.
From Phil.Surface Require Import SurfaceSourceBoolJoinTelescope.

(*
  FSEM-01 L-1: conditional model of an actual zero-actual source break
  from a freshly allocated Unrestricted Bool header, with ordinary
  terminal Linear owner consumption after the loop scope closes.
  Real Haskell source/cut/error evidence is separately exercised in CI.
  This does not claim an extracted Haskell-to-Rocq implementation proof.
*)

Definition pruneScopedBoolHeader
  (headerName : Syntax.Name) (header : Context.ResourceContext)
  : Context.ResourceContext :=
  Context.mkResourceContext
    (Context.deleteBinding headerName
      (Context.unrestrictedBindings header))
    (Context.affineBindings header)
    (Context.linearBindings header)
    (Context.sharedLoans header).

Definition NoLinearOwner (state : Context.ResourceContext) : Prop :=
  forall owner : Syntax.Name, Context.linearBindings state owner = None.

Theorem source_break_closes_fresh_bool_header :
  forall (initial header : Context.ResourceContext)
         (name : Syntax.Name) (ty : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted name ty initial =
      Context.Inserted header ->
    Context.unrestrictedBindings (pruneScopedBoolHeader name header) name = None.
Proof.
  intros initial header name ty Hinsert.
  unfold pruneScopedBoolHeader.
  simpl.
  unfold Context.deleteBinding.
  now rewrite String.eqb_refl.
Qed.

Theorem source_break_restores_preloop_unrestricted_lookup :
  forall (initial header : Context.ResourceContext)
         (slot other : Syntax.Name) (ty : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted slot ty initial =
      Context.Inserted header ->
    Context.unrestrictedBindings (pruneScopedBoolHeader slot header) other =
      Context.unrestrictedBindings initial other.
Proof.
  intros initial header slot other ty Hinsert.
  destruct (String.eqb other slot) eqn:Heq.
  - apply String.eqb_eq in Heq. subst other.
    pose proof (one_checked_unrestricted_join_slot_is_fresh_and_exact
      initial header slot ty Hinsert)
      as [Hfresh _].
    rewrite (source_break_closes_fresh_bool_header
      initial header slot ty Hinsert).
    symmetry. exact Hfresh.
  - pose proof (Context.insertBinding_success_preserves_other_names
      Syntax.Unrestricted slot other ty initial header Hinsert Heq)
      as [Hlookup _].
    unfold pruneScopedBoolHeader.
    simpl.
    unfold Context.deleteBinding.
    now rewrite Heq.
Qed.

Theorem source_break_preserves_all_preloop_linear_owners :
  forall (initial header : Context.ResourceContext)
         (slot owner : Syntax.Name) (ty : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted slot ty initial =
      Context.Inserted header ->
    Context.linearBindings (pruneScopedBoolHeader slot header) owner =
      Context.linearBindings initial owner.
Proof.
  intros initial header slot owner ty Hinsert.
  unfold pruneScopedBoolHeader.
  simpl.
  exact (checked_join_slot_preserves_every_linear_owner
    initial header slot owner ty Hinsert).
Qed.

Theorem source_break_preserves_preloop_loan_set :
  forall (initial header : Context.ResourceContext)
         (slot : Syntax.Name) (ty : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted slot ty initial =
      Context.Inserted header ->
    Context.sharedLoans (pruneScopedBoolHeader slot header) =
      Context.sharedLoans initial.
Proof.
  intros initial header slot ty Hinsert.
  pose proof (Context.insertBinding_success_exact
    Syntax.Unrestricted slot ty initial header Hinsert)
      as [_ [_ [_ [_ [_ Hloans]]]]].
  unfold pruneScopedBoolHeader.
  simpl.
  exact Hloans.
Qed.

Theorem source_break_return_consumes_exact_linear_owner :
  forall (exited completed : Context.ResourceContext)
         (owner : Syntax.Name) (ty : Syntax.Ty),
    Context.consumeLinear owner exited = Context.Consumed ty completed ->
    Context.linearBindings exited owner = Some ty /\
    Context.linearBindings completed owner = None /\
    (forall other,
      String.eqb other owner = false ->
      Context.linearBindings completed other =
        Context.linearBindings exited other).
Proof.
  intros exited completed owner ty Hconsume.
  pose proof (Context.consumeLinear_success_exact
    owner exited completed ty Hconsume)
    as [Hbefore [Hafter [Hothers _]]].
  repeat split; assumption.
Qed.

Theorem source_break_return_is_complete_when_no_other_linear_debt :
  forall (exited completed : Context.ResourceContext)
         (owner : Syntax.Name) (ty : Syntax.Ty),
    Context.consumeLinear owner exited = Context.Consumed ty completed ->
    (forall other,
      String.eqb other owner = false ->
      Context.linearBindings exited other = None) ->
    NoLinearOwner completed.
Proof.
  intros exited completed owner ty Hconsume HnoOther.
  pose proof (source_break_return_consumes_exact_linear_owner
    exited completed owner ty Hconsume)
    as [_ [Howner Hothers]].
  unfold NoLinearOwner.
  intro candidate.
  destruct (String.eqb candidate owner) eqn:Heq.
  - apply String.eqb_eq in Heq. subst candidate.
    exact Howner.
  - rewrite (Hothers candidate Heq).
    exact (HnoOther candidate Heq).
Qed.

Theorem source_break_outstanding_linear_debt_blocks_completion :
  forall (exited completed : Context.ResourceContext)
         (owner debt : Syntax.Name) (ownerTy debtTy : Syntax.Ty),
    String.eqb debt owner = false ->
    Context.linearBindings exited debt = Some debtTy ->
    Context.consumeLinear owner exited =
      Context.Consumed ownerTy completed ->
    ~ NoLinearOwner completed.
Proof.
  intros exited completed owner debt ownerTy debtTy
    Hdistinct Hdebt Hconsume Hcomplete.
  pose proof (source_break_return_consumes_exact_linear_owner
    exited completed owner ownerTy Hconsume)
    as [_ [_ Hothers]].
  specialize (Hothers debt Hdistinct).
  unfold NoLinearOwner in Hcomplete.
  specialize (Hcomplete debt).
  rewrite Hcomplete in Hothers.
  rewrite Hdebt in Hothers.
  discriminate.
Qed.

Theorem source_break_absent_exit_actuals_are_exactly_zero :
  @nil bool = [].
Proof. reflexivity. Qed.

Print Assumptions source_break_closes_fresh_bool_header.
Print Assumptions source_break_restores_preloop_unrestricted_lookup.
Print Assumptions source_break_preserves_all_preloop_linear_owners.
Print Assumptions source_break_preserves_preloop_loan_set.
Print Assumptions source_break_return_consumes_exact_linear_owner.
Print Assumptions source_break_return_is_complete_when_no_other_linear_debt.
Print Assumptions source_break_outstanding_linear_debt_blocks_completion.
Print Assumptions source_break_absent_exit_actuals_are_exactly_zero.
