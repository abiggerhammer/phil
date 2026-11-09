From Stdlib Require Import Strings.String Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.

(*
  FSEM-01 L-2: conditional normalized Core model of source-checked
  Linear Bytes[N] ownership transfer into a one-slot loop header and
  through one explicit source continue actual. The production Haskell
  checker separately exercises exact finite Map/Set states and errors.
  This is neither dynamic iteration nor universal Haskell↔Rocq refinement.
*)

Theorem linear_loop_entry_consumes_old_owner_and_installs_header :
  forall (initial spent header : Context.ResourceContext)
         (old slot : Syntax.Name) (ty : Syntax.Ty),
    Context.consumeLinear old initial = Context.Consumed ty spent ->
    Context.insertBinding Syntax.Linear slot ty spent =
      Context.Inserted header ->
    Context.linearBindings initial old = Some ty /\
    Context.linearBindings spent old = None /\
    Context.linearBindings header slot = Some ty.
Proof.
  intros initial spent header old slot ty Hconsume Hbind.
  pose proof (Context.consumeLinear_success_exact
    old initial spent ty Hconsume) as [Hbefore [Hspent _]].
  pose proof (Context.insertBinding_success_exact
    Syntax.Linear slot ty spent header Hbind)
    as [_ [_ [_ [Htyped _]]]].
  simpl in Htyped.
  destruct Htyped as [_ [_ Hslot]].
  repeat split; assumption.
Qed.

Theorem linear_loop_header_was_absent_before_exact_insertion :
  forall (spent header : Context.ResourceContext)
         (slot : Syntax.Name) (ty : Syntax.Ty),
    Context.insertBinding Syntax.Linear slot ty spent =
      Context.Inserted header ->
    Context.unrestrictedBindings spent slot = None /\
    Context.affineBindings spent slot = None /\
    Context.linearBindings spent slot = None.
Proof.
  intros spent header slot ty Hbind.
  pose proof (Context.insertBinding_success_exact
    Syntax.Linear slot ty spent header Hbind)
    as [Hu [Ha [Hl _]]].
  repeat split; assumption.
Qed.

Theorem linear_loop_moved_old_owner_does_not_reappear :
  forall (initial spent header : Context.ResourceContext)
         (old slot : Syntax.Name) (ty : Syntax.Ty),
    Context.consumeLinear old initial = Context.Consumed ty spent ->
    Context.insertBinding Syntax.Linear slot ty spent =
      Context.Inserted header ->
    String.eqb old slot = false ->
    Context.linearBindings header old = None.
Proof.
  intros initial spent header old slot ty Hconsume Hbind Hdistinct.
  pose proof (Context.consumeLinear_success_exact
    old initial spent ty Hconsume)
    as [_ [Hspent _]].
  pose proof (Context.insertBinding_success_preserves_other_names
    Syntax.Linear slot old ty spent header Hbind Hdistinct)
    as [_ [_ Hlinear]].
  rewrite Hlinear.
  exact Hspent.
Qed.

Theorem linear_loop_backedge_consumes_then_rebinds_exact_header :
  forall (header spent rebound : Context.ResourceContext)
         (slot : Syntax.Name) (ty : Syntax.Ty),
    Context.consumeLinear slot header = Context.Consumed ty spent ->
    Context.insertBinding Syntax.Linear slot ty spent =
      Context.Inserted rebound ->
    Context.linearBindings header slot = Some ty /\
    Context.linearBindings spent slot = None /\
    Context.linearBindings rebound slot = Some ty.
Proof.
  intros header spent rebound slot ty Hconsume Hbind.
  exact (linear_loop_entry_consumes_old_owner_and_installs_header
    header spent rebound slot slot ty Hconsume Hbind).
Qed.

Theorem linear_loop_reentry_has_exact_linear_header :
  forall (header rebound joined : Context.ResourceContext)
         (slot : Syntax.Name) (ty : Syntax.Ty),
    Context.linearBindings header slot = Some ty ->
    ContextJoin.ContextJoinSuccess [header;rebound] joined ->
    Context.linearBindings joined slot = Some ty.
Proof.
  intros header rebound joined slot ty Hheader Hjoin.
  pose proof (ContextJoin.context_join_linear_converges
    [header;rebound] joined header Hjoin
    (or_introl eq_refl)) as Hconverges.
  unfold ContextJoin.SameBindingMap in Hconverges.
  rewrite (Hconverges slot).
  exact Hheader.
Qed.

Theorem linear_loop_reentry_preserves_every_linear_owner :
  forall (header rebound joined : Context.ResourceContext)
         (owner : Syntax.Name),
    ContextJoin.ContextJoinSuccess [header;rebound] joined ->
    Context.linearBindings joined owner =
      Context.linearBindings header owner /\
    Context.linearBindings joined owner =
      Context.linearBindings rebound owner.
Proof.
  intros header rebound joined owner Hjoin.
  pose proof (ContextJoin.context_join_linear_converges
    [header;rebound] joined header Hjoin
    (or_introl eq_refl)) as Hfirst.
  pose proof (ContextJoin.context_join_linear_converges
    [header;rebound] joined rebound Hjoin
    (or_intror (or_introl eq_refl))) as Hsecond.
  unfold ContextJoin.SameBindingMap in *.
  split; [exact (Hfirst owner)|exact (Hsecond owner)].
Qed.

Theorem linear_loop_reentry_closes_all_loans :
  forall (header rebound joined : Context.ResourceContext),
    ContextJoin.ContextJoinSuccess [header;rebound] joined ->
    ContextJoin.NoLoans joined.
Proof.
  intros header rebound joined Hjoin.
  exact (ContextJoin.context_join_output_has_no_loans
    [header;rebound] joined Hjoin).
Qed.

Theorem linear_loop_duplicate_live_header_is_rejected :
  forall (header : Context.ResourceContext)
         (slot : Syntax.Name) (ty : Syntax.Ty),
    Context.linearBindings header slot = Some ty ->
    Context.insertBinding Syntax.Linear slot ty header =
      Context.InsertError (Context.DuplicateBinding slot).
Proof.
  intros header slot ty Hlive.
  unfold Context.insertBinding, Context.bindingExists,
    Context.bindingPresent.
  rewrite Hlive.
  destruct (Context.unrestrictedBindings header slot);
  destruct (Context.affineBindings header slot);
  reflexivity.
Qed.

Print Assumptions linear_loop_entry_consumes_old_owner_and_installs_header.
Print Assumptions linear_loop_header_was_absent_before_exact_insertion.
Print Assumptions linear_loop_moved_old_owner_does_not_reappear.
Print Assumptions linear_loop_backedge_consumes_then_rebinds_exact_header.
Print Assumptions linear_loop_reentry_has_exact_linear_header.
Print Assumptions linear_loop_reentry_preserves_every_linear_owner.
Print Assumptions linear_loop_reentry_closes_all_loans.
Print Assumptions linear_loop_duplicate_live_header_is_rejected.
