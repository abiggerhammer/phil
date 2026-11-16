From Stdlib Require Import Strings.String Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.

(*
  FSEM-01 J-5: one source-checked Linear Bytes[N] post-if join-state
  binding. These are conditional facts about the existing Core consume,
  join and insertion relations. Separate actual Grammar-v1 source tests
  enforce exact binder identity, predecessor value and production errors.
  No arbitrary source control or runtime phi execution is proved here.
*)

Theorem j5_parallel_source_moves_spend_one_owner_on_each_path :
  forall (initial leftSpent rightSpent : Context.ResourceContext)
         (old : Syntax.Name) (ty : Syntax.Ty),
    Context.consumeLinear old initial = Context.Consumed ty leftSpent ->
    Context.consumeLinear old initial = Context.Consumed ty rightSpent ->
    Context.linearBindings initial old = Some ty /\
    Context.linearBindings leftSpent old = None /\
    Context.linearBindings rightSpent old = None /\
    leftSpent = rightSpent.
Proof.
  intros initial leftSpent rightSpent old ty Hleft Hright.
  pose proof (Context.consumeLinear_success_exact
    old initial leftSpent ty Hleft) as [Hbefore [Hspent _]].
  pose proof (Context.consumeLinear_success_exact
    old initial rightSpent ty Hright) as [_ [Hother _]].
  assert (leftSpent = rightSpent) by congruence.
  repeat split; assumption.
Qed.

Theorem j5_successful_join_and_fresh_linear_slot :
  forall (left right joined bound : Context.ResourceContext)
         (old slot : Syntax.Name) (ty : Syntax.Ty),
    Context.linearBindings left old = None ->
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    Context.insertBinding Syntax.Linear slot ty joined =
      Context.Inserted bound ->
    String.eqb old slot = false ->
    Context.linearBindings joined old = None /\
    Context.linearBindings bound old = None /\
    Context.linearBindings bound slot = Some ty /\
    ContextJoin.NoLoans bound.
Proof.
  intros left right joined bound old slot ty
    Hspent Hjoin Hinsert Hdistinct.
  pose proof (ContextJoin.context_join_linear_converges
    [left;right] joined left Hjoin (or_introl eq_refl))
    as Hconverges.
  unfold ContextJoin.SameBindingMap in Hconverges.
  assert (Hold : Context.linearBindings joined old = None).
  { rewrite (Hconverges old). exact Hspent. }
  pose proof (Context.insertBinding_success_exact
    Syntax.Linear slot ty joined bound Hinsert)
    as [_ [_ [_ [Htyped [Hpreserved Hloans]]]]].
  simpl in Htyped.
  destruct Htyped as [_ [_ Hslot]].
  pose proof (Hpreserved old Hdistinct)
    as [_ [_ HstillSpent]].
  pose proof (ContextJoin.context_join_output_has_no_loans
    [left;right] joined Hjoin) as HnoLoans.
  repeat split.
  - exact Hold.
  - rewrite HstillSpent. exact Hold.
  - exact Hslot.
  - unfold ContextJoin.NoLoans in *.
    intro name. rewrite Hloans. exact (HnoLoans name).
Qed.

Theorem j5_linear_spectator_preserved_by_branch_join_and_slot :
  forall (initial left right joined bound : Context.ResourceContext)
         (old slot spectator : Syntax.Name) (ty : Syntax.Ty),
    Context.consumeLinear old initial = Context.Consumed ty left ->
    Context.consumeLinear old initial = Context.Consumed ty right ->
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    Context.insertBinding Syntax.Linear slot ty joined =
      Context.Inserted bound ->
    String.eqb spectator old = false ->
    String.eqb spectator slot = false ->
    Context.linearBindings bound spectator =
      Context.linearBindings initial spectator.
Proof.
  intros initial left right joined bound old slot spectator ty
    Hleft _ Hjoin Hinsert HneqOld HneqSlot.
  pose proof (Context.consumeLinear_success_preserves_other_linear
    old spectator initial left ty Hleft HneqOld) as Hcons.
  pose proof (ContextJoin.context_join_linear_converges
    [left;right] joined left Hjoin (or_introl eq_refl))
    as Hconverges.
  unfold ContextJoin.SameBindingMap in Hconverges.
  pose proof (Context.insertBinding_success_preserves_other_names
    Syntax.Linear slot spectator ty joined bound
    Hinsert HneqSlot) as [_ [_ Hslot]].
  rewrite Hslot, (Hconverges spectator).
  exact Hcons.
Qed.

Theorem j5_slot_cannot_be_inserted_twice :
  forall (joined bound : Context.ResourceContext)
         (slot : Syntax.Name) (ty : Syntax.Ty),
    Context.insertBinding Syntax.Linear slot ty joined =
      Context.Inserted bound ->
    Context.insertBinding Syntax.Linear slot ty bound =
      Context.InsertError (Context.DuplicateBinding slot).
Proof.
  intros joined bound slot ty Hinsert.
  pose proof (Context.insertBinding_success_exact
    Syntax.Linear slot ty joined bound Hinsert)
    as [_ [_ [_ [Htyped _]]]].
  simpl in Htyped.
  destruct Htyped as [_ [_ Hslot]].
  unfold Context.insertBinding, Context.bindingExists,
    Context.bindingPresent.
  rewrite Hslot.
  destruct (Context.unrestrictedBindings bound slot);
  destruct (Context.affineBindings bound slot);
  reflexivity.
Qed.

Theorem j5_linear_join_return_consumes_fresh_slot_once :
  forall (bound returned : Context.ResourceContext)
         (slot : Syntax.Name) (ty : Syntax.Ty),
    Context.consumeLinear slot bound = Context.Consumed ty returned ->
    Context.linearBindings bound slot = Some ty /\
    Context.linearBindings returned slot = None.
Proof.
  intros bound returned slot ty H.
  pose proof (Context.consumeLinear_success_exact
    slot bound returned ty H) as [Hpresent [Hspent _]].
  now split.
Qed.

Theorem j5_live_loan_refuses_move_before_join :
  forall (context : Context.ResourceContext)
         (owner : Syntax.Name),
    Context.sharedLoans context owner = true ->
    Context.consumeLinear owner context =
      Context.ConsumeError (Context.OwnerBorrowed owner).
Proof.
  intros context owner Hloan.
  unfold Context.consumeLinear. now rewrite Hloan.
Qed.

Print Assumptions j5_parallel_source_moves_spend_one_owner_on_each_path.
Print Assumptions j5_successful_join_and_fresh_linear_slot.
Print Assumptions j5_linear_spectator_preserved_by_branch_join_and_slot.
Print Assumptions j5_slot_cannot_be_inserted_twice.
Print Assumptions j5_linear_join_return_consumes_fresh_slot_once.
Print Assumptions j5_live_loan_refuses_move_before_join.
