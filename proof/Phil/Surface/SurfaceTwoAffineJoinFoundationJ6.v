From Stdlib Require Import Lists.List Strings.String Bool.Bool.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.
From Phil.Surface Require Import SurfaceSourceAffineJoinScopeBridge.

(*
  FSEM-01 J-6A: mathematical groundwork for a future selected Affine
  source join slot. The source fixture checker independently validates
  two different, legitimately admitted nominal owners and a fresh
  lexical successor; the production Surface join-state elaborator is
  NOT extended in this groundwork PR.
  No Haskell implementation refinement, runtime phi value, nominal
  lifecycle evidence, or source branch execution is assumed/proved.
*)

(* A pure, pointwise model of moving an Affine binding from a branch.
   The Haskell driver separately calls production Core.consumeAffine. *)
Definition j6_move_affine
    (owner : Syntax.Name) (before : Context.ResourceContext)
  : Context.ResourceContext :=
  Context.mkResourceContext
    (Context.unrestrictedBindings before)
    (Context.deleteBinding owner (Context.affineBindings before))
    (Context.linearBindings before)
    (Context.sharedLoans before).

Theorem j6_model_move_removes_own_affine_binding :
  forall (owner : Syntax.Name) (before : Context.ResourceContext),
    Context.affineBindings (j6_move_affine owner before) owner = None.
Proof.
  intros owner before. unfold j6_move_affine.
  simpl. unfold Context.deleteBinding.
  now rewrite String.eqb_refl.
Qed.

Theorem j6_model_move_preserves_other_affine_bindings :
  forall (owner other : Syntax.Name) (before : Context.ResourceContext),
    String.eqb other owner = false ->
    Context.affineBindings (j6_move_affine owner before) other =
      Context.affineBindings before other.
Proof.
  intros owner other before Hneq.
  unfold j6_move_affine. simpl.
  unfold Context.deleteBinding. now rewrite Hneq.
Qed.

Theorem j6_model_move_preserves_unrestricted_linear_and_loans :
  forall (owner : Syntax.Name) (before : Context.ResourceContext),
    Context.unrestrictedBindings (j6_move_affine owner before) =
      Context.unrestrictedBindings before /\
    Context.linearBindings (j6_move_affine owner before) =
      Context.linearBindings before /\
    Context.sharedLoans (j6_move_affine owner before) =
      Context.sharedLoans before.
Proof. intros; repeat split; reflexivity. Qed.

Theorem j6_selected_slot_does_not_resurrect_either_source_owner :
  forall (left right joined bound : Context.ResourceContext)
         (leftOwner rightOwner selected : Syntax.Name) (permit : Syntax.Ty),
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    Context.affineBindings left leftOwner = None ->
    Context.affineBindings right rightOwner = None ->
    Context.insertBinding Syntax.Affine selected permit joined =
      Context.Inserted bound ->
    String.eqb leftOwner selected = false ->
    String.eqb rightOwner selected = false ->
    Context.affineBindings joined leftOwner = None /\
    Context.affineBindings joined rightOwner = None /\
    Context.affineBindings bound leftOwner = None /\
    Context.affineBindings bound rightOwner = None /\
    Context.affineBindings bound selected = Some permit /\
    ContextJoin.NoLoans bound.
Proof.
  intros left right joined bound leftOwner rightOwner selected permit
    Hjoin Hleft Hright Hinsert HdistinctLeft HdistinctRight.
  pose proof
    (affine_source_branch_without_owner_cannot_restore_it_at_join
      left right joined leftOwner Hjoin Hleft) as HgoneLeft.
  pose proof
    (affine_source_other_branch_without_owner_cannot_restore_it_at_join
      left right joined rightOwner Hjoin Hright) as HgoneRight.
  pose proof
    (Context.insertBinding_success_exact
      Syntax.Affine selected permit joined bound Hinsert)
    as [_ [_ [_ [Htyped [Hpreserved Hloans]]]]].
  simpl in Htyped.
  destruct Htyped as [_ [Hslot _]].
  pose proof (Hpreserved leftOwner HdistinctLeft) as [_ [HremLeft _]].
  pose proof (Hpreserved rightOwner HdistinctRight) as [_ [HremRight _]].
  pose proof (ContextJoin.context_join_output_has_no_loans
    [left;right] joined Hjoin) as HnoLoans.
  repeat split.
  - exact HgoneLeft.
  - exact HgoneRight.
  - rewrite HremLeft. exact HgoneLeft.
  - rewrite HremRight. exact HgoneRight.
  - exact Hslot.
  - unfold ContextJoin.NoLoans in *.
    intro owner. rewrite Hloans. exact (HnoLoans owner).
Qed.

Theorem j6_retained_affine_spectator_survives_join_and_new_slot :
  forall (left right joined bound : Context.ResourceContext)
         (spectator selected : Syntax.Name) (spectatorTy permitTy : Syntax.Ty),
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    Context.affineBindings left spectator = Some spectatorTy ->
    Context.affineBindings right spectator = Some spectatorTy ->
    Context.insertBinding Syntax.Affine selected permitTy joined =
      Context.Inserted bound ->
    String.eqb spectator selected = false ->
    Context.affineBindings bound spectator = Some spectatorTy.
Proof.
  intros left right joined bound spectator selected spectatorTy permitTy
    Hjoin Hleft Hright Hinsert Hdistinct.
  pose proof
    (affine_source_owner_kept_by_both_branches_is_retained
      left right joined spectator spectatorTy Hjoin Hleft Hright) as Hcommon.
  pose proof
    (Context.insertBinding_success_preserves_other_names
      Syntax.Affine selected spectator permitTy joined bound
      Hinsert Hdistinct) as [_ [Hpreserved _]].
  rewrite Hpreserved. exact Hcommon.
Qed.

Lemma j6_affine_slot_insertion_preserves_all_linear_bindings :
  forall (joined bound : Context.ResourceContext)
         (selected : Syntax.Name) (permitTy : Syntax.Ty),
    Context.insertBinding Syntax.Affine selected permitTy joined =
      Context.Inserted bound ->
    Context.linearBindings bound = Context.linearBindings joined.
Proof.
  intros joined bound selected permitTy Hinsert.
  unfold Context.insertBinding in Hinsert.
  destruct (Context.bindingExists selected joined) eqn:Hexists;
    try discriminate.
  inversion Hinsert; subst bound. reflexivity.
Qed.

Theorem j6_linear_spectator_survives_join_and_affine_slot :
  forall (left right joined bound : Context.ResourceContext)
         (spectator selected : Syntax.Name) (permitTy : Syntax.Ty),
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    Context.insertBinding Syntax.Affine selected permitTy joined =
      Context.Inserted bound ->
    Context.linearBindings bound spectator =
      Context.linearBindings left spectator /\
    Context.linearBindings bound spectator =
      Context.linearBindings right spectator.
Proof.
  intros left right joined bound spectator selected permitTy Hjoin Hinsert.
  pose proof (j6_affine_slot_insertion_preserves_all_linear_bindings
    joined bound selected permitTy Hinsert) as Hsame.
  rewrite Hsame.
  split.
  - pose proof (ContextJoin.context_join_linear_converges
      [left;right] joined left Hjoin (or_introl eq_refl)) as Hleft.
    unfold ContextJoin.SameBindingMap in Hleft. exact (Hleft spectator).
  - pose proof (ContextJoin.context_join_linear_converges
      [left;right] joined right Hjoin
      (or_intror (or_introl eq_refl))) as Hright.
    unfold ContextJoin.SameBindingMap in Hright. exact (Hright spectator).
Qed.

Theorem j6_fresh_affine_slot_cannot_be_installed_twice :
  forall (joined bound : Context.ResourceContext)
         (selected : Syntax.Name) (permitTy : Syntax.Ty),
    Context.insertBinding Syntax.Affine selected permitTy joined =
      Context.Inserted bound ->
    Context.insertBinding Syntax.Affine selected permitTy bound =
      Context.InsertError (Context.DuplicateBinding selected).
Proof.
  intros joined bound selected permitTy Hinsert.
  pose proof (Context.insertBinding_success_exact
    Syntax.Affine selected permitTy joined bound Hinsert)
    as [_ [_ [_ [Htyped _]]]].
  simpl in Htyped.
  destruct Htyped as [_ [Hslot _]].
  unfold Context.insertBinding, Context.bindingExists,
    Context.bindingPresent.
  rewrite Hslot.
  destruct (Context.unrestrictedBindings bound selected);
  destruct (Context.linearBindings bound selected);
  reflexivity.
Qed.

Print Assumptions j6_model_move_removes_own_affine_binding.
Print Assumptions j6_model_move_preserves_other_affine_bindings.
Print Assumptions j6_model_move_preserves_unrestricted_linear_and_loans.
Print Assumptions j6_selected_slot_does_not_resurrect_either_source_owner.
Print Assumptions j6_retained_affine_spectator_survives_join_and_new_slot.
Print Assumptions j6_linear_spectator_survives_join_and_affine_slot.
Print Assumptions j6_fresh_affine_slot_cannot_be_installed_twice.
