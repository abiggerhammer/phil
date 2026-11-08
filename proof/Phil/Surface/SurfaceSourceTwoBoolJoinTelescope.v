From Stdlib Require Import Lists.List Bool.Bool Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.
From Phil.Surface Require Import SurfaceSourceBoolJoinTelescope.

(*
  FSEM-01: conditional normalized Core proof for two fresh Unrestricted
  state binders. Finite source-derived Haskell tests check native Map/Set
  behavior; this is not universal Haskell-to-Rocq implementation refinement.
*)

Definition twoBoolPhi
  (condition leftFirst leftSecond rightFirst rightSecond : bool)
  : bool * bool :=
  (sourceBoolPhi condition leftFirst rightFirst,
   sourceBoolPhi condition leftSecond rightSecond).

Theorem two_bool_phi_preserves_branch_and_tuple_position :
  forall condition leftFirst leftSecond rightFirst rightSecond,
    twoBoolPhi condition leftFirst leftSecond rightFirst rightSecond =
      if condition then (leftFirst,leftSecond) else (rightFirst,rightSecond).
Proof.
  intros condition leftFirst leftSecond rightFirst rightSecond.
  destruct condition; reflexivity.
Qed.

Theorem two_bool_phi_does_not_require_branch_value_equality :
  twoBoolPhi true true false false true = (true,false) /\
  twoBoolPhi false true false false true = (false,true).
Proof. split; reflexivity. Qed.

Theorem two_successful_unrestricted_slots_have_distinct_names :
  forall (joined firstBound bothBound : Context.ResourceContext)
         (first second : Syntax.Name) (firstTy secondTy : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted first firstTy joined =
      Context.Inserted firstBound ->
    Context.insertBinding Syntax.Unrestricted second secondTy firstBound =
      Context.Inserted bothBound ->
    first <> second.
Proof.
  intros joined firstBound bothBound first second firstTy secondTy
    Hfirst Hsecond Heq.
  pose proof
    (one_checked_unrestricted_join_slot_is_fresh_and_exact
      joined firstBound first firstTy Hfirst)
      as [_ [_ [_ [Hpresent _]]]].
  pose proof
    (one_checked_unrestricted_join_slot_is_fresh_and_exact
      firstBound bothBound second secondTy Hsecond)
      as [Habsent _].
  subst second.
  rewrite Hpresent in Habsent.
  discriminate.
Qed.

Theorem two_successful_unrestricted_slots_retain_first_checked_type :
  forall (joined firstBound bothBound : Context.ResourceContext)
         (first second : Syntax.Name) (firstTy secondTy : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted first firstTy joined =
      Context.Inserted firstBound ->
    Context.insertBinding Syntax.Unrestricted second secondTy firstBound =
      Context.Inserted bothBound ->
    Context.unrestrictedBindings bothBound first = Some firstTy.
Proof.
  intros joined firstBound bothBound first second firstTy secondTy
    Hfirst Hsecond.
  pose proof
    (two_successful_unrestricted_slots_have_distinct_names
      joined firstBound bothBound first second firstTy secondTy Hfirst Hsecond)
      as Hneq.
  pose proof
    (one_checked_unrestricted_join_slot_is_fresh_and_exact
      joined firstBound first firstTy Hfirst)
      as [_ [_ [_ [Hpresent _]]]].
  pose proof
    (Context.insertBinding_success_exact Syntax.Unrestricted second
      secondTy firstBound bothBound Hsecond)
      as [_ [_ [_ [_ [Hothers _]]]]].
  assert (String.eqb first second = false) as Hdiff.
  { apply String.eqb_neq. exact Hneq. }
  specialize (Hothers first Hdiff) as [Hsame _].
  rewrite Hsame.
  exact Hpresent.
Qed.

Theorem two_checked_unrestricted_slots_preserve_every_linear_owner :
  forall (joined firstBound bothBound : Context.ResourceContext)
         (first second owner : Syntax.Name) (firstTy secondTy : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted first firstTy joined =
      Context.Inserted firstBound ->
    Context.insertBinding Syntax.Unrestricted second secondTy firstBound =
      Context.Inserted bothBound ->
    Context.linearBindings bothBound owner =
      Context.linearBindings joined owner.
Proof.
  intros joined firstBound bothBound first second owner
    firstTy secondTy Hfirst Hsecond.
  rewrite (checked_join_slot_preserves_every_linear_owner
    firstBound bothBound second owner secondTy Hsecond).
  exact (checked_join_slot_preserves_every_linear_owner
    joined firstBound first owner firstTy Hfirst).
Qed.

Theorem two_checked_slots_preserve_both_source_linear_spectators :
  forall (left right joined firstBound bothBound : Context.ResourceContext)
         (first second owner : Syntax.Name) (firstTy secondTy : Syntax.Ty),
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    Context.insertBinding Syntax.Unrestricted first firstTy joined =
      Context.Inserted firstBound ->
    Context.insertBinding Syntax.Unrestricted second secondTy firstBound =
      Context.Inserted bothBound ->
    Context.linearBindings bothBound owner = Context.linearBindings left owner /\
    Context.linearBindings bothBound owner = Context.linearBindings right owner.
Proof.
  intros left right joined firstBound bothBound
    first second owner firstTy secondTy Hjoin Hfirst Hsecond.
  pose proof
    (checked_join_slot_preserves_source_linear_spectator
      left right joined firstBound first owner firstTy Hjoin Hfirst)
    as [Hleft Hright].
  pose proof
    (checked_join_slot_preserves_every_linear_owner
      firstBound bothBound second owner secondTy Hsecond) as Hsame.
  split; rewrite Hsame; assumption.
Qed.

Theorem two_checked_slots_preserve_closed_loans :
  forall (left right joined firstBound bothBound : Context.ResourceContext)
         (first second : Syntax.Name) (firstTy secondTy : Syntax.Ty),
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    Context.insertBinding Syntax.Unrestricted first firstTy joined =
      Context.Inserted firstBound ->
    Context.insertBinding Syntax.Unrestricted second secondTy firstBound =
      Context.Inserted bothBound ->
    ContextJoin.NoLoans bothBound.
Proof.
  intros left right joined firstBound bothBound first second
    firstTy secondTy Hjoin Hfirst Hsecond.
  pose proof
    (checked_join_slot_preserves_join_loan_closure
      left right joined firstBound first firstTy Hjoin Hfirst) as Hclosed.
  pose proof
    (Context.insertBinding_success_exact Syntax.Unrestricted second
      secondTy firstBound bothBound Hsecond)
    as [_ [_ [_ [_ [_ HsameLoans]]]]].
  unfold ContextJoin.NoLoans in *.
  intro owner.
  rewrite HsameLoans.
  exact (Hclosed owner).
Qed.

Print Assumptions two_bool_phi_preserves_branch_and_tuple_position.
Print Assumptions two_bool_phi_does_not_require_branch_value_equality.
Print Assumptions two_successful_unrestricted_slots_have_distinct_names.
Print Assumptions two_successful_unrestricted_slots_retain_first_checked_type.
Print Assumptions two_checked_unrestricted_slots_preserve_every_linear_owner.
Print Assumptions two_checked_slots_preserve_both_source_linear_spectators.
Print Assumptions two_checked_slots_preserve_closed_loans.
