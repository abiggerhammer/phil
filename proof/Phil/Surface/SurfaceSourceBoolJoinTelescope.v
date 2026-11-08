From Stdlib Require Import Lists.List Bool.Bool Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.

(*
  FSEM-01: one nonempty post-join Bool source telescope, following
  two checked predecessor values and a successful native resource join.
  Finite Haskell tests observe the actual production predecessor/checker
  transitions and errors. These are conditional normalized Rocq facts,
  not an extracted source parser or arbitrary invariant solver.
*)

Definition sourceBoolPhi (condition left right : bool) : bool :=
  if condition then left else right.

Theorem bool_phi_chooses_a_checked_predecessor :
  forall condition left right,
    sourceBoolPhi condition left right = left \/
    sourceBoolPhi condition left right = right.
Proof.
  intros condition left right.
  destruct condition; simpl; auto.
Qed.

(* The checked two-branch predecessor values need not be equal. A join-state
   Bool binder represents a phi value whose source depends on the decision. *)
Theorem distinct_source_boolean_operands_are_representable :
  sourceBoolPhi true true false = true /\
  sourceBoolPhi false true false = false.
Proof. split; reflexivity. Qed.

Inductive SourceBoolInvariantProof : Type :=
| JoinInvariantLiteralTrue
| JoinInvariantReflexive
| JoinInvariantUnproved.

Definition sourceBoolInvariantDischarged
  (evidence : SourceBoolInvariantProof) : bool :=
  match evidence with
  | JoinInvariantLiteralTrue => true
  | JoinInvariantReflexive => true
  | JoinInvariantUnproved => false
  end.

Theorem literal_true_invariant_is_discharged :
  sourceBoolInvariantDischarged JoinInvariantLiteralTrue = true.
Proof. reflexivity. Qed.

Theorem reflexive_post_join_bool_invariant_is_discharged :
  forall chosen : bool,
    chosen = chosen /\
    sourceBoolInvariantDischarged JoinInvariantReflexive = true.
Proof.
  intro chosen; split; reflexivity.
Qed.

Theorem unproved_join_invariant_is_not_accepted :
  sourceBoolInvariantDischarged JoinInvariantUnproved = false.
Proof. reflexivity. Qed.

(* The exact normalized production Core insertion (not an abstract arbitrary
   record rewrite) installs the one post-join Unrestricted binder. The source
   adapter supplies its exact binder key and source-checked Bool type. *)
Theorem one_checked_unrestricted_join_slot_is_fresh_and_exact :
  forall (joined after : Context.ResourceContext)
         (slot : Syntax.Name) (ty : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted slot ty joined =
      Context.Inserted after ->
    Context.unrestrictedBindings joined slot = None /\
    Context.affineBindings joined slot = None /\
    Context.linearBindings joined slot = None /\
    Context.unrestrictedBindings after slot = Some ty /\
    Context.affineBindings after slot = None /\
    Context.linearBindings after slot = None.
Proof.
  intros joined after slot ty Hinsert.
  pose proof
    (Context.insertBinding_success_exact
      Syntax.Unrestricted slot ty joined after Hinsert)
    as [Hu [Ha [Hl [Hslot _]]]].
  simpl in Hslot.
  destruct Hslot as [Hsu [Hsa Hsl]].
  repeat split; assumption.
Qed.

Theorem checked_join_slot_preserves_every_linear_owner :
  forall (joined after : Context.ResourceContext)
         (slot owner : Syntax.Name) (ty : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted slot ty joined =
      Context.Inserted after ->
    Context.linearBindings after owner =
      Context.linearBindings joined owner.
Proof.
  intros joined after slot owner ty Hinsert.
  pose proof
    (Context.insertBinding_success_exact
      Syntax.Unrestricted slot ty joined after Hinsert)
    as [_ [_ [Hfresh [_ [Hothers _]]]]].
  destruct (String.eqb owner slot) eqn:Heq.
  - apply String.eqb_eq in Heq. subst owner.
    pose proof
      (one_checked_unrestricted_join_slot_is_fresh_and_exact
        joined after slot ty Hinsert)
      as [_ [_ [Hbefore [_ [_ Hafter]]]]].
    rewrite Hbefore, Hafter. reflexivity.
  - pose proof (Hothers owner Heq) as [_ [_ Hlinear]].
    exact Hlinear.
Qed.

Theorem checked_join_slot_preserves_join_loan_closure :
  forall (left right joined after : Context.ResourceContext)
         (slot : Syntax.Name) (ty : Syntax.Ty),
    ContextJoin.ContextJoinSuccess [left; right] joined ->
    Context.insertBinding Syntax.Unrestricted slot ty joined =
      Context.Inserted after ->
    ContextJoin.NoLoans after.
Proof.
  intros left right joined after slot ty Hjoin Hinsert.
  pose proof
    (Context.insertBinding_success_exact
      Syntax.Unrestricted slot ty joined after Hinsert)
    as [_ [_ [_ [_ [_ HsameLoans]]]]].
  unfold ContextJoin.NoLoans.
  intro owner.
  rewrite HsameLoans.
  exact (ContextJoin.context_join_output_has_no_loans
    [left; right] joined Hjoin owner).
Qed.

Theorem checked_join_slot_preserves_source_linear_spectator :
  forall (left right joined after : Context.ResourceContext)
         (slot owner : Syntax.Name) (ty : Syntax.Ty),
    ContextJoin.ContextJoinSuccess [left; right] joined ->
    Context.insertBinding Syntax.Unrestricted slot ty joined =
      Context.Inserted after ->
    Context.linearBindings after owner =
      Context.linearBindings left owner /\
    Context.linearBindings after owner =
      Context.linearBindings right owner.
Proof.
  intros left right joined after slot owner ty Hjoin Hinsert.
  pose proof
    (checked_join_slot_preserves_every_linear_owner
      joined after slot owner ty Hinsert) as Hsame.
  split; rewrite Hsame.
  - pose proof
      (ContextJoin.context_join_linear_converges
        [left;right] joined left Hjoin
        (or_introl eq_refl)) as Hleft.
    unfold ContextJoin.SameBindingMap in Hleft.
    exact (Hleft owner).
  - pose proof
      (ContextJoin.context_join_linear_converges
        [left;right] joined right Hjoin
        (or_intror (or_introl eq_refl))) as Hright.
    unfold ContextJoin.SameBindingMap in Hright.
    exact (Hright owner).
Qed.

Print Assumptions bool_phi_chooses_a_checked_predecessor.
Print Assumptions distinct_source_boolean_operands_are_representable.
Print Assumptions literal_true_invariant_is_discharged.
Print Assumptions reflexive_post_join_bool_invariant_is_discharged.
Print Assumptions unproved_join_invariant_is_not_accepted.
Print Assumptions one_checked_unrestricted_join_slot_is_fresh_and_exact.
Print Assumptions checked_join_slot_preserves_every_linear_owner.
Print Assumptions checked_join_slot_preserves_join_loan_closure.
Print Assumptions checked_join_slot_preserves_source_linear_spectator.
