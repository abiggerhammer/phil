From Stdlib Require Import Lists.List Bool.Bool Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.
From Phil.Surface Require Import SurfaceSourceBoolJoinTelescope.

(*
  FSEM-01 L-1: bounded conditional model for a checked source loop initial
  entry and one continuing backedge. Production Haskell independently checks
  the parsed source actuals, exact context maps, and failure prefixes.
  The hypotheses here represent native insertBinding / joinContinuing
  success; this is NOT universal Haskell↔Rocq refinement or dynamic looping.
*)

Theorem source_loop_bool_header_has_exact_fresh_binding :
  forall (initial header : Context.ResourceContext)
         (slot : Syntax.Name) (ty : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted slot ty initial =
      Context.Inserted header ->
    Context.unrestrictedBindings initial slot = None /\
    Context.affineBindings initial slot = None /\
    Context.linearBindings initial slot = None /\
    Context.unrestrictedBindings header slot = Some ty /\
    Context.affineBindings header slot = None /\
    Context.linearBindings header slot = None.
Proof.
  intros initial header slot ty Hinsert.
  exact (one_checked_unrestricted_join_slot_is_fresh_and_exact
    initial header slot ty Hinsert).
Qed.

Theorem source_loop_bool_reentry_preserves_initial_linear_spectator :
  forall (initial header backedge reentered : Context.ResourceContext)
         (slot owner : Syntax.Name) (ty : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted slot ty initial =
      Context.Inserted header ->
    ContextJoin.ContextJoinSuccess [header;backedge] reentered ->
    Context.linearBindings reentered owner =
      Context.linearBindings initial owner.
Proof.
  intros initial header backedge reentered slot owner ty Hinsert Hjoin.
  pose proof
    (ContextJoin.context_join_linear_converges
      [header;backedge] reentered header Hjoin
      (or_introl eq_refl)) as Hleft.
  unfold ContextJoin.SameBindingMap in Hleft.
  transitivity (Context.linearBindings header owner).
  - exact (Hleft owner).
  - exact (checked_join_slot_preserves_every_linear_owner
      initial header slot owner ty Hinsert).
Qed.

Theorem source_loop_bool_reentry_agrees_with_backedge_linear_spectator :
  forall (header backedge reentered : Context.ResourceContext)
         (owner : Syntax.Name),
    ContextJoin.ContextJoinSuccess [header;backedge] reentered ->
    Context.linearBindings reentered owner =
      Context.linearBindings backedge owner.
Proof.
  intros header backedge reentered owner Hjoin.
  pose proof
    (ContextJoin.context_join_linear_converges
      [header;backedge] reentered backedge Hjoin
      (or_intror (or_introl eq_refl))) as Hright.
  unfold ContextJoin.SameBindingMap in Hright.
  exact (Hright owner).
Qed.

Theorem source_loop_bool_reentry_preserves_closed_loan_state :
  forall (header backedge reentered : Context.ResourceContext),
    ContextJoin.ContextJoinSuccess [header;backedge] reentered ->
    ContextJoin.NoLoans reentered.
Proof.
  intros header backedge reentered Hjoin.
  unfold ContextJoin.NoLoans.
  intro owner.
  exact (ContextJoin.context_join_output_has_no_loans
    [header;backedge] reentered Hjoin owner).
Qed.

Theorem source_loop_bool_header_does_not_consume_linear_state :
  forall (initial header : Context.ResourceContext)
         (slot owner : Syntax.Name) (ty : Syntax.Ty),
    Context.insertBinding Syntax.Unrestricted slot ty initial =
      Context.Inserted header ->
    Context.linearBindings header owner =
      Context.linearBindings initial owner.
Proof.
  intros initial header slot owner ty Hinsert.
  exact (checked_join_slot_preserves_every_linear_owner
    initial header slot owner ty Hinsert).
Qed.

(* A minimal decision model for the explicit type/mode premise. The source
   adapter must establish isExpectedBool from the real checker, not text. *)
Definition sourceLoopEdgeAdmitted
  (mode : Syntax.Mode) (isExpectedBool : bool) : bool :=
  match mode with
  | Syntax.Unrestricted => isExpectedBool
  | _ => false
  end.

Theorem linear_loop_state_actual_is_not_a_valid_bool_edge :
  forall isExpectedBool,
    sourceLoopEdgeAdmitted Syntax.Linear isExpectedBool = false.
Proof. intros []; reflexivity. Qed.

Theorem affine_loop_state_actual_is_not_a_valid_bool_edge :
  forall isExpectedBool,
    sourceLoopEdgeAdmitted Syntax.Affine isExpectedBool = false.
Proof. intros []; reflexivity. Qed.

Theorem unrestricted_wrong_type_is_not_a_valid_bool_edge :
  sourceLoopEdgeAdmitted Syntax.Unrestricted false = false.
Proof. reflexivity. Qed.

Theorem literal_true_loop_invariant_is_discharged :
  sourceBoolInvariantDischarged JoinInvariantLiteralTrue = true.
Proof. reflexivity. Qed.

Theorem unproved_loop_invariant_is_not_discharged :
  sourceBoolInvariantDischarged JoinInvariantUnproved = false.
Proof. reflexivity. Qed.

Print Assumptions source_loop_bool_header_has_exact_fresh_binding.
Print Assumptions source_loop_bool_reentry_preserves_initial_linear_spectator.
Print Assumptions source_loop_bool_reentry_agrees_with_backedge_linear_spectator.
Print Assumptions source_loop_bool_reentry_preserves_closed_loan_state.
Print Assumptions source_loop_bool_header_does_not_consume_linear_state.
Print Assumptions linear_loop_state_actual_is_not_a_valid_bool_edge.
Print Assumptions affine_loop_state_actual_is_not_a_valid_bool_edge.
Print Assumptions unrestricted_wrong_type_is_not_a_valid_bool_edge.
Print Assumptions literal_true_loop_invariant_is_discharged.
Print Assumptions unproved_loop_invariant_is_not_discharged.
