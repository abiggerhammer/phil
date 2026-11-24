From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.
Import ListNotations.
Open Scope bool_scope.
From Phil.Core Require Import Syntax Context DataElimination.

(* The parser, selected bytes, interface derivation, and Core representation
   correspondence are premises outside this finite model. *)
Definition Nominal := (nat * nat)%type.

Definition same_nominal (expected actual : Nominal) : bool :=
  Nat.eqb (fst expected) (fst actual) && Nat.eqb (snd expected) (snd actual).

Definition gated_step {State : Type} (expected actual : Nominal)
    (linear loaned : bool) (native : unit -> option State) : option State :=
  if same_nominal expected actual && linear && negb loaned
  then native tt else None.

Theorem nominal_equality_exact : forall expected actual,
    same_nominal expected actual = true <-> expected = actual.
Proof.
  intros [k i] [k' i'].
  unfold same_nominal; simpl.
  rewrite Bool.andb_true_iff, !Nat.eqb_eq.
  split; intros H.
  - destruct H; subst; reflexivity.
  - inversion H; auto.
Qed.

Theorem failed_gate_produces_no_successor : forall State expected actual linear loaned
    (native : unit -> option State),
    (expected <> actual \/ linear = false \/ loaned = true) ->
    gated_step expected actual linear loaned native = None.
Proof.
  intros State expected actual [|] [|] native H;
    unfold gated_step; destruct (same_nominal expected actual) eqn:E;
    simpl; try reflexivity.
  apply nominal_equality_exact in E. subst.
  destruct H as [H | [H | H]]; contradiction || discriminate.
Qed.

Theorem accepted_gate_uses_native_successor : forall State expected actual linear loaned
    (native : unit -> option State) state,
    gated_step expected actual linear loaned native = Some state ->
    expected = actual /\ linear = true /\ loaned = false /\ native tt = Some state.
Proof.
  intros State expected actual [|] [|] native state;
    unfold gated_step; destruct (same_nominal expected actual) eqn:E;
    simpl; try discriminate.
  apply nominal_equality_exact in E; auto.
Qed.

Theorem accepted_native_consumption_retires_owner : forall owner before after carrier,
    Context.consumeLinear owner before = Context.Consumed carrier after ->
    Context.linearBindings after owner = None.
Proof.
  intros. eapply DataElimination.consuming_linear_aggregate_removes_owner; eauto.
Qed.

Theorem accepted_plan_binds_linear : forall fields dispositions field,
    DataElimination.EliminationPlanAccepted fields dispositions ->
    In field fields ->
    DataElimination.dataFieldMode field = Linear ->
    dispositions (DataElimination.dataFieldKey field) = Some DataElimination.FieldBound.
Proof.
  intros. eapply DataElimination.accepted_plan_binds_every_linear_field; eauto.
Qed.

Print Assumptions nominal_equality_exact.
Print Assumptions failed_gate_produces_no_successor.
Print Assumptions accepted_gate_uses_native_successor.
Print Assumptions accepted_native_consumption_retires_owner.
Print Assumptions accepted_plan_binds_linear.
