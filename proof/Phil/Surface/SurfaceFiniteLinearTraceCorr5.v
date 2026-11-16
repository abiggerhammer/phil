From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context.
From Phil.Surface Require Import
  SurfaceFiniteContextFrame SurfaceFiniteLinearStepCorr4.

(*
  FSEM-01 CORR-5: compose the executable CORR-4 finite Linear transitions.
  Computed failure is sticky: later commands do not execute or create
  state. The theorem is universal over finite MODEL traces whose initial
  finite snapshot is exactly related to an extensional Core context.

  Actual Haskell Grammar-v1 source->wire fidelity, Unicode Text/Name,
  GHC Map/Set semantics and source error-class refinements remain
  independently TESTED premises, not new axioms or global proofs.
*)

Module F := SurfaceFiniteContextFrame.
Module One := SurfaceFiniteLinearStepCorr4.

Inductive LinearCommand : Type :=
| MoveLinear : Syntax.Name -> LinearCommand
| BindLinear : Syntax.Name -> Syntax.Ty -> LinearCommand.

Inductive LinearFailure : Type :=
| LoanRefusal : Syntax.Name -> LinearFailure
| MissingLinear : Syntax.Name -> LinearFailure
| DuplicateLinear : Syntax.Name -> LinearFailure.

Inductive FiniteStepResult : Type :=
| FiniteStepOk : F.FiniteSnapshot -> FiniteStepResult
| FiniteStepError : LinearFailure -> FiniteStepResult.

Inductive CoreStepResult : Type :=
| CoreStepOk : Context.ResourceContext -> CoreStepResult
| CoreStepError : LinearFailure -> CoreStepResult.

Definition finiteStep (cmd : LinearCommand) (snap : F.FiniteSnapshot)
  : FiniteStepResult :=
  match cmd with
  | MoveLinear name =>
      match One.consumeFiniteLinear name snap with
      | One.FiniteConsumed _ successor => FiniteStepOk successor
      | One.FiniteBorrowed => FiniteStepError (LoanRefusal name)
      | One.FiniteMissing => FiniteStepError (MissingLinear name)
      end
  | BindLinear name ty =>
      match One.insertFiniteLinear name ty snap with
      | One.FiniteInserted successor => FiniteStepOk successor
      | One.FiniteDuplicate => FiniteStepError (DuplicateLinear name)
      end
  end.

Definition coreStep (cmd : LinearCommand) (ctx : Context.ResourceContext)
  : CoreStepResult :=
  match cmd with
  | MoveLinear name =>
      match Context.consumeLinear name ctx with
      | Context.Consumed _ successor => CoreStepOk successor
      | Context.ConsumeError (Context.OwnerBorrowed _) =>
          CoreStepError (LoanRefusal name)
      | Context.ConsumeError (Context.UnknownLinearBinding _) =>
          CoreStepError (MissingLinear name)
      | Context.ConsumeError (Context.DuplicateBinding _) =>
          CoreStepError (DuplicateLinear name)
      end
  | BindLinear name ty =>
      match Context.insertBinding Syntax.Linear name ty ctx with
      | Context.Inserted successor => CoreStepOk successor
      | Context.InsertError (Context.DuplicateBinding _) =>
          CoreStepError (DuplicateLinear name)
      | Context.InsertError (Context.OwnerBorrowed _) =>
          CoreStepError (LoanRefusal name)
      | Context.InsertError (Context.UnknownLinearBinding _) =>
          CoreStepError (MissingLinear name)
      end
  end.

Theorem corr5_computed_step_preserves_exact_context :
  forall snap ctx command,
    F.ExactFiniteRelation snap ctx ->
    match finiteStep command snap with
    | FiniteStepError reason =>
        coreStep command ctx = CoreStepError reason
    | FiniteStepOk successor =>
        exists next,
          coreStep command ctx = CoreStepOk next /\
          F.ExactFiniteRelation successor next
    end.
Proof.
  intros snap ctx command Hrel.
  destruct command as [owner | owner ty]; simpl.
  - pose proof
      (One.corr4_finite_linear_consume_exact_decision
        snap ctx owner Hrel) as Hstep.
    destruct (One.consumeFiniteLinear owner snap) as
      [found successor | |] eqn:Heval; simpl in Hstep.
    + destruct Hstep as [next [Hcore Hnext]].
      exists next. split; [| exact Hnext].
      unfold coreStep. now rewrite Hcore.
    + unfold coreStep. now rewrite Hstep.
    + unfold coreStep. now rewrite Hstep.
  - pose proof
      (One.corr4_finite_linear_insert_exact_decision
        snap ctx owner ty Hrel) as Hstep.
    destruct (One.insertFiniteLinear owner ty snap) as
      [successor |] eqn:Heval; simpl in Hstep.
    + destruct Hstep as [next [Hcore Hnext]].
      exists next. split; [| exact Hnext].
      unfold coreStep. now rewrite Hcore.
    + unfold coreStep. now rewrite Hstep.
Qed.

Inductive Replay (State : Type) : Type :=
| Finished : list State -> Replay State
| Halted : nat -> LinearFailure -> list State -> Replay State.
Arguments Finished {State} _.
Arguments Halted {State} _ _ _.

(* Every recorded prefix includes the initial state; successful steps
   prepend their current state. Rejection records the offending index and
   the last *valid* state but never a fabricated failed successor. *)
Fixpoint replayFinite
  (commands : list LinearCommand) (initial : F.FiniteSnapshot)
  : Replay F.FiniteSnapshot :=
  match commands with
  | [] => Finished [initial]
  | command :: tail =>
      match finiteStep command initial with
      | FiniteStepError why => Halted 0 why [initial]
      | FiniteStepOk next =>
          match replayFinite tail next with
          | Finished trace => Finished (initial :: trace)
          | Halted index why trace =>
              Halted (S index) why (initial :: trace)
          end
      end
  end.

Fixpoint replayCore
  (commands : list LinearCommand) (initial : Context.ResourceContext)
  : Replay Context.ResourceContext :=
  match commands with
  | [] => Finished [initial]
  | command :: tail =>
      match coreStep command initial with
      | CoreStepError why => Halted 0 why [initial]
      | CoreStepOk next =>
          match replayCore tail next with
          | Finished trace => Finished (initial :: trace)
          | Halted index why trace =>
              Halted (S index) why (initial :: trace)
          end
      end
  end.

Definition prefixFinite
  (initial : F.FiniteSnapshot) (outcome : Replay F.FiniteSnapshot)
  : Replay F.FiniteSnapshot :=
  match outcome with
  | Finished trace => Finished (initial :: trace)
  | Halted index why trace =>
      Halted (S index) why (initial :: trace)
  end.

Definition prefixCore
  (initial : Context.ResourceContext) (outcome : Replay Context.ResourceContext)
  : Replay Context.ResourceContext :=
  match outcome with
  | Finished trace => Finished (initial :: trace)
  | Halted index why trace =>
      Halted (S index) why (initial :: trace)
  end.

Inductive ReplayRelated :
  Replay F.FiniteSnapshot -> Replay Context.ResourceContext -> Prop :=
| ReplayBothFinish : forall finiteTrace coreTrace,
    Forall2 F.ExactFiniteRelation finiteTrace coreTrace ->
    ReplayRelated (Finished finiteTrace) (Finished coreTrace)
| ReplayBothHalt : forall index why finiteTrace coreTrace,
    Forall2 F.ExactFiniteRelation finiteTrace coreTrace ->
    ReplayRelated
      (Halted index why finiteTrace)
      (Halted index why coreTrace).

Lemma corr5_prefix_preserves_related_replay :
  forall finiteInitial coreInitial finiteResult coreResult,
    F.ExactFiniteRelation finiteInitial coreInitial ->
    ReplayRelated finiteResult coreResult ->
    ReplayRelated
      (prefixFinite finiteInitial finiteResult)
      (prefixCore coreInitial coreResult).
Proof.
  intros fs cs fr cr Hinitial Hrun.
  destruct Hrun as [ft ct Htraces | n why ft ct Htraces];
    simpl; constructor; constructor; assumption.
Qed.

Theorem corr5_arbitrary_finite_trace_refines_core_model :
  forall commands finiteInitial coreInitial,
    F.ExactFiniteRelation finiteInitial coreInitial ->
    ReplayRelated
      (replayFinite commands finiteInitial)
      (replayCore commands coreInitial).
Proof.
  induction commands as [|command tail IH];
    intros finiteInitial coreInitial Hinitial.
  - simpl. constructor. constructor; [assumption|constructor].
  - simpl.
    pose proof
      (corr5_computed_step_preserves_exact_context
        finiteInitial coreInitial command Hinitial) as Hstep.
    destruct (finiteStep command finiteInitial) as [next | why]
      eqn:Hfinite; simpl in Hstep.
    + destruct Hstep as [coreNext [Hcore Hnext]].
      rewrite Hcore.
      apply corr5_prefix_preserves_related_replay.
      * exact Hinitial.
      * apply IH. exact Hnext.
    + rewrite Hstep.
      constructor. constructor; [assumption|constructor].
Qed.

Theorem corr5_first_failure_blocks_any_later_commands :
  forall prefix suffix initial index reason visited,
    replayFinite prefix initial = Halted index reason visited ->
    replayFinite (prefix ++ suffix) initial =
      Halted index reason visited.
Proof.
  induction prefix as [|command rest IH];
    intros suffix initial index reason visited Hfailure.
  - simpl in Hfailure. discriminate.
  - simpl in Hfailure.
    destruct (finiteStep command initial) as [next | why] eqn:Hstep.
    + destruct (replayFinite rest next) as [completed | failedIndex failedReason failedPrefix]
        eqn:Hrest; try discriminate.
      inversion Hfailure; subst index reason visited; clear Hfailure.
      simpl. rewrite Hstep.
      rewrite (IH suffix next failedIndex failedReason failedPrefix Hrest).
      reflexivity.
    + inversion Hfailure; subst index reason visited; clear Hfailure.
      simpl. now rewrite Hstep.
Qed.

Theorem corr5_failure_at_first_step_never_records_successor :
  forall command tail initial reason,
    finiteStep command initial = FiniteStepError reason ->
    replayFinite (command :: tail) initial =
      Halted 0 reason [initial].
Proof.
  intros command tail initial reason Hfailure.
  simpl. now rewrite Hfailure.
Qed.

Print Assumptions corr5_computed_step_preserves_exact_context.
Print Assumptions corr5_arbitrary_finite_trace_refines_core_model.
Print Assumptions corr5_first_failure_blocks_any_later_commands.
Print Assumptions corr5_failure_at_first_step_never_records_successor.
