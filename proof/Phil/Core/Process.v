From Coq Require Import Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax.

(*
  Proof-oriented model of Phil.Core.Process.sequenceFlow.

  CheckState is opaque here: the sequencing theorem depends only on the Control
  discriminator. FlowResult retains the implementation's Either-style failure
  behavior, so the preservation theorem is conditional on successful sequencing.
*)

Parameter CheckState : Type.

Record FlowPath : Type := mkFlowPath
  { pathControl : Control
  ; pathState : CheckState
  }.

Definition ProcessFlow := list FlowPath.

Inductive FlowResult (E : Type) : Type :=
| FlowOk : ProcessFlow -> FlowResult E
| FlowError : E -> FlowResult E.

Arguments FlowOk {E} _.
Arguments FlowError {E} _.

Definition advance {E : Type}
  (continuation : CheckState -> FlowResult E)
  (path : FlowPath) : FlowResult E :=
  match pathControl path with
  | Continue => continuation (pathState path)
  | Return _ => FlowOk [path]
  | Closed _ => FlowOk [path]
  | Failed _ _ => FlowOk [path]
  end.

Fixpoint sequenceFlow {E : Type}
  (flow : ProcessFlow)
  (continuation : CheckState -> FlowResult E) : FlowResult E :=
  match flow with
  | [] => FlowOk []
  | path :: rest =>
      match advance continuation path with
      | FlowError err => FlowError err
      | FlowOk advanced =>
          match sequenceFlow rest continuation with
          | FlowError err => FlowError err
          | FlowOk advancedRest => FlowOk (advanced ++ advancedRest)
          end
      end
  end.

(* PHIL-PROC-SEQ-001: Continue is exactly the case delegated onward. *)
Theorem advance_continue_uses_continuation :
  forall (E : Type)
         (continuation : CheckState -> FlowResult E)
         (state : CheckState),
    advance continuation (mkFlowPath Continue state) = continuation state.
Proof.
  reflexivity.
Qed.

(* PHIL-PROC-SEQ-001: terminal/control-transfer paths are not delegated. *)
Theorem advance_noncontinuing_preserved :
  forall (E : Type)
         (continuation : CheckState -> FlowResult E)
         (path : FlowPath),
    pathControl path <> Continue ->
    advance continuation path = FlowOk [path].
Proof.
  intros E continuation path Hnoncontinuing.
  destruct path as [control state].
  simpl in Hnoncontinuing.
  destruct control; simpl.
  - exfalso. apply Hnoncontinuing. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(*
  PHIL-PROC-SEQ-001.

  If sequencing succeeds, every non-Continue input path occurs unchanged in the
  output. Thus Return, Closed, and Failed paths survive sequencing exactly; only
  Continue paths can be replaced by continuation output.
*)
Theorem sequenceFlow_preserves_noncontinuing :
  forall (E : Type)
         (flow output : ProcessFlow)
         (continuation : CheckState -> FlowResult E)
         (path : FlowPath),
    sequenceFlow flow continuation = FlowOk output ->
    In path flow ->
    pathControl path <> Continue ->
    In path output.
Proof.
  intros E flow.
  induction flow as [| head tail IH].
  - intros output continuation path Hsequence Hin Hnoncontinuing.
    inversion Hin.
  - intros output continuation path Hsequence Hin Hnoncontinuing.
    simpl in Hsequence.
    destruct (advance continuation head) as [advanced | err] eqn:Hadvance.
    + destruct (sequenceFlow tail continuation) as [restOutput | restErr] eqn:Hrest.
      * inversion Hsequence; subst output; clear Hsequence.
        simpl in Hin.
        destruct Hin as [Heq | Hintail].
        -- subst head.
           pose proof
             (advance_noncontinuing_preserved E continuation path Hnoncontinuing)
             as Hpreserved.
           rewrite Hpreserved in Hadvance.
           inversion Hadvance; subst advanced.
           simpl. left. reflexivity.
        -- apply in_or_app. right.
           eapply IH; eauto.
      * discriminate.
    + discriminate.
Qed.
