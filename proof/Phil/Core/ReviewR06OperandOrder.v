From Stdlib Require Import Lists.List.

From Phil.Core Require Import SequentialExecutionOrder.

Import ListNotations.

(*
  PHIL-P1-REVIEW-R06 — optional using operands are evaluated before the later
  on operand for receive_exact and select.

  PHIL-EXEC-ORDER-001 already owns the general semantic rule: strict children
  execute left-to-right, and a stopping child suppresses every later child.
  R06 adds only the form-specific child plan used by Grammar-v1:

    receive_exact amount [using evidence] on endpoint
    select branch-arguments [using evidence] on endpoint

  The concrete mapping from GrammarV1ReceiveExactExpression and
  GrammarV1SelectExpression into these child plans remains an implementation
  correspondence boundary exercised by the permanent R06 regression.
*)

Definition continuingChild
  (trace : list SequentialExecutionOrder.ExecutionEvent)
  : SequentialExecutionOrder.LocalTraceResult :=
  SequentialExecutionOrder.mkLocalTraceResult
    trace SequentialExecutionOrder.LocalContinues.

Definition stoppingChild
  (trace : list SequentialExecutionOrder.ExecutionEvent)
  : SequentialExecutionOrder.LocalTraceResult :=
  SequentialExecutionOrder.mkLocalTraceResult
    trace SequentialExecutionOrder.LocalStops.

Definition receiveExactUsingChildren
  (amountTrace evidenceTrace endpointTrace :
    list SequentialExecutionOrder.ExecutionEvent)
  : list SequentialExecutionOrder.LocalTraceResult :=
  [ continuingChild amountTrace
  ; continuingChild evidenceTrace
  ; continuingChild endpointTrace
  ].

Definition receiveExactWithoutUsingChildren
  (amountTrace endpointTrace :
    list SequentialExecutionOrder.ExecutionEvent)
  : list SequentialExecutionOrder.LocalTraceResult :=
  [ continuingChild amountTrace
  ; continuingChild endpointTrace
  ].

Definition receiveExactTerminalUsingChildren
  (amountTrace evidenceTrace endpointTrace :
    list SequentialExecutionOrder.ExecutionEvent)
  : list SequentialExecutionOrder.LocalTraceResult :=
  [ continuingChild amountTrace
  ; stoppingChild evidenceTrace
  ; continuingChild endpointTrace
  ].

(*
  For select, payloadSummaryTrace is the already source-ordered trace of the
  branch-argument prefix.  PHIL-EXEC-ORDER-001 owns ordering inside that prefix;
  R06 certifies where the optional boundary/evidence operand sits relative to
  that prefix and the endpoint.
*)
Definition selectUsingChildren
  (payloadSummaryTrace boundaryTrace endpointTrace :
    list SequentialExecutionOrder.ExecutionEvent)
  : list SequentialExecutionOrder.LocalTraceResult :=
  [ continuingChild payloadSummaryTrace
  ; continuingChild boundaryTrace
  ; continuingChild endpointTrace
  ].

Definition selectWithoutUsingChildren
  (payloadSummaryTrace endpointTrace :
    list SequentialExecutionOrder.ExecutionEvent)
  : list SequentialExecutionOrder.LocalTraceResult :=
  [ continuingChild payloadSummaryTrace
  ; continuingChild endpointTrace
  ].

Definition selectTerminalUsingChildren
  (payloadSummaryTrace boundaryTrace endpointTrace :
    list SequentialExecutionOrder.ExecutionEvent)
  : list SequentialExecutionOrder.LocalTraceResult :=
  [ continuingChild payloadSummaryTrace
  ; stoppingChild boundaryTrace
  ; continuingChild endpointTrace
  ].

Theorem review_r06_receive_exact_using_is_amount_then_evidence_then_endpoint :
  forall amountTrace evidenceTrace endpointTrace,
    SequentialExecutionOrder.evaluateStrictChildren
      (receiveExactUsingChildren amountTrace evidenceTrace endpointTrace) =
    SequentialExecutionOrder.mkLocalTraceResult
      (amountTrace ++ evidenceTrace ++ endpointTrace)
      SequentialExecutionOrder.LocalContinues.
Proof.
  intros amountTrace evidenceTrace endpointTrace.
  unfold receiveExactUsingChildren, continuingChild,
    SequentialExecutionOrder.evaluateStrictChildren.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Theorem review_r06_receive_exact_without_using_is_amount_then_endpoint :
  forall amountTrace endpointTrace,
    SequentialExecutionOrder.evaluateStrictChildren
      (receiveExactWithoutUsingChildren amountTrace endpointTrace) =
    SequentialExecutionOrder.mkLocalTraceResult
      (amountTrace ++ endpointTrace)
      SequentialExecutionOrder.LocalContinues.
Proof.
  intros amountTrace endpointTrace.
  unfold receiveExactWithoutUsingChildren, continuingChild,
    SequentialExecutionOrder.evaluateStrictChildren.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Theorem review_r06_terminal_receive_exact_using_suppresses_endpoint :
  forall amountTrace evidenceTrace endpointTrace,
    SequentialExecutionOrder.evaluateStrictChildren
      (receiveExactTerminalUsingChildren
        amountTrace evidenceTrace endpointTrace) =
    SequentialExecutionOrder.mkLocalTraceResult
      (amountTrace ++ evidenceTrace)
      SequentialExecutionOrder.LocalStops.
Proof.
  intros amountTrace evidenceTrace endpointTrace.
  unfold receiveExactTerminalUsingChildren, continuingChild, stoppingChild,
    SequentialExecutionOrder.evaluateStrictChildren.
  reflexivity.
Qed.

Theorem review_r06_select_using_is_payload_then_boundary_then_endpoint :
  forall payloadSummaryTrace boundaryTrace endpointTrace,
    SequentialExecutionOrder.evaluateStrictChildren
      (selectUsingChildren
        payloadSummaryTrace boundaryTrace endpointTrace) =
    SequentialExecutionOrder.mkLocalTraceResult
      (payloadSummaryTrace ++ boundaryTrace ++ endpointTrace)
      SequentialExecutionOrder.LocalContinues.
Proof.
  intros payloadSummaryTrace boundaryTrace endpointTrace.
  unfold selectUsingChildren, continuingChild,
    SequentialExecutionOrder.evaluateStrictChildren.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Theorem review_r06_select_without_using_is_payload_then_endpoint :
  forall payloadSummaryTrace endpointTrace,
    SequentialExecutionOrder.evaluateStrictChildren
      (selectWithoutUsingChildren payloadSummaryTrace endpointTrace) =
    SequentialExecutionOrder.mkLocalTraceResult
      (payloadSummaryTrace ++ endpointTrace)
      SequentialExecutionOrder.LocalContinues.
Proof.
  intros payloadSummaryTrace endpointTrace.
  unfold selectWithoutUsingChildren, continuingChild,
    SequentialExecutionOrder.evaluateStrictChildren.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Theorem review_r06_terminal_select_using_suppresses_endpoint :
  forall payloadSummaryTrace boundaryTrace endpointTrace,
    SequentialExecutionOrder.evaluateStrictChildren
      (selectTerminalUsingChildren
        payloadSummaryTrace boundaryTrace endpointTrace) =
    SequentialExecutionOrder.mkLocalTraceResult
      (payloadSummaryTrace ++ boundaryTrace)
      SequentialExecutionOrder.LocalStops.
Proof.
  intros payloadSummaryTrace boundaryTrace endpointTrace.
  unfold selectTerminalUsingChildren, continuingChild, stoppingChild,
    SequentialExecutionOrder.evaluateStrictChildren.
  reflexivity.
Qed.

Theorem review_r06_is_an_instance_of_strict_child_stop_authority :
  forall prefixTrace usingTrace endpointTrace,
    SequentialExecutionOrder.evaluateStrictChildren
      [ continuingChild prefixTrace
      ; stoppingChild usingTrace
      ; continuingChild endpointTrace
      ] =
    SequentialExecutionOrder.mkLocalTraceResult
      (prefixTrace ++ usingTrace)
      SequentialExecutionOrder.LocalStops.
Proof.
  intros prefixTrace usingTrace endpointTrace.
  unfold continuingChild, stoppingChild,
    SequentialExecutionOrder.evaluateStrictChildren.
  reflexivity.
Qed.
