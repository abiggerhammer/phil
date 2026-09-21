From Stdlib Require Import Bool.Bool.
From Phil.Core Require Import Console.

(*
  PHIL-P1-IO-CONSOLE-001 — executable implementation correspondence.

  Concrete Text equality/length, authority checker results, provider interface
  strings, diagnostics, and accepted Haskell values stay native. This file owns
  only the finite ordered decisions reflected by Phil.IO.Console.
*)

Inductive ConsoleOccurrenceDecision : Type :=
| ConsoleOccurrenceAccepted
| ConsoleOccurrenceEmpty.

Definition decideConsoleOccurrenceByFacts
  (occurrenceEmpty : bool) : ConsoleOccurrenceDecision :=
  if occurrenceEmpty then ConsoleOccurrenceEmpty
  else ConsoleOccurrenceAccepted.

Inductive ConsoleOperationDecision : Type :=
| ConsoleOperationAccepted
| ConsoleOperationKindMismatch.

Definition decideConsoleOperationByFacts
  (kindAllowsOperation : bool) : ConsoleOperationDecision :=
  if kindAllowsOperation then ConsoleOperationAccepted
  else ConsoleOperationKindMismatch.

Inductive ConsoleObservedReadKind : Type :=
| ObservedConsoleLine
| ObservedConsoleEndOfInput
| ObservedConsoleReadFailure.

Inductive ConsoleReadDecision : Type :=
| ConsoleReadAccepted
| ConsoleReadOperationKindMismatch
| ConsoleReadAuthorityRejected
| ConsoleReadLineExceedsLimit.

Definition decideConsoleReadByFacts
  (kindAllowsRead authorityAccepted : bool)
  (observedKind : ConsoleObservedReadKind)
  (lineWithinLimit : bool) : ConsoleReadDecision :=
  if kindAllowsRead then
    if authorityAccepted then
      match observedKind with
      | ObservedConsoleLine =>
          if lineWithinLimit then ConsoleReadAccepted
          else ConsoleReadLineExceedsLimit
      | ObservedConsoleEndOfInput => ConsoleReadAccepted
      | ObservedConsoleReadFailure => ConsoleReadAccepted
      end
    else ConsoleReadAuthorityRejected
  else ConsoleReadOperationKindMismatch.

Inductive ConsoleWriteDecision : Type :=
| ConsoleWriteAccepted
| ConsoleWriteOperationKindMismatch
| ConsoleWriteAuthorityRejected
| ConsoleWriteProgressOutOfRange.

Definition decideConsoleWriteByFacts
  (kindAllowsWrite authorityAccepted observedSuccess progressWithinRequest : bool)
  : ConsoleWriteDecision :=
  if kindAllowsWrite then
    if authorityAccepted then
      if observedSuccess then ConsoleWriteAccepted
      else if progressWithinRequest then ConsoleWriteAccepted
      else ConsoleWriteProgressOutOfRange
    else ConsoleWriteAuthorityRejected
  else ConsoleWriteOperationKindMismatch.

Definition consoleWriteUsesFullRequested
  (observedSuccess : bool) : bool := observedSuccess.

Inductive ConsoleFlushDecision : Type :=
| ConsoleFlushAccepted
| ConsoleFlushOperationKindMismatch
| ConsoleFlushAuthorityRejected.

Definition decideConsoleFlushByFacts
  (kindAllowsFlush authorityAccepted : bool) : ConsoleFlushDecision :=
  if kindAllowsFlush then
    if authorityAccepted then ConsoleFlushAccepted
    else ConsoleFlushAuthorityRejected
  else ConsoleFlushOperationKindMismatch.

Theorem empty_console_occurrence_rejects :
  decideConsoleOccurrenceByFacts true = ConsoleOccurrenceEmpty.
Proof. reflexivity. Qed.

Theorem nonempty_console_occurrence_accepts :
  decideConsoleOccurrenceByFacts false = ConsoleOccurrenceAccepted.
Proof. reflexivity. Qed.

Theorem illegal_console_operation_rejects :
  decideConsoleOperationByFacts false = ConsoleOperationKindMismatch.
Proof. reflexivity. Qed.

Theorem legal_console_operation_accepts :
  decideConsoleOperationByFacts true = ConsoleOperationAccepted.
Proof. reflexivity. Qed.

Theorem read_kind_mismatch_rejects_before_authority_or_outcome :
  forall authorityAccepted observedKind lineWithinLimit,
    decideConsoleReadByFacts false authorityAccepted observedKind lineWithinLimit =
      ConsoleReadOperationKindMismatch.
Proof. reflexivity. Qed.

Theorem rejected_read_authority_blocks_outcome_validation :
  forall observedKind lineWithinLimit,
    decideConsoleReadByFacts true false observedKind lineWithinLimit =
      ConsoleReadAuthorityRejected.
Proof. reflexivity. Qed.

Theorem overbound_line_rejects :
  decideConsoleReadByFacts true true ObservedConsoleLine false =
    ConsoleReadLineExceedsLimit.
Proof. reflexivity. Qed.

Theorem bounded_line_accepts :
  decideConsoleReadByFacts true true ObservedConsoleLine true =
    ConsoleReadAccepted.
Proof. reflexivity. Qed.

Theorem eof_accepts_after_preconditions :
  forall lineWithinLimit,
    decideConsoleReadByFacts true true ObservedConsoleEndOfInput lineWithinLimit =
      ConsoleReadAccepted.
Proof. reflexivity. Qed.

Theorem portable_read_failure_accepts_after_preconditions :
  forall lineWithinLimit,
    decideConsoleReadByFacts true true ObservedConsoleReadFailure lineWithinLimit =
      ConsoleReadAccepted.
Proof. reflexivity. Qed.

Theorem write_kind_mismatch_rejects_first :
  forall authorityAccepted observedSuccess progressWithinRequest,
    decideConsoleWriteByFacts
      false authorityAccepted observedSuccess progressWithinRequest =
      ConsoleWriteOperationKindMismatch.
Proof. reflexivity. Qed.

Theorem rejected_write_authority_blocks_progress_validation :
  forall observedSuccess progressWithinRequest,
    decideConsoleWriteByFacts true false observedSuccess progressWithinRequest =
      ConsoleWriteAuthorityRejected.
Proof. reflexivity. Qed.

Theorem successful_write_accepts_without_prefix_fact :
  forall progressWithinRequest,
    decideConsoleWriteByFacts true true true progressWithinRequest =
      ConsoleWriteAccepted.
Proof. reflexivity. Qed.

Theorem failed_write_accepts_exactly_in_range_progress :
  decideConsoleWriteByFacts true true false true = ConsoleWriteAccepted /\
  decideConsoleWriteByFacts true true false false =
    ConsoleWriteProgressOutOfRange.
Proof. split; reflexivity. Qed.

Theorem successful_write_selects_full_request :
  consoleWriteUsesFullRequested true = true.
Proof. reflexivity. Qed.

Theorem failed_write_selects_reported_prefix :
  consoleWriteUsesFullRequested false = false.
Proof. reflexivity. Qed.

Theorem flush_kind_mismatch_rejects_first :
  forall authorityAccepted,
    decideConsoleFlushByFacts false authorityAccepted =
      ConsoleFlushOperationKindMismatch.
Proof. reflexivity. Qed.

Theorem rejected_flush_authority_rejects_second :
  decideConsoleFlushByFacts true false = ConsoleFlushAuthorityRejected.
Proof. reflexivity. Qed.

Theorem authorized_output_flush_accepts :
  decideConsoleFlushByFacts true true = ConsoleFlushAccepted.
Proof. reflexivity. Qed.

Theorem console_occurrence_accepts_iff_nonempty_fact :
  forall occurrenceEmpty,
    decideConsoleOccurrenceByFacts occurrenceEmpty =
      ConsoleOccurrenceAccepted <->
    occurrenceEmpty = false.
Proof.
  intros occurrenceEmpty.
  destruct occurrenceEmpty; cbn; split; intro H; try discriminate; reflexivity.
Qed.

Theorem console_operation_accepts_iff_allowed_fact :
  forall kindAllowsOperation,
    decideConsoleOperationByFacts kindAllowsOperation =
      ConsoleOperationAccepted <->
    kindAllowsOperation = true.
Proof.
  intros kindAllowsOperation.
  destruct kindAllowsOperation; cbn; split; intro H; try discriminate; reflexivity.
Qed.

Theorem console_read_accepts_iff_ordered_facts :
  forall kindAllowsRead authorityAccepted observedKind lineWithinLimit,
    decideConsoleReadByFacts
      kindAllowsRead authorityAccepted observedKind lineWithinLimit =
      ConsoleReadAccepted <->
    kindAllowsRead = true /\
    authorityAccepted = true /\
    match observedKind with
    | ObservedConsoleLine => lineWithinLimit = true
    | ObservedConsoleEndOfInput => True
    | ObservedConsoleReadFailure => True
    end.
Proof.
  intros kindAllowsRead authorityAccepted observedKind lineWithinLimit.
  destruct kindAllowsRead, authorityAccepted, observedKind, lineWithinLimit;
    cbn; intuition discriminate.
Qed.

Theorem console_write_accepts_iff_ordered_facts :
  forall kindAllowsWrite authorityAccepted observedSuccess progressWithinRequest,
    decideConsoleWriteByFacts
      kindAllowsWrite authorityAccepted observedSuccess progressWithinRequest =
      ConsoleWriteAccepted <->
    kindAllowsWrite = true /\
    authorityAccepted = true /\
    (observedSuccess = true \/ progressWithinRequest = true).
Proof.
  intros kindAllowsWrite authorityAccepted observedSuccess progressWithinRequest.
  destruct kindAllowsWrite, authorityAccepted, observedSuccess,
           progressWithinRequest;
    cbn; intuition discriminate.
Qed.

Theorem console_flush_accepts_iff_ordered_facts :
  forall kindAllowsFlush authorityAccepted,
    decideConsoleFlushByFacts kindAllowsFlush authorityAccepted =
      ConsoleFlushAccepted <->
    kindAllowsFlush = true /\ authorityAccepted = true.
Proof.
  intros kindAllowsFlush authorityAccepted.
  destruct kindAllowsFlush, authorityAccepted;
    cbn; intuition discriminate.
Qed.
