From Stdlib Require Import Arith.Arith Bool.Bool Lists.List.
From Phil.Core Require Import GenericStructural.

(*
  PHIL-P1-IO-CONSOLE-001 — explicit console-provider semantics.

  This proof owns the normalized semantic facts for exact console occurrence
  identity, legal operation/kind pairs, default structural authority modes,
  bounded line reads, exact observable write-prefix progress, and flush output
  semantics. Authority possession/effect permission themselves remain imported
  predecessor boundaries.
*)

Definition ConsoleOccurrenceKey : Type := nat.

Inductive ConsoleProviderKind : Type :=
| ConsoleInputProvider
| ConsoleOutputProvider.

Record SemanticConsoleOccurrence : Type := mkSemanticConsoleOccurrence {
  semanticConsoleOccurrenceKey : ConsoleOccurrenceKey;
  semanticConsoleProviderKind : ConsoleProviderKind
}.

Inductive ConsoleOperation : Type :=
| ConsoleReadLineOp
| ConsoleWriteOp
| ConsoleFlushOp.

Definition consoleOperationAllowedForKind
  (kind : ConsoleProviderKind)
  (operation : ConsoleOperation) : bool :=
  match kind, operation with
  | ConsoleInputProvider, ConsoleReadLineOp => true
  | ConsoleOutputProvider, ConsoleWriteOp => true
  | ConsoleOutputProvider, ConsoleFlushOp => true
  | _, _ => false
  end.

Definition defaultConsoleAuthorityMode
  (kind : ConsoleProviderKind) : Mode :=
  match kind with
  | ConsoleInputProvider => Linear
  | ConsoleOutputProvider => Affine
  end.

Theorem stdin_default_authority_is_linear :
  defaultConsoleAuthorityMode ConsoleInputProvider = Linear.
Proof. reflexivity. Qed.

Theorem output_default_authority_is_affine :
  defaultConsoleAuthorityMode ConsoleOutputProvider = Affine.
Proof. reflexivity. Qed.

Theorem input_allows_only_read_line :
  consoleOperationAllowedForKind ConsoleInputProvider ConsoleReadLineOp = true /\
  consoleOperationAllowedForKind ConsoleInputProvider ConsoleWriteOp = false /\
  consoleOperationAllowedForKind ConsoleInputProvider ConsoleFlushOp = false.
Proof. repeat split; reflexivity. Qed.

Theorem output_allows_write_and_flush_only :
  consoleOperationAllowedForKind ConsoleOutputProvider ConsoleReadLineOp = false /\
  consoleOperationAllowedForKind ConsoleOutputProvider ConsoleWriteOp = true /\
  consoleOperationAllowedForKind ConsoleOutputProvider ConsoleFlushOp = true.
Proof. repeat split; reflexivity. Qed.

Theorem distinct_console_occurrence_keys_do_not_collapse :
  forall leftKey rightKey kind,
    leftKey <> rightKey ->
    mkSemanticConsoleOccurrence leftKey kind <>
      mkSemanticConsoleOccurrence rightKey kind.
Proof.
  intros leftKey rightKey kind Hneq Heq.
  inversion Heq.
  contradiction.
Qed.

Theorem input_and_output_occurrences_do_not_collapse :
  forall key,
    mkSemanticConsoleOccurrence key ConsoleInputProvider <>
      mkSemanticConsoleOccurrence key ConsoleOutputProvider.
Proof.
  intros key Heq.
  inversion Heq.
Qed.

Inductive SemanticConsoleReadOutcome : Type :=
| SemanticConsoleLine (lineLength : nat)
| SemanticConsoleEndOfInput
| SemanticConsoleReadFailure.

Inductive CheckedConsoleRead
  : SemanticConsoleOccurrence -> nat -> SemanticConsoleReadOutcome -> Prop :=
| CheckedConsoleLineAccepted :
    forall occurrence limit lineLength,
      semanticConsoleProviderKind occurrence = ConsoleInputProvider ->
      lineLength <= limit ->
      CheckedConsoleRead occurrence limit (SemanticConsoleLine lineLength)
| CheckedConsoleEndOfInputAccepted :
    forall occurrence limit,
      semanticConsoleProviderKind occurrence = ConsoleInputProvider ->
      CheckedConsoleRead occurrence limit SemanticConsoleEndOfInput
| CheckedConsoleReadFailureAccepted :
    forall occurrence limit,
      semanticConsoleProviderKind occurrence = ConsoleInputProvider ->
      CheckedConsoleRead occurrence limit SemanticConsoleReadFailure.

Theorem checked_console_line_is_bounded :
  forall occurrence limit lineLength,
    CheckedConsoleRead occurrence limit (SemanticConsoleLine lineLength) ->
    lineLength <= limit.
Proof.
  intros occurrence limit lineLength Hchecked.
  inversion Hchecked.
  assumption.
Qed.

Theorem checked_console_read_is_input_only :
  forall occurrence limit outcome,
    CheckedConsoleRead occurrence limit outcome ->
    semanticConsoleProviderKind occurrence = ConsoleInputProvider.
Proof.
  intros occurrence limit outcome Hchecked.
  inversion Hchecked; assumption.
Qed.

Inductive SemanticConsoleWriteOutcome : Type :=
| SemanticConsoleWriteSucceeded
| SemanticConsoleWriteFailed (observablePrefixLength : nat).

Inductive CheckedConsoleWrite
  : SemanticConsoleOccurrence -> nat -> SemanticConsoleWriteOutcome -> nat -> Prop :=
| CheckedConsoleWriteSuccess :
    forall occurrence requestedLength,
      semanticConsoleProviderKind occurrence = ConsoleOutputProvider ->
      CheckedConsoleWrite
        occurrence requestedLength SemanticConsoleWriteSucceeded requestedLength
| CheckedConsoleWriteFailure :
    forall occurrence requestedLength prefixLength,
      semanticConsoleProviderKind occurrence = ConsoleOutputProvider ->
      prefixLength <= requestedLength ->
      CheckedConsoleWrite
        occurrence requestedLength
        (SemanticConsoleWriteFailed prefixLength)
        prefixLength.

Theorem successful_console_write_observes_full_request :
  forall occurrence requestedLength observableLength,
    CheckedConsoleWrite
      occurrence requestedLength SemanticConsoleWriteSucceeded observableLength ->
    observableLength = requestedLength.
Proof.
  intros occurrence requestedLength observableLength Hchecked.
  inversion Hchecked.
  reflexivity.
Qed.

Theorem failed_console_write_preserves_exact_prefix_progress :
  forall occurrence requestedLength prefixLength observableLength,
    CheckedConsoleWrite
      occurrence requestedLength
      (SemanticConsoleWriteFailed prefixLength)
      observableLength ->
    observableLength = prefixLength /\ prefixLength <= requestedLength.
Proof.
  intros occurrence requestedLength prefixLength observableLength Hchecked.
  inversion Hchecked.
  split.
  - reflexivity.
  - assumption.
Qed.

Theorem checked_console_write_is_output_only :
  forall occurrence requestedLength outcome observableLength,
    CheckedConsoleWrite occurrence requestedLength outcome observableLength ->
    semanticConsoleProviderKind occurrence = ConsoleOutputProvider.
Proof.
  intros occurrence requestedLength outcome observableLength Hchecked.
  inversion Hchecked; assumption.
Qed.

Inductive SemanticConsoleFlushOutcome : Type :=
| SemanticConsoleFlushSucceeded
| SemanticConsoleFlushFailed.

Inductive CheckedConsoleFlush
  : SemanticConsoleOccurrence -> SemanticConsoleFlushOutcome -> Prop :=
| CheckedConsoleFlushAccepted :
    forall occurrence outcome,
      semanticConsoleProviderKind occurrence = ConsoleOutputProvider ->
      CheckedConsoleFlush occurrence outcome.

Theorem checked_console_flush_is_output_only :
  forall occurrence outcome,
    CheckedConsoleFlush occurrence outcome ->
    semanticConsoleProviderKind occurrence = ConsoleOutputProvider.
Proof.
  intros occurrence outcome Hchecked.
  inversion Hchecked.
  assumption.
Qed.
