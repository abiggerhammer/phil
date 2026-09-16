From Stdlib Require Import Bool.Bool.
From Phil.Core Require Import UTF8.

(*
  PHIL-P1-IO-CODEC-001 — executable implementation correspondence.

  Production first executes the already-certified predecessor provider call.
  Only after that predecessor succeeds does the codec layer classify the result.
  This file owns that finite ordering surface; concrete Text/ByteString codec
  facts and the predecessor provider implementations remain explicit boundaries.
*)

Inductive UTF8ReadDecision : Type :=
| UTF8ReadPredecessorRejected
| UTF8ReadDecoded
| UTF8ReadDecodeFailed
| UTF8ReadProviderFailed.

Definition decideReadUTF8ByFacts
  (predecessorAccepted providerSucceeded decodeSucceeded : bool)
  : UTF8ReadDecision :=
  if predecessorAccepted then
    if providerSucceeded then
      if decodeSucceeded then UTF8ReadDecoded
      else UTF8ReadDecodeFailed
    else UTF8ReadProviderFailed
  else UTF8ReadPredecessorRejected.

Inductive UTF8CompositionDecision : Type :=
| UTF8CompositionPredecessorRejected
| UTF8CompositionAccepted.

Definition decideWriteUTF8ByFacts
  (predecessorAccepted : bool) : UTF8CompositionDecision :=
  if predecessorAccepted then UTF8CompositionAccepted
  else UTF8CompositionPredecessorRejected.

Definition decideWriteLineByFacts
  (predecessorAccepted : bool) : UTF8CompositionDecision :=
  if predecessorAccepted then UTF8CompositionAccepted
  else UTF8CompositionPredecessorRejected.

Theorem read_utf8_predecessor_rejection_blocks_codec_classification :
  forall providerSucceeded decodeSucceeded,
    decideReadUTF8ByFacts false providerSucceeded decodeSucceeded =
      UTF8ReadPredecessorRejected.
Proof. reflexivity. Qed.

Theorem read_utf8_provider_failure_bypasses_decode :
  forall decodeSucceeded,
    decideReadUTF8ByFacts true false decodeSucceeded =
      UTF8ReadProviderFailed.
Proof. reflexivity. Qed.

Theorem read_utf8_successful_valid_decode_accepts_exact_text :
  decideReadUTF8ByFacts true true true = UTF8ReadDecoded.
Proof. reflexivity. Qed.

Theorem read_utf8_successful_invalid_decode_is_explicit_failure :
  decideReadUTF8ByFacts true true false = UTF8ReadDecodeFailed.
Proof. reflexivity. Qed.

Theorem write_utf8_requires_accepted_filesystem_replace :
  decideWriteUTF8ByFacts false = UTF8CompositionPredecessorRejected /\
  decideWriteUTF8ByFacts true = UTF8CompositionAccepted.
Proof. split; reflexivity. Qed.

Theorem write_line_requires_accepted_console_write :
  decideWriteLineByFacts false = UTF8CompositionPredecessorRejected /\
  decideWriteLineByFacts true = UTF8CompositionAccepted.
Proof. split; reflexivity. Qed.

Theorem read_utf8_has_no_branch_that_reclassifies_provider_failure_as_decode_failure :
  forall decodeSucceeded,
    decideReadUTF8ByFacts true false decodeSucceeded <>
      UTF8ReadDecodeFailed.
Proof.
  intros decodeSucceeded.
  destruct decodeSucceeded; discriminate.
Qed.

Theorem convenience_writes_introduce_no_post_predecessor_rejection :
  decideWriteUTF8ByFacts true = UTF8CompositionAccepted /\
  decideWriteLineByFacts true = UTF8CompositionAccepted.
Proof. split; reflexivity. Qed.
