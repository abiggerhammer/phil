From Stdlib Require Import Arith.Arith Lists.List.
From Phil.Core Require Import ProviderRelativePath RuntimeBytes FileSystem Console.

Import ListNotations.

(*
  PHIL-P1-IO-CODEC-001 — explicit UTF-8 codec and convenience composition.

  This proof owns Phil's semantic contract for the explicit text/bytes boundary
  and for ordinary composition with the already-certified FileSystem and Console
  operations.  It deliberately does not claim to verify the implementation of
  Data.Text.Encoding itself.  A QualifiedUTF8Codec is the competent
  representation/realization boundary: it must establish exact round-trip and
  non-normalizing injectivity for Phil semantic scalar sequences.
*)

Definition SemanticTextValue : Type := list nat.

Definition lineFeedScalar : nat := 10.

Definition appendLineFeed (text : SemanticTextValue) : SemanticTextValue :=
  text ++ [lineFeedScalar].

Record QualifiedUTF8Codec : Type := mkQualifiedUTF8Codec {
  semanticUTF8Encode : SemanticTextValue -> SemanticBytesValue;
  semanticUTF8Decode : SemanticBytesValue -> option SemanticTextValue;
  semanticUTF8RoundTripExact :
    forall text,
      semanticUTF8Decode (semanticUTF8Encode text) = Some text;
  semanticUTF8EncodeInjective :
    forall left right,
      semanticUTF8Encode left = semanticUTF8Encode right ->
      left = right
}.

Theorem qualified_utf8_round_trip_is_exact :
  forall codec text,
    semanticUTF8Decode codec (semanticUTF8Encode codec text) = Some text.
Proof.
  intros codec text.
  apply semanticUTF8RoundTripExact.
Qed.

Theorem qualified_utf8_does_not_normalize_distinct_scalar_sequences :
  forall codec left right,
    left <> right ->
    semanticUTF8Encode codec left <> semanticUTF8Encode codec right.
Proof.
  intros codec left right Hdistinct Hequal.
  apply Hdistinct.
  eapply semanticUTF8EncodeInjective.
  exact Hequal.
Qed.

Theorem encoded_utf8_is_runtime_bytes :
  forall codec text,
    BytesValueHasType (semanticUTF8Encode codec text) RuntimeBytesIndex.
Proof.
  intros codec text.
  apply runtime_bytes_carries_no_exact_length_requirement.
Qed.

Inductive SemanticReadUTF8Outcome : Type :=
| SemanticReadUTF8Decoded (text : SemanticTextValue)
| SemanticReadUTF8DecodeFailed
| SemanticReadUTF8ProviderFailed (failure : SemanticFileSystemFailure).

Inductive CheckedSemanticReadUTF8
  (codec : QualifiedUTF8Codec)
  (occurrence : ProviderIdentity)
  (path : SemanticProviderRelativePath)
  (limit : nat)
  (prior : SemanticFileSystemState)
  : SemanticFileReadOutcome -> SemanticFileSystemState ->
    SemanticReadUTF8Outcome -> Prop :=
| CheckedSemanticReadUTF8Decoded :
    forall next bytes text,
      CheckedSemanticFileSystemRead
        occurrence path limit prior
        (SemanticFileReadSucceeded bytes) next ->
      semanticUTF8Decode codec bytes = Some text ->
      CheckedSemanticReadUTF8
        codec occurrence path limit prior
        (SemanticFileReadSucceeded bytes) next
        (SemanticReadUTF8Decoded text)
| CheckedSemanticReadUTF8DecodeFailed :
    forall next bytes,
      CheckedSemanticFileSystemRead
        occurrence path limit prior
        (SemanticFileReadSucceeded bytes) next ->
      semanticUTF8Decode codec bytes = None ->
      CheckedSemanticReadUTF8
        codec occurrence path limit prior
        (SemanticFileReadSucceeded bytes) next
        SemanticReadUTF8DecodeFailed
| CheckedSemanticReadUTF8ProviderFailed :
    forall next failure,
      CheckedSemanticFileSystemRead
        occurrence path limit prior
        (SemanticFileReadFailed failure) next ->
      CheckedSemanticReadUTF8
        codec occurrence path limit prior
        (SemanticFileReadFailed failure) next
        (SemanticReadUTF8ProviderFailed failure).

Theorem checked_read_utf8_retains_exact_filesystem_read :
  forall codec occurrence path limit prior fileOutcome next codecOutcome,
    CheckedSemanticReadUTF8
      codec occurrence path limit prior fileOutcome next codecOutcome ->
    CheckedSemanticFileSystemRead
      occurrence path limit prior fileOutcome next.
Proof.
  intros codec occurrence path limit prior fileOutcome next codecOutcome Hchecked.
  inversion Hchecked; subst; assumption.
Qed.

Theorem checked_read_utf8_preserves_filesystem_state :
  forall codec occurrence path limit prior fileOutcome next codecOutcome,
    CheckedSemanticReadUTF8
      codec occurrence path limit prior fileOutcome next codecOutcome ->
    next = prior.
Proof.
  intros codec occurrence path limit prior fileOutcome next codecOutcome Hchecked.
  eapply checked_read_preserves_semantic_state.
  eapply checked_read_utf8_retains_exact_filesystem_read.
  exact Hchecked.
Qed.

Theorem read_utf8_preserves_provider_failure_exactly :
  forall codec occurrence path limit prior failure next codecOutcome,
    CheckedSemanticReadUTF8
      codec occurrence path limit prior
      (SemanticFileReadFailed failure) next codecOutcome ->
    codecOutcome = SemanticReadUTF8ProviderFailed failure.
Proof.
  intros codec occurrence path limit prior failure next codecOutcome Hchecked.
  inversion Hchecked; reflexivity.
Qed.

Theorem read_utf8_successful_invalid_decode_is_explicit :
  forall codec occurrence path limit prior bytes next codecOutcome,
    CheckedSemanticReadUTF8
      codec occurrence path limit prior
      (SemanticFileReadSucceeded bytes) next codecOutcome ->
    semanticUTF8Decode codec bytes = None ->
    codecOutcome = SemanticReadUTF8DecodeFailed.
Proof.
  intros codec occurrence path limit prior bytes next codecOutcome Hchecked Hinvalid.
  inversion Hchecked; subst; try reflexivity; congruence.
Qed.

Theorem read_utf8_successful_decode_preserves_exact_text :
  forall codec occurrence path limit prior bytes next text codecOutcome,
    CheckedSemanticReadUTF8
      codec occurrence path limit prior
      (SemanticFileReadSucceeded bytes) next codecOutcome ->
    semanticUTF8Decode codec bytes = Some text ->
    codecOutcome = SemanticReadUTF8Decoded text.
Proof.
  intros codec occurrence path limit prior bytes next text codecOutcome Hchecked Hdecoded.
  inversion Hchecked; subst; try reflexivity; congruence.
Qed.

Inductive CheckedSemanticWriteUTF8
  (codec : QualifiedUTF8Codec)
  (occurrence : ProviderIdentity)
  (path : SemanticProviderRelativePath)
  (text : SemanticTextValue)
  (prior : SemanticFileSystemState)
  : SemanticFileReplaceOutcome -> SemanticFileSystemState -> Prop :=
| CheckedSemanticWriteUTF8Accepted :
    forall outcome next,
      CheckedSemanticFileSystemReplace
        occurrence path (semanticUTF8Encode codec text)
        prior outcome next ->
      CheckedSemanticWriteUTF8
        codec occurrence path text prior outcome next.

Theorem checked_write_utf8_retains_exact_filesystem_replace :
  forall codec occurrence path text prior outcome next,
    CheckedSemanticWriteUTF8
      codec occurrence path text prior outcome next ->
    CheckedSemanticFileSystemReplace
      occurrence path (semanticUTF8Encode codec text)
      prior outcome next.
Proof.
  intros codec occurrence path text prior outcome next Hchecked.
  inversion Hchecked; assumption.
Qed.

Theorem successful_write_utf8_is_process_observable_as_exact_encoded_bytes :
  forall codec occurrence path text prior next,
    CheckedSemanticWriteUTF8
      codec occurrence path text prior
      SemanticFileReplaceSucceeded next ->
    lookupSemanticFileSystemBinding path next =
      Some (semanticUTF8Encode codec text).
Proof.
  intros codec occurrence path text prior next Hchecked.
  eapply successful_replace_is_process_observable.
  eapply checked_write_utf8_retains_exact_filesystem_replace.
  exact Hchecked.
Qed.

Theorem failed_write_utf8_preserves_prior_filesystem_state :
  forall codec occurrence path text prior failure next,
    CheckedSemanticWriteUTF8
      codec occurrence path text prior
      (SemanticFileReplaceFailed failure) next ->
    next = prior.
Proof.
  intros codec occurrence path text prior failure next Hchecked.
  eapply failed_replace_preserves_prior_state_exactly.
  eapply checked_write_utf8_retains_exact_filesystem_replace.
  exact Hchecked.
Qed.

Inductive CheckedSemanticWriteLine
  (occurrence : SemanticConsoleOccurrence)
  (text : SemanticTextValue)
  : SemanticConsoleWriteOutcome -> nat -> Prop :=
| CheckedSemanticWriteLineAccepted :
    forall outcome observableLength,
      CheckedConsoleWrite
        occurrence (length (appendLineFeed text)) outcome observableLength ->
      CheckedSemanticWriteLine occurrence text outcome observableLength.

Theorem write_line_appends_exactly_one_line_feed_scalar :
  forall text,
    length (appendLineFeed text) = S (length text).
Proof.
  intros text.
  unfold appendLineFeed.
  rewrite app_length.
  simpl.
  apply Nat.add_1_r.
Qed.

Theorem checked_write_line_retains_exact_console_write :
  forall occurrence text outcome observableLength,
    CheckedSemanticWriteLine occurrence text outcome observableLength ->
    CheckedConsoleWrite
      occurrence (length (appendLineFeed text)) outcome observableLength.
Proof.
  intros occurrence text outcome observableLength Hchecked.
  inversion Hchecked; assumption.
Qed.

Theorem failed_write_line_preserves_console_partial_progress :
  forall occurrence text prefixLength observableLength,
    CheckedSemanticWriteLine
      occurrence text (SemanticConsoleWriteFailed prefixLength) observableLength ->
    observableLength = prefixLength /\
    prefixLength <= S (length text).
Proof.
  intros occurrence text prefixLength observableLength Hchecked.
  pose proof
    (checked_write_line_retains_exact_console_write
      occurrence text (SemanticConsoleWriteFailed prefixLength)
      observableLength Hchecked) as Hwrite.
  pose proof
    (failed_console_write_preserves_exact_prefix_progress
      occurrence (length (appendLineFeed text))
      prefixLength observableLength Hwrite) as Hprogress.
  destruct Hprogress as [Hequal Hbound].
  split.
  - exact Hequal.
  - rewrite write_line_appends_exactly_one_line_feed_scalar in Hbound.
    exact Hbound.
Qed.
