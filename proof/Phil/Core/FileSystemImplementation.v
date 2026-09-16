From Stdlib Require Import Bool.Bool.
From Phil.Core Require Import FileSystem.

(*
  PHIL-P1-IO-FS-001 — executable implementation correspondence.

  Production extracts concrete facts from Path, Int, Authority, Map and Bytes.
  This file owns only the ordered decision surface reflected by
  Phil.IO.FileSystem. Existing Path, Bytes, authority and effect semantics stay
  predecessor/native boundaries.
*)

Inductive FileSystemObservedReadKind : Type :=
| ObservedReadSuccess
| ObservedReadTooLarge
| ObservedReadNotFound
| ObservedReadPortableNegative.

Inductive FileSystemReadDecision : Type :=
| FileSystemReadAccepted
| FileSystemReadPathOccurrenceMismatch
| FileSystemReadNegativeLimit
| FileSystemReadAuthorityRejected
| FileSystemReadSuccessMissingBinding
| FileSystemReadSuccessContentMismatch
| FileSystemReadSuccessExceedsLimit
| FileSystemReadTooLargeMismatch
| FileSystemReadNotFoundMismatch.

Definition decideFileSystemReadByFacts
  (pathOccurrenceMatches limitNonnegative authorityAccepted : bool)
  (observedKind : FileSystemObservedReadKind)
  (bindingPresent contentMatches withinLimit : bool)
  : FileSystemReadDecision :=
  if pathOccurrenceMatches then
    if limitNonnegative then
      if authorityAccepted then
        match observedKind with
        | ObservedReadSuccess =>
            if bindingPresent then
              if contentMatches then
                if withinLimit then FileSystemReadAccepted
                else FileSystemReadSuccessExceedsLimit
              else FileSystemReadSuccessContentMismatch
            else FileSystemReadSuccessMissingBinding
        | ObservedReadTooLarge =>
            if bindingPresent then
              if withinLimit then FileSystemReadTooLargeMismatch
              else FileSystemReadAccepted
            else FileSystemReadTooLargeMismatch
        | ObservedReadNotFound =>
            if bindingPresent then FileSystemReadNotFoundMismatch
            else FileSystemReadAccepted
        | ObservedReadPortableNegative => FileSystemReadAccepted
        end
      else FileSystemReadAuthorityRejected
    else FileSystemReadNegativeLimit
  else FileSystemReadPathOccurrenceMismatch.

Inductive FileSystemReplaceDecision : Type :=
| FileSystemReplaceAccepted
| FileSystemReplacePathOccurrenceMismatch
| FileSystemReplaceAuthorityRejected.

Definition decideFileSystemReplaceByFacts
  (pathOccurrenceMatches authorityAccepted : bool)
  : FileSystemReplaceDecision :=
  if pathOccurrenceMatches then
    if authorityAccepted then FileSystemReplaceAccepted
    else FileSystemReplaceAuthorityRejected
  else FileSystemReplacePathOccurrenceMismatch.

Definition replaceShouldInstallBinding
  (observedSuccess : bool) : bool := observedSuccess.

Theorem read_path_mismatch_rejects_first :
  forall limitNonnegative authorityAccepted observedKind bindingPresent contentMatches withinLimit,
    decideFileSystemReadByFacts
      false limitNonnegative authorityAccepted observedKind
      bindingPresent contentMatches withinLimit =
    FileSystemReadPathOccurrenceMismatch.
Proof. reflexivity. Qed.

Theorem negative_limit_rejects_before_authority_or_outcome :
  forall authorityAccepted observedKind bindingPresent contentMatches withinLimit,
    decideFileSystemReadByFacts
      true false authorityAccepted observedKind
      bindingPresent contentMatches withinLimit =
    FileSystemReadNegativeLimit.
Proof. reflexivity. Qed.

Theorem rejected_read_authority_blocks_outcome_validation :
  forall observedKind bindingPresent contentMatches withinLimit,
    decideFileSystemReadByFacts
      true true false observedKind
      bindingPresent contentMatches withinLimit =
    FileSystemReadAuthorityRejected.
Proof. reflexivity. Qed.

Theorem successful_read_requires_existing_binding :
  forall contentMatches withinLimit,
    decideFileSystemReadByFacts
      true true true ObservedReadSuccess
      false contentMatches withinLimit =
    FileSystemReadSuccessMissingBinding.
Proof. reflexivity. Qed.

Theorem successful_read_requires_exact_content_before_bound :
  forall withinLimit,
    decideFileSystemReadByFacts
      true true true ObservedReadSuccess
      true false withinLimit =
    FileSystemReadSuccessContentMismatch.
Proof. reflexivity. Qed.

Theorem oversized_success_rejects :
  decideFileSystemReadByFacts
    true true true ObservedReadSuccess
    true true false =
  FileSystemReadSuccessExceedsLimit.
Proof. reflexivity. Qed.

Theorem bounded_exact_success_accepts :
  decideFileSystemReadByFacts
    true true true ObservedReadSuccess
    true true true =
  FileSystemReadAccepted.
Proof. reflexivity. Qed.

Theorem too_large_requires_existing_oversized_binding :
  decideFileSystemReadByFacts
    true true true ObservedReadTooLarge
    true false false =
  FileSystemReadAccepted.
Proof. reflexivity. Qed.

Theorem too_large_rejects_when_binding_is_within_limit :
  forall contentMatches,
    decideFileSystemReadByFacts
      true true true ObservedReadTooLarge
      true contentMatches true =
    FileSystemReadTooLargeMismatch.
Proof. reflexivity. Qed.

Theorem too_large_rejects_without_binding :
  forall contentMatches withinLimit,
    decideFileSystemReadByFacts
      true true true ObservedReadTooLarge
      false contentMatches withinLimit =
    FileSystemReadTooLargeMismatch.
Proof. reflexivity. Qed.

Theorem not_found_accepts_only_absent_binding :
  forall contentMatches withinLimit,
    decideFileSystemReadByFacts
      true true true ObservedReadNotFound
      false contentMatches withinLimit =
    FileSystemReadAccepted /\
    decideFileSystemReadByFacts
      true true true ObservedReadNotFound
      true contentMatches withinLimit =
    FileSystemReadNotFoundMismatch.
Proof.
  intros contentMatches withinLimit.
  split; reflexivity.
Qed.

Theorem portable_negative_is_state_agnostic_after_preconditions :
  forall bindingPresent contentMatches withinLimit,
    decideFileSystemReadByFacts
      true true true ObservedReadPortableNegative
      bindingPresent contentMatches withinLimit =
    FileSystemReadAccepted.
Proof. reflexivity. Qed.

Theorem replace_path_mismatch_rejects_first :
  forall authorityAccepted,
    decideFileSystemReplaceByFacts false authorityAccepted =
    FileSystemReplacePathOccurrenceMismatch.
Proof. reflexivity. Qed.

Theorem replace_authority_rejects_second :
  decideFileSystemReplaceByFacts true false =
    FileSystemReplaceAuthorityRejected.
Proof. reflexivity. Qed.

Theorem authorized_matching_replace_accepts :
  decideFileSystemReplaceByFacts true true =
    FileSystemReplaceAccepted.
Proof. reflexivity. Qed.

Theorem successful_replace_selects_binding_installation :
  replaceShouldInstallBinding true = true.
Proof. reflexivity. Qed.

Theorem failed_replace_selects_prior_state_preservation :
  replaceShouldInstallBinding false = false.
Proof. reflexivity. Qed.
