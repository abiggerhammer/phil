From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import ProviderRelativePath RuntimeBytes.

(*
  PHIL-P1-IO-FS-001 — bounded read and process-observable replace semantics.

  This file owns the representation-neutral filesystem state transition facts.
  Canonical provider-relative Path identity and runtime-sized Bytes are imported
  predecessor boundaries. Authority competence is likewise imported: this proof
  assumes an accepted authority fact and proves what an accepted filesystem
  operation may do with semantic state.
*)

Inductive SemanticFileSystemOperation : Type :=
| SemanticFileSystemRead
| SemanticFileSystemReplace.

Parameter FileSystemAuthorityAccepted
  : ProviderIdentity -> SemanticFileSystemOperation -> Prop.

Definition PathBelongsToOccurrence
  (occurrence : ProviderIdentity)
  (path : SemanticProviderRelativePath) : Prop :=
  semanticPathOccurrence path = occurrence.

Inductive SemanticFileSystemFailure : Type :=
| SemanticFileSystemNotFound
| SemanticFileSystemTooLarge
| SemanticFileSystemPortableNegative (code : nat).

Inductive SemanticFileReadOutcome : Type :=
| SemanticFileReadSucceeded (bytes : SemanticBytesValue)
| SemanticFileReadFailed (failure : SemanticFileSystemFailure).

Inductive SemanticFileReplaceOutcome : Type :=
| SemanticFileReplaceSucceeded
| SemanticFileReplaceFailed (failure : SemanticFileSystemFailure).

Parameter SemanticFileSystemState : Type.

Parameter lookupSemanticFileSystemBinding
  : SemanticProviderRelativePath -> SemanticFileSystemState -> option SemanticBytesValue.

Parameter replaceSemanticFileSystemBinding
  : SemanticProviderRelativePath -> SemanticBytesValue -> SemanticFileSystemState ->
    SemanticFileSystemState.

Axiom replace_binding_is_process_observable :
  forall path bytes state,
    lookupSemanticFileSystemBinding
      path
      (replaceSemanticFileSystemBinding path bytes state) =
    Some bytes.

Inductive CheckedSemanticFileSystemRead
  : ProviderIdentity -> SemanticProviderRelativePath -> nat ->
    SemanticFileSystemState -> SemanticFileReadOutcome ->
    SemanticFileSystemState -> Prop :=
| CheckedSemanticFileSystemReadSuccess :
    forall occurrence path limit prior expected observed,
      PathBelongsToOccurrence occurrence path ->
      FileSystemAuthorityAccepted occurrence SemanticFileSystemRead ->
      lookupSemanticFileSystemBinding path prior = Some expected ->
      observed = expected ->
      semanticBytesRuntimeLength observed <= limit ->
      CheckedSemanticFileSystemRead
        occurrence path limit prior
        (SemanticFileReadSucceeded observed)
        prior
| CheckedSemanticFileSystemReadTooLarge :
    forall occurrence path limit prior bytes,
      PathBelongsToOccurrence occurrence path ->
      FileSystemAuthorityAccepted occurrence SemanticFileSystemRead ->
      lookupSemanticFileSystemBinding path prior = Some bytes ->
      limit < semanticBytesRuntimeLength bytes ->
      CheckedSemanticFileSystemRead
        occurrence path limit prior
        (SemanticFileReadFailed SemanticFileSystemTooLarge)
        prior
| CheckedSemanticFileSystemReadNotFound :
    forall occurrence path limit prior,
      PathBelongsToOccurrence occurrence path ->
      FileSystemAuthorityAccepted occurrence SemanticFileSystemRead ->
      lookupSemanticFileSystemBinding path prior = None ->
      CheckedSemanticFileSystemRead
        occurrence path limit prior
        (SemanticFileReadFailed SemanticFileSystemNotFound)
        prior
| CheckedSemanticFileSystemReadPortableNegative :
    forall occurrence path limit prior code,
      PathBelongsToOccurrence occurrence path ->
      FileSystemAuthorityAccepted occurrence SemanticFileSystemRead ->
      CheckedSemanticFileSystemRead
        occurrence path limit prior
        (SemanticFileReadFailed (SemanticFileSystemPortableNegative code))
        prior.

Inductive CheckedSemanticFileSystemReplace
  : ProviderIdentity -> SemanticProviderRelativePath -> SemanticBytesValue ->
    SemanticFileSystemState -> SemanticFileReplaceOutcome ->
    SemanticFileSystemState -> Prop :=
| CheckedSemanticFileSystemReplaceSuccess :
    forall occurrence path bytes prior,
      PathBelongsToOccurrence occurrence path ->
      FileSystemAuthorityAccepted occurrence SemanticFileSystemReplace ->
      CheckedSemanticFileSystemReplace
        occurrence path bytes prior
        SemanticFileReplaceSucceeded
        (replaceSemanticFileSystemBinding path bytes prior)
| CheckedSemanticFileSystemReplaceFailure :
    forall occurrence path bytes prior failure,
      PathBelongsToOccurrence occurrence path ->
      FileSystemAuthorityAccepted occurrence SemanticFileSystemReplace ->
      CheckedSemanticFileSystemReplace
        occurrence path bytes prior
        (SemanticFileReplaceFailed failure)
        prior.

Theorem checked_read_preserves_semantic_state :
  forall occurrence path limit prior outcome next,
    CheckedSemanticFileSystemRead occurrence path limit prior outcome next ->
    next = prior.
Proof.
  intros occurrence path limit prior outcome next Hchecked.
  inversion Hchecked; reflexivity.
Qed.

Theorem successful_read_returns_exact_binding_within_limit :
  forall occurrence path limit prior observed next,
    CheckedSemanticFileSystemRead
      occurrence path limit prior
      (SemanticFileReadSucceeded observed) next ->
    lookupSemanticFileSystemBinding path prior = Some observed /\
    semanticBytesRuntimeLength observed <= limit.
Proof.
  intros occurrence path limit prior observed next Hchecked.
  inversion Hchecked; subst.
  split; assumption.
Qed.

Theorem too_large_read_requires_existing_oversized_binding :
  forall occurrence path limit prior next,
    CheckedSemanticFileSystemRead
      occurrence path limit prior
      (SemanticFileReadFailed SemanticFileSystemTooLarge) next ->
    exists bytes,
      lookupSemanticFileSystemBinding path prior = Some bytes /\
      limit < semanticBytesRuntimeLength bytes.
Proof.
  intros occurrence path limit prior next Hchecked.
  inversion Hchecked; subst.
  eexists; split; eassumption.
Qed.

Theorem not_found_read_requires_absent_binding :
  forall occurrence path limit prior next,
    CheckedSemanticFileSystemRead
      occurrence path limit prior
      (SemanticFileReadFailed SemanticFileSystemNotFound) next ->
    lookupSemanticFileSystemBinding path prior = None.
Proof.
  intros occurrence path limit prior next Hchecked.
  inversion Hchecked; subst.
  assumption.
Qed.

Theorem accepted_read_uses_exact_path_occurrence :
  forall occurrence path limit prior outcome next,
    CheckedSemanticFileSystemRead occurrence path limit prior outcome next ->
    semanticPathOccurrence path = occurrence.
Proof.
  intros occurrence path limit prior outcome next Hchecked.
  inversion Hchecked; subst; assumption.
Qed.

Theorem successful_replace_is_process_observable :
  forall occurrence path bytes prior next,
    CheckedSemanticFileSystemReplace
      occurrence path bytes prior SemanticFileReplaceSucceeded next ->
    lookupSemanticFileSystemBinding path next = Some bytes.
Proof.
  intros occurrence path bytes prior next Hchecked.
  inversion Hchecked; subst.
  apply replace_binding_is_process_observable.
Qed.

Theorem failed_replace_preserves_prior_state_exactly :
  forall occurrence path bytes prior failure next,
    CheckedSemanticFileSystemReplace
      occurrence path bytes prior
      (SemanticFileReplaceFailed failure) next ->
    next = prior.
Proof.
  intros occurrence path bytes prior failure next Hchecked.
  inversion Hchecked; reflexivity.
Qed.

Theorem accepted_replace_uses_exact_path_occurrence :
  forall occurrence path bytes prior outcome next,
    CheckedSemanticFileSystemReplace occurrence path bytes prior outcome next ->
    semanticPathOccurrence path = occurrence.
Proof.
  intros occurrence path bytes prior outcome next Hchecked.
  inversion Hchecked; subst; assumption.
Qed.

Theorem read_and_replace_authority_operations_are_distinct :
  SemanticFileSystemRead <> SemanticFileSystemReplace.
Proof.
  discriminate.
Qed.
