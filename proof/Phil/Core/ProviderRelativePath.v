From Stdlib Require Import Lists.List.
Import ListNotations.

(*
  PHIL-P1-IO-PATH-001 — canonical provider-relative Path semantics.

  This proof owns the representation-neutral semantic facts that an accepted
  Path is qualified by exactly one FileSystem occurrence, contains only
  nonempty/non-dot/non-parent source segments, and preserves the exact segment
  scalar sequences supplied by the checked implementation.

  Concrete Data.Text scalar representation and splitOn "/" behavior remain
  implementation facts.  Host path conventions are deliberately absent from
  the semantic identity.
*)

Definition UnicodeScalar : Type := nat.
Definition ProviderIdentity : Type := list UnicodeScalar.
Definition PathSegment : Type := list UnicodeScalar.

Definition dotScalar : UnicodeScalar := 46.
Definition backslashScalar : UnicodeScalar := 92.

Definition ValidProviderIdentity (occurrence : ProviderIdentity) : Prop :=
  occurrence <> [].

Definition ValidPathSegment (segment : PathSegment) : Prop :=
  segment <> [] /\
  segment <> [dotScalar] /\
  segment <> [dotScalar; dotScalar].

Record SemanticProviderRelativePath : Type := mkSemanticProviderRelativePath {
  semanticPathOccurrence : ProviderIdentity;
  semanticPathSegments : list PathSegment
}.

Inductive CheckedProviderRelativePath
  : ProviderIdentity -> list PathSegment -> SemanticProviderRelativePath -> Prop :=
| CheckedProviderRelativePathAccepted :
    forall occurrence segments,
      ValidProviderIdentity occurrence ->
      segments <> [] ->
      Forall ValidPathSegment segments ->
      CheckedProviderRelativePath
        occurrence
        segments
        (mkSemanticProviderRelativePath occurrence segments).

Theorem checked_path_occurrence_is_exact :
  forall occurrence segments path,
    CheckedProviderRelativePath occurrence segments path ->
    semanticPathOccurrence path = occurrence.
Proof.
  intros occurrence segments path Hchecked.
  inversion Hchecked.
  reflexivity.
Qed.

Theorem checked_path_segments_are_exact :
  forall occurrence segments path,
    CheckedProviderRelativePath occurrence segments path ->
    semanticPathSegments path = segments.
Proof.
  intros occurrence segments path Hchecked.
  inversion Hchecked.
  reflexivity.
Qed.

Theorem checked_path_has_nonempty_provider_occurrence :
  forall occurrence segments path,
    CheckedProviderRelativePath occurrence segments path ->
    ValidProviderIdentity occurrence.
Proof.
  intros occurrence segments path Hchecked.
  inversion Hchecked.
  assumption.
Qed.

Theorem checked_path_has_at_least_one_segment :
  forall occurrence segments path,
    CheckedProviderRelativePath occurrence segments path ->
    segments <> [].
Proof.
  intros occurrence segments path Hchecked.
  inversion Hchecked.
  assumption.
Qed.

Theorem checked_path_contains_only_canonical_segments :
  forall occurrence segments path,
    CheckedProviderRelativePath occurrence segments path ->
    Forall ValidPathSegment segments.
Proof.
  intros occurrence segments path Hchecked.
  inversion Hchecked.
  assumption.
Qed.

Theorem provider_occurrence_is_identity_bearing :
  forall leftOccurrence rightOccurrence segments,
    leftOccurrence <> rightOccurrence ->
    mkSemanticProviderRelativePath leftOccurrence segments <>
      mkSemanticProviderRelativePath rightOccurrence segments.
Proof.
  intros leftOccurrence rightOccurrence segments Hneq Heq.
  inversion Heq.
  contradiction.
Qed.

Theorem distinct_scalar_segment_sequences_do_not_normalize_together :
  forall occurrence leftSegments rightSegments,
    leftSegments <> rightSegments ->
    mkSemanticProviderRelativePath occurrence leftSegments <>
      mkSemanticProviderRelativePath occurrence rightSegments.
Proof.
  intros occurrence leftSegments rightSegments Hneq Heq.
  inversion Heq.
  contradiction.
Qed.

Theorem accepted_constructor_preserves_occurrence_and_segments :
  forall occurrence segments,
    ValidProviderIdentity occurrence ->
    segments <> [] ->
    Forall ValidPathSegment segments ->
    CheckedProviderRelativePath
      occurrence
      segments
      (mkSemanticProviderRelativePath occurrence segments).
Proof.
  intros occurrence segments Hoccurrence Hsegments Hvalid.
  constructor; assumption.
Qed.

Theorem source_backslash_is_ordinary_segment_data :
  ValidPathSegment [backslashScalar].
Proof.
  unfold ValidPathSegment, backslashScalar, dotScalar.
  repeat split; discriminate.
Qed.
