From Stdlib Require Import Bool.Bool Lists.List Arith.PeanoNat.
From Phil.Core Require Import ProviderRelativePath.
Import ListNotations.

(*
  PHIL-P1-IO-PATH-001 — executable implementation correspondence.

  Production computes concrete Data.Text facts.  This file owns the ordered
  admission decisions reflected by Phil.Systems:

    occurrence: empty rejects, otherwise accepts;
    path: empty raw text before absolute source '/', then segments left-to-right;
    segment: empty before '.', then '..', otherwise accepted.

  Concrete Text.null, isPrefixOf, splitOn and scalar representation remain the
  native representation boundary.
*)

Inductive FileSystemOccurrenceDecision : Type :=
| FileSystemOccurrenceAccepted
| FileSystemOccurrenceEmpty.

Definition decideFileSystemOccurrenceByFacts
  (occurrenceEmpty : bool) : FileSystemOccurrenceDecision :=
  if occurrenceEmpty then
    FileSystemOccurrenceEmpty
  else
    FileSystemOccurrenceAccepted.

Inductive ProviderRelativePathDecision : Type :=
| ProviderRelativePathAccepted
| ProviderRelativePathEmpty
| ProviderRelativePathAbsolute
| ProviderRelativePathEmptySegment (index : nat)
| ProviderRelativePathDotSegment (index : nat)
| ProviderRelativePathParentSegment (index : nat).

Record ProviderRelativeSegmentFacts : Type := mkProviderRelativeSegmentFacts {
  providerRelativeSegmentEmpty : bool;
  providerRelativeSegmentDot : bool;
  providerRelativeSegmentParent : bool
}.

Definition decideProviderRelativeSegmentAt
  (index : nat)
  (facts : ProviderRelativeSegmentFacts)
  : ProviderRelativePathDecision :=
  if providerRelativeSegmentEmpty facts then
    ProviderRelativePathEmptySegment index
  else if providerRelativeSegmentDot facts then
    ProviderRelativePathDotSegment index
  else if providerRelativeSegmentParent facts then
    ProviderRelativePathParentSegment index
  else
    ProviderRelativePathAccepted.

Fixpoint decideProviderRelativeSegmentsFrom
  (index : nat)
  (facts : list ProviderRelativeSegmentFacts)
  : ProviderRelativePathDecision :=
  match facts with
  | [] => ProviderRelativePathAccepted
  | first :: rest =>
      match decideProviderRelativeSegmentAt index first with
      | ProviderRelativePathAccepted =>
          decideProviderRelativeSegmentsFrom (S index) rest
      | rejected => rejected
      end
  end.

Definition decideProviderRelativePathByFacts
  (rawEmpty startsWithSourceSlash : bool)
  (segmentFacts : list ProviderRelativeSegmentFacts)
  : ProviderRelativePathDecision :=
  if rawEmpty then
    ProviderRelativePathEmpty
  else if startsWithSourceSlash then
    ProviderRelativePathAbsolute
  else
    decideProviderRelativeSegmentsFrom 1 segmentFacts.

Theorem empty_occurrence_rejects :
  decideFileSystemOccurrenceByFacts true = FileSystemOccurrenceEmpty.
Proof.
  reflexivity.
Qed.

Theorem nonempty_occurrence_accepts :
  decideFileSystemOccurrenceByFacts false = FileSystemOccurrenceAccepted.
Proof.
  reflexivity.
Qed.

Theorem empty_path_rejects_before_absolute_check :
  forall startsWithSourceSlash segmentFacts,
    decideProviderRelativePathByFacts
      true startsWithSourceSlash segmentFacts =
      ProviderRelativePathEmpty.
Proof.
  reflexivity.
Qed.

Theorem absolute_source_root_rejects_before_segment_validation :
  forall segmentFacts,
    decideProviderRelativePathByFacts false true segmentFacts =
      ProviderRelativePathAbsolute.
Proof.
  reflexivity.
Qed.

Theorem empty_segment_rejects_before_dot_or_parent :
  forall index dot parent,
    decideProviderRelativeSegmentAt
      index
      (mkProviderRelativeSegmentFacts true dot parent) =
      ProviderRelativePathEmptySegment index.
Proof.
  reflexivity.
Qed.

Theorem dot_segment_rejects_before_parent :
  forall index parent,
    decideProviderRelativeSegmentAt
      index
      (mkProviderRelativeSegmentFacts false true parent) =
      ProviderRelativePathDotSegment index.
Proof.
  reflexivity.
Qed.

Theorem parent_segment_rejects_after_nonempty_nondot :
  forall index,
    decideProviderRelativeSegmentAt
      index
      (mkProviderRelativeSegmentFacts false false true) =
      ProviderRelativePathParentSegment index.
Proof.
  reflexivity.
Qed.

Theorem clean_segment_advances_to_next_source_segment :
  forall index rest,
    decideProviderRelativeSegmentsFrom
      index
      (mkProviderRelativeSegmentFacts false false false :: rest) =
    decideProviderRelativeSegmentsFrom (S index) rest.
Proof.
  reflexivity.
Qed.

Theorem first_rejected_segment_blocks_later_segments :
  forall index facts rest decision,
    decideProviderRelativeSegmentAt index facts = decision ->
    decision <> ProviderRelativePathAccepted ->
    decideProviderRelativeSegmentsFrom index (facts :: rest) = decision.
Proof.
  intros index facts rest decision Hdecision Hrejected.
  simpl.
  rewrite Hdecision.
  destruct decision; try contradiction; reflexivity.
Qed.

Theorem accepted_segment_decision_implies_clean_facts :
  forall index facts,
    decideProviderRelativeSegmentAt index facts =
      ProviderRelativePathAccepted ->
    providerRelativeSegmentEmpty facts = false /\
    providerRelativeSegmentDot facts = false /\
    providerRelativeSegmentParent facts = false.
Proof.
  intros index facts Haccepted.
  destruct facts as [empty dot parent].
  destruct empty, dot, parent; simpl in Haccepted; try discriminate;
    repeat split; reflexivity.
Qed.

(*
  This relation is the explicit bridge from concrete implementation facts to
  representation-neutral scalar sequences.  The fact extraction itself is the
  native Data.Text boundary; accepted clean facts must describe a canonical
  semantic segment.
*)
Parameter SegmentFactsDescribe
  : ProviderRelativeSegmentFacts -> PathSegment -> Prop.

Axiom clean_described_segment_is_valid :
  forall facts segment,
    SegmentFactsDescribe facts segment ->
    providerRelativeSegmentEmpty facts = false ->
    providerRelativeSegmentDot facts = false ->
    providerRelativeSegmentParent facts = false ->
    ValidPathSegment segment.

Inductive SegmentFactsDescribeList
  : list ProviderRelativeSegmentFacts -> list PathSegment -> Prop :=
| SegmentFactsDescribeNil :
    SegmentFactsDescribeList [] []
| SegmentFactsDescribeCons :
    forall facts segment restFacts restSegments,
      SegmentFactsDescribe facts segment ->
      SegmentFactsDescribeList restFacts restSegments ->
      SegmentFactsDescribeList
        (facts :: restFacts)
        (segment :: restSegments).

Theorem accepted_segment_list_is_semantically_canonical :
  forall index facts segments,
    SegmentFactsDescribeList facts segments ->
    decideProviderRelativeSegmentsFrom index facts =
      ProviderRelativePathAccepted ->
    Forall ValidPathSegment segments.
Proof.
  intros index facts segments Hdescribe.
  revert index.
  induction Hdescribe as
      [| facts segment restFacts restSegments Hfacts Hrest IH];
    intros index Haccepted.
  - constructor.
  - simpl in Haccepted.
    destruct (decideProviderRelativeSegmentAt index facts) eqn:Hsegment;
      try discriminate Haccepted.
    constructor.
    + pose proof
        (accepted_segment_decision_implies_clean_facts
          index facts Hsegment)
        as [Hempty [Hdot Hparent]].
      eapply clean_described_segment_is_valid; eauto.
    + eapply IH.
      exact Haccepted.
Qed.

Theorem accepted_implementation_path_constructs_exact_semantic_path :
  forall occurrence segments segmentFacts,
    ValidProviderIdentity occurrence ->
    segments <> [] ->
    SegmentFactsDescribeList segmentFacts segments ->
    decideProviderRelativePathByFacts false false segmentFacts =
      ProviderRelativePathAccepted ->
    CheckedProviderRelativePath
      occurrence
      segments
      (mkSemanticProviderRelativePath occurrence segments).
Proof.
  intros occurrence segments segmentFacts Hoccurrence Hsegments Hdescribe Haccepted.
  apply CheckedProviderRelativePathAccepted.
  - exact Hoccurrence.
  - exact Hsegments.
  - eapply accepted_segment_list_is_semantically_canonical.
    + exact Hdescribe.
    + exact Haccepted.
Qed.
