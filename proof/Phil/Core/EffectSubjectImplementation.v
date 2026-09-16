From Stdlib Require Import Bool.Bool Lists.List.

From Phil.Core Require Import EffectSubject.

(*
  PHIL-EFFECT-SUBJECT-001 — executable implementation correspondence.

  The Haskell implementation reflects exact subject lookup/equality and the
  opaque correspondence token into a short ordered decision tree.  Concrete
  Text equality, list indexing, canonical effect serialization, and diagnostics
  remain native representation boundaries; this file owns the semantic branch
  structure of the final retarget decision.
*)

Inductive EffectSubjectCorrespondenceDecision : Type :=
| EffectSubjectCorrespondenceAccepted
| EffectSubjectCorrespondenceSourceEmpty
| EffectSubjectCorrespondenceTargetEmpty
| EffectSubjectCorrespondenceRevisionEmpty.

Definition decideEffectSubjectCorrespondence
  (sourceNonempty targetNonempty revisionNonempty : bool)
  : EffectSubjectCorrespondenceDecision :=
  if sourceNonempty then
    if targetNonempty then
      if revisionNonempty then EffectSubjectCorrespondenceAccepted
      else EffectSubjectCorrespondenceRevisionEmpty
    else EffectSubjectCorrespondenceTargetEmpty
  else EffectSubjectCorrespondenceSourceEmpty.

Definition effectSubjectCorrespondenceFactsAccepted
  (sourceNonempty targetNonempty revisionNonempty : bool) : bool :=
  andb sourceNonempty (andb targetNonempty revisionNonempty).

Theorem correspondence_decision_accept_iff_all_integrity_facts :
  forall sourceNonempty targetNonempty revisionNonempty,
    decideEffectSubjectCorrespondence
      sourceNonempty targetNonempty revisionNonempty =
      EffectSubjectCorrespondenceAccepted <->
    effectSubjectCorrespondenceFactsAccepted
      sourceNonempty targetNonempty revisionNonempty = true.
Proof.
  intros sourceNonempty targetNonempty revisionNonempty.
  destruct sourceNonempty, targetNonempty, revisionNonempty;
    simpl; split; intro H; try reflexivity; discriminate H.
Qed.

Inductive EffectSubjectRetargetDecision : Type :=
| EffectSubjectRetargetAcceptedSame
| EffectSubjectRetargetAcceptedCorrespondence
| EffectSubjectRetargetIndexOutOfRange
| EffectSubjectRetargetRequiresCorrespondence
| EffectSubjectRetargetCorrespondenceSourceMismatch
| EffectSubjectRetargetCorrespondenceTargetMismatch.

Definition decideEffectSubjectRetarget
  (indexInRange sameSubject correspondencePresent
   correspondenceSourceMatches correspondenceTargetMatches : bool)
  : EffectSubjectRetargetDecision :=
  if indexInRange then
    if sameSubject then EffectSubjectRetargetAcceptedSame
    else
      if correspondencePresent then
        if correspondenceSourceMatches then
          if correspondenceTargetMatches then
            EffectSubjectRetargetAcceptedCorrespondence
          else EffectSubjectRetargetCorrespondenceTargetMismatch
        else EffectSubjectRetargetCorrespondenceSourceMismatch
      else EffectSubjectRetargetRequiresCorrespondence
  else EffectSubjectRetargetIndexOutOfRange.

Definition effectSubjectRetargetFactsAccepted
  (indexInRange sameSubject correspondencePresent
   correspondenceSourceMatches correspondenceTargetMatches : bool) : bool :=
  andb indexInRange
    (orb sameSubject
      (andb correspondencePresent
        (andb correspondenceSourceMatches correspondenceTargetMatches))).

Definition effectSubjectRetargetDecisionAccepted
  (decision : EffectSubjectRetargetDecision) : bool :=
  match decision with
  | EffectSubjectRetargetAcceptedSame => true
  | EffectSubjectRetargetAcceptedCorrespondence => true
  | _ => false
  end.

Theorem retarget_decision_accept_iff_exact_reflected_shape :
  forall indexInRange sameSubject correspondencePresent
    correspondenceSourceMatches correspondenceTargetMatches,
    effectSubjectRetargetDecisionAccepted
      (decideEffectSubjectRetarget
        indexInRange sameSubject correspondencePresent
        correspondenceSourceMatches correspondenceTargetMatches) = true <->
    effectSubjectRetargetFactsAccepted
      indexInRange sameSubject correspondencePresent
      correspondenceSourceMatches correspondenceTargetMatches = true.
Proof.
  intros indexInRange sameSubject correspondencePresent
    correspondenceSourceMatches correspondenceTargetMatches.
  destruct indexInRange, sameSubject, correspondencePresent,
    correspondenceSourceMatches, correspondenceTargetMatches;
    simpl; split; intro H; try reflexivity; discriminate H.
Qed.

Theorem same_subject_decision_does_not_require_correspondence :
  forall correspondencePresent correspondenceSourceMatches
    correspondenceTargetMatches,
    decideEffectSubjectRetarget
      true true correspondencePresent
      correspondenceSourceMatches correspondenceTargetMatches =
      EffectSubjectRetargetAcceptedSame.
Proof.
  reflexivity.
Qed.

Theorem distinct_subject_without_correspondence_decision_rejects :
  forall correspondenceSourceMatches correspondenceTargetMatches,
    decideEffectSubjectRetarget
      true false false
      correspondenceSourceMatches correspondenceTargetMatches =
      EffectSubjectRetargetRequiresCorrespondence.
Proof.
  reflexivity.
Qed.

Theorem exact_correspondence_decision_accepts_changed_subject :
  decideEffectSubjectRetarget true false true true true =
    EffectSubjectRetargetAcceptedCorrespondence.
Proof.
  reflexivity.
Qed.

Theorem correspondence_source_mismatch_decision_rejects :
  forall correspondenceTargetMatches,
    decideEffectSubjectRetarget true false true false correspondenceTargetMatches =
      EffectSubjectRetargetCorrespondenceSourceMismatch.
Proof.
  reflexivity.
Qed.

Theorem correspondence_target_mismatch_decision_rejects :
  decideEffectSubjectRetarget true false true true false =
    EffectSubjectRetargetCorrespondenceTargetMismatch.
Proof.
  reflexivity.
Qed.

Theorem out_of_range_decision_rejects_before_identity_checks :
  forall sameSubject correspondencePresent correspondenceSourceMatches
    correspondenceTargetMatches,
    decideEffectSubjectRetarget
      false sameSubject correspondencePresent
      correspondenceSourceMatches correspondenceTargetMatches =
      EffectSubjectRetargetIndexOutOfRange.
Proof.
  reflexivity.
Qed.

Theorem accepted_same_subject_branch_constructs_certified_retarget :
  forall index subject effect,
    nth_error
      (semanticEffectSubjects (checkedSemanticEffectIdentity effect))
      index = Some subject ->
    decideEffectSubjectRetarget true true false false false =
      EffectSubjectRetargetAcceptedSame ->
    CheckedEffectSubjectRetarget index subject None effect effect.
Proof.
  intros index subject effect Hsubject Hdecision.
  apply same_subject_without_correspondence_is_accepted.
  exact Hsubject.
Qed.

Theorem accepted_correspondence_branch_constructs_certified_retarget :
  forall index source target correspondence effect,
    nth_error
      (semanticEffectSubjects (checkedSemanticEffectIdentity effect))
      index = Some source ->
    source <> target ->
    effectSubjectCorrespondenceSource correspondence = source ->
    effectSubjectCorrespondenceTarget correspondence = target ->
    EffectSubjectCorrespondenceValid correspondence ->
    decideEffectSubjectRetarget true false true true true =
      EffectSubjectRetargetAcceptedCorrespondence ->
    CheckedEffectSubjectRetarget
      index target (Some correspondence) effect
      (mkCheckedSemanticEffect
        (mkSemanticEffectIdentity
          (semanticEffectLabel (checkedSemanticEffectIdentity effect))
          (replaceEffectSubjectAt index target
            (semanticEffectSubjects (checkedSemanticEffectIdentity effect))))
        (checkedSemanticEffectRepresentationToken effect)).
Proof.
  intros index source target correspondence effect Hsource Hdistinct
    HcorrespondenceSource HcorrespondenceTarget Hvalid Hdecision.
  apply exact_correspondence_constructs_changed_retarget with (source := source).
  - exact Hsource.
  - exact Hdistinct.
  - exact HcorrespondenceSource.
  - exact HcorrespondenceTarget.
  - exact Hvalid.
Qed.

Theorem representation_coincidence_has_no_acceptance_input :
  forall (Representation : Type)
    indexInRange sameSubject correspondencePresent
    correspondenceSourceMatches correspondenceTargetMatches
    (firstRepresentation secondRepresentation : Representation),
    firstRepresentation = secondRepresentation ->
    decideEffectSubjectRetarget
      indexInRange sameSubject correspondencePresent
      correspondenceSourceMatches correspondenceTargetMatches =
    decideEffectSubjectRetarget
      indexInRange sameSubject correspondencePresent
      correspondenceSourceMatches correspondenceTargetMatches.
Proof.
  intros.
  reflexivity.
Qed.
