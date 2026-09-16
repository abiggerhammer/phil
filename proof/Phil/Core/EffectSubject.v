From Stdlib Require Import Lists.List Arith.PeanoNat.

Import ListNotations.

(*
  PHIL-EFFECT-SUBJECT-001 — semantic effect identity is indexed by exact
  semantic subjects.

  Effect labels and subject identities are semantic.  Runtime handles, source
  spellings, target symbols, addresses, and other representation facts are not
  part of effect identity and cannot authorize subject retargeting.

  A changed subject is admissible only through an explicit correspondence that
  names the exact current source, exact requested target, and a nonzero accepted
  relation revision.  Truth of the externally accepted relation and concrete
  Text/canonical-serialization details remain correspondence boundaries.
*)

Record SemanticEffectIdentity : Type := mkSemanticEffectIdentity {
  semanticEffectLabel : list nat;
  semanticEffectSubjects : list nat
}.

Record CheckedSemanticEffect : Type := mkCheckedSemanticEffect {
  checkedSemanticEffectIdentity : SemanticEffectIdentity;
  checkedSemanticEffectRepresentationToken : nat
}.

Record EffectSubjectCorrespondence : Type := mkEffectSubjectCorrespondence {
  effectSubjectCorrespondenceSource : nat;
  effectSubjectCorrespondenceTarget : nat;
  effectSubjectCorrespondenceRevision : nat
}.

Definition EffectSubjectCorrespondenceValid
  (correspondence : EffectSubjectCorrespondence) : Prop :=
  effectSubjectCorrespondenceRevision correspondence <> 0.

Fixpoint replaceEffectSubjectAt
  (index target : nat)
  (subjects : list nat) : list nat :=
  match index, subjects with
  | O, _ :: rest => target :: rest
  | S remaining, subject :: rest =>
      subject :: replaceEffectSubjectAt remaining target rest
  | _, [] => []
  end.

Inductive CheckedEffectSubjectRetarget
  : nat -> nat -> option EffectSubjectCorrespondence ->
    CheckedSemanticEffect -> CheckedSemanticEffect -> Prop :=
| CheckedEffectRetargetSame :
    forall index source target effect,
      nth_error
        (semanticEffectSubjects (checkedSemanticEffectIdentity effect))
        index = Some source ->
      source = target ->
      CheckedEffectSubjectRetarget index target None effect effect
| CheckedEffectRetargetCorrespondence :
    forall index source target correspondence effect,
      nth_error
        (semanticEffectSubjects (checkedSemanticEffectIdentity effect))
        index = Some source ->
      source <> target ->
      effectSubjectCorrespondenceSource correspondence = source ->
      effectSubjectCorrespondenceTarget correspondence = target ->
      EffectSubjectCorrespondenceValid correspondence ->
      CheckedEffectSubjectRetarget
        index target (Some correspondence) effect
        (mkCheckedSemanticEffect
          (mkSemanticEffectIdentity
            (semanticEffectLabel (checkedSemanticEffectIdentity effect))
            (replaceEffectSubjectAt index target
              (semanticEffectSubjects
                (checkedSemanticEffectIdentity effect))))
          (checkedSemanticEffectRepresentationToken effect)).

Theorem semantic_effect_identity_preserves_exact_subjects :
  forall first second,
    first = second ->
    semanticEffectSubjects first = semanticEffectSubjects second.
Proof.
  intros first second Hequal.
  subst second.
  reflexivity.
Qed.

Theorem same_label_distinct_subjects_do_not_collapse :
  forall label firstSubjects secondSubjects,
    firstSubjects <> secondSubjects ->
    mkSemanticEffectIdentity label firstSubjects <>
      mkSemanticEffectIdentity label secondSubjects.
Proof.
  intros label firstSubjects secondSubjects Hdistinct Hequal.
  apply Hdistinct.
  exact
    (semantic_effect_identity_preserves_exact_subjects
      (mkSemanticEffectIdentity label firstSubjects)
      (mkSemanticEffectIdentity label secondSubjects)
      Hequal).
Qed.

Theorem matching_representation_does_not_collapse_effect_identity :
  forall first second,
    checkedSemanticEffectRepresentationToken first =
      checkedSemanticEffectRepresentationToken second ->
    checkedSemanticEffectIdentity first <>
      checkedSemanticEffectIdentity second ->
    first <> second.
Proof.
  intros first second Hrepresentation Hidentity Hequal.
  subst second.
  apply Hidentity.
  reflexivity.
Qed.

Theorem checked_retarget_without_correspondence_is_same_subject :
  forall index target before after,
    CheckedEffectSubjectRetarget index target None before after ->
    after = before /\
    exists source,
      nth_error
        (semanticEffectSubjects (checkedSemanticEffectIdentity before))
        index = Some source /\
      source = target.
Proof.
  intros index target before after Hchecked.
  inversion Hchecked; subst.
  split.
  - reflexivity.
  - eexists.
    split; eauto.
Qed.

Theorem distinct_subject_without_correspondence_rejects :
  forall index source target before after,
    nth_error
      (semanticEffectSubjects (checkedSemanticEffectIdentity before))
      index = Some source ->
    source <> target ->
    ~ CheckedEffectSubjectRetarget index target None before after.
Proof.
  intros index source target before after Hsource Hdistinct Hchecked.
  destruct
    (checked_retarget_without_correspondence_is_same_subject
      index target before after Hchecked)
    as [_ [actualSource [Hactual Hsame]]].
  rewrite Hsource in Hactual.
  inversion Hactual; subst actualSource.
  contradiction.
Qed.

Corollary matching_representation_does_not_authorize_subject_retarget :
  forall index source target before after,
    nth_error
      (semanticEffectSubjects (checkedSemanticEffectIdentity before))
      index = Some source ->
    source <> target ->
    checkedSemanticEffectRepresentationToken before =
      checkedSemanticEffectRepresentationToken after ->
    ~ CheckedEffectSubjectRetarget index target None before after.
Proof.
  intros index source target before after Hsource Hdistinct Hrepresentation.
  apply distinct_subject_without_correspondence_rejects with (source := source).
  - exact Hsource.
  - exact Hdistinct.
Qed.

Theorem changed_retarget_carries_exact_correspondence :
  forall index target correspondence before after,
    CheckedEffectSubjectRetarget
      index target (Some correspondence) before after ->
    exists source,
      nth_error
        (semanticEffectSubjects (checkedSemanticEffectIdentity before))
        index = Some source /\
      source <> target /\
      effectSubjectCorrespondenceSource correspondence = source /\
      effectSubjectCorrespondenceTarget correspondence = target /\
      EffectSubjectCorrespondenceValid correspondence /\
      after =
        mkCheckedSemanticEffect
          (mkSemanticEffectIdentity
            (semanticEffectLabel (checkedSemanticEffectIdentity before))
            (replaceEffectSubjectAt index target
              (semanticEffectSubjects
                (checkedSemanticEffectIdentity before))))
          (checkedSemanticEffectRepresentationToken before).
Proof.
  intros index target correspondence before after Hchecked.
  inversion Hchecked; subst.
  eexists.
  repeat split; eauto.
Qed.

Theorem same_subject_without_correspondence_is_accepted :
  forall index subject effect,
    nth_error
      (semanticEffectSubjects (checkedSemanticEffectIdentity effect))
      index = Some subject ->
    CheckedEffectSubjectRetarget index subject None effect effect.
Proof.
  intros index subject effect Hsubject.
  econstructor.
  - exact Hsubject.
  - reflexivity.
Qed.

Theorem exact_correspondence_constructs_changed_retarget :
  forall index source target correspondence effect,
    nth_error
      (semanticEffectSubjects (checkedSemanticEffectIdentity effect))
      index = Some source ->
    source <> target ->
    effectSubjectCorrespondenceSource correspondence = source ->
    effectSubjectCorrespondenceTarget correspondence = target ->
    EffectSubjectCorrespondenceValid correspondence ->
    CheckedEffectSubjectRetarget
      index target (Some correspondence) effect
      (mkCheckedSemanticEffect
        (mkSemanticEffectIdentity
          (semanticEffectLabel (checkedSemanticEffectIdentity effect))
          (replaceEffectSubjectAt index target
            (semanticEffectSubjects (checkedSemanticEffectIdentity effect))))
        (checkedSemanticEffectRepresentationToken effect)).
Proof.
  intros index source target correspondence effect
    Hsource Hdistinct HcorrespondenceSource HcorrespondenceTarget Hvalid.
  econstructor; eauto.
Qed.

Theorem checked_retarget_preserves_effect_label :
  forall index target correspondence before after,
    CheckedEffectSubjectRetarget
      index target correspondence before after ->
    semanticEffectLabel (checkedSemanticEffectIdentity after) =
      semanticEffectLabel (checkedSemanticEffectIdentity before).
Proof.
  intros index target correspondence before after Hchecked.
  inversion Hchecked; subst; reflexivity.
Qed.

Theorem checked_retarget_preserves_representation_token :
  forall index target correspondence before after,
    CheckedEffectSubjectRetarget
      index target correspondence before after ->
    checkedSemanticEffectRepresentationToken after =
      checkedSemanticEffectRepresentationToken before.
Proof.
  intros index target correspondence before after Hchecked.
  inversion Hchecked; subst; reflexivity.
Qed.

Theorem changed_retarget_rebuilds_exact_subject_identity :
  forall index target correspondence before after,
    CheckedEffectSubjectRetarget
      index target (Some correspondence) before after ->
    checkedSemanticEffectIdentity after =
      mkSemanticEffectIdentity
        (semanticEffectLabel (checkedSemanticEffectIdentity before))
        (replaceEffectSubjectAt index target
          (semanticEffectSubjects (checkedSemanticEffectIdentity before))).
Proof.
  intros index target correspondence before after Hchecked.
  inversion Hchecked; subst.
  reflexivity.
Qed.
