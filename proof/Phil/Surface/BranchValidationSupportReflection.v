From Stdlib Require Import Lists.List Arith.PeanoNat.
From Phil.Surface Require Import BranchEvidenceSupport.

Import ListNotations.

(*
  P-BRANCH-SUPPORT-REFLECTION-01 — validation-decision tranche.

  The production repair in #1350 changed the native Surface support walk so a
  ValidationDecision contributes both the validation context and validated
  subject before branch-local bindings are pruned.  The accepted elimination
  later materializes TyValidated over those same two logical subjects.

  This proof-correspondence slice connects that repaired producer shape to the
  existing BranchEvidenceSupport model.  It deliberately covers only the
  validation-decision route; digest, recognition, provider and callable
  decision correspondence remain separate successor work.
*)

Definition ValidationDecisionNativeSupport
  (context subject : SubjectId) : list SubjectId :=
  [context; subject].

Definition MaterializedValidatedEvidenceSupport
  (context subject : SubjectId) : list SubjectId :=
  [context; subject].

Definition PreviousDecisionShapeSupport : list SubjectId := [].

Definition SupportReflects
  (producerSupport exposedSupport : list SubjectId) : Prop :=
  forall logicalSubject,
    In logicalSubject exposedSupport ->
    In logicalSubject producerSupport.

Theorem repaired_validation_support_reflects_materialized_evidence :
  forall context subject,
    SupportReflects
      (ValidationDecisionNativeSupport context subject)
      (MaterializedValidatedEvidenceSupport context subject).
Proof.
  intros context subject logicalSubject Hin.
  exact Hin.
Qed.

Theorem previous_empty_shape_support_does_not_reflect_validation_evidence :
  forall context subject,
    ~ SupportReflects
        PreviousDecisionShapeSupport
        (MaterializedValidatedEvidenceSupport context subject).
Proof.
  intros context subject Hreflect.
  unfold SupportReflects in Hreflect.
  specialize (Hreflect context).
  assert (Hin : In context (MaterializedValidatedEvidenceSupport context subject)).
  {
    unfold MaterializedValidatedEvidenceSupport.
    simpl. left. reflexivity.
  }
  specialize (Hreflect Hin).
  inversion Hreflect.
Qed.

Theorem previous_empty_shape_support_is_vacuously_exportable :
  forall survivors,
    ExportSupport survivors [] PreviousDecisionShapeSupport [].
Proof.
  intros survivors.
  constructor.
Qed.

Lemma export_support_cons_inv :
  forall survivors rebases source sources exported,
    ExportSupport survivors rebases (source :: sources) exported ->
    exists target targets,
      exported = target :: targets /\
      ExportSubject survivors rebases source target /\
      ExportSupport survivors rebases sources targets.
Proof.
  intros survivors rebases source sources exported Hexport.
  inversion Hexport as
    [
    | source' target sources' targets Hsubject Htail ];
    subst.
  exists target, targets.
  repeat split; assumption || reflexivity.
Qed.

Theorem validation_support_exports_when_both_subjects_survive :
  forall survivors context subject,
    In context survivors ->
    In subject survivors ->
    ExportSupport
      survivors []
      (ValidationDecisionNativeSupport context subject)
      [context; subject].
Proof.
  intros survivors context subject Hcontext Hsubject.
  unfold ValidationDecisionNativeSupport.
  constructor.
  - apply ExportSubject_survives. exact Hcontext.
  - constructor.
    + apply ExportSubject_survives. exact Hsubject.
    + constructor.
Qed.

Theorem validation_subject_cannot_escape_when_subject_dies :
  forall survivors context subject exported,
    ~ In subject survivors ->
    ~ ExportSupport
        survivors []
        (ValidationDecisionNativeSupport context subject)
        exported.
Proof.
  intros survivors context subject exported HnotLive Hexport.
  unfold ValidationDecisionNativeSupport in Hexport.
  destruct
    (export_support_cons_inv
      survivors [] context [subject] exported Hexport)
    as [contextTarget [tail [Hexposed [_ Hrest]]]].
  destruct
    (export_support_cons_inv
      survivors [] subject [] tail Hrest)
    as [subjectTarget [finalTail [_ [HsubjectExport _]]]].
  apply
    (unsupported_subject_cannot_export
      survivors [] subject subjectTarget
      HnotLive
      (empty_rebase_has_no_source subject)).
  exact HsubjectExport.
Qed.

Theorem fresh_spelling_reuse_does_not_authorize_old_validation_subject :
  forall survivors context subject fresh exported,
    subject <> fresh ->
    ~ In subject survivors ->
    ~ ExportSupport
        (fresh :: survivors) []
        (ValidationDecisionNativeSupport context subject)
        exported.
Proof.
  intros survivors context subject fresh exported Hdistinct HnotLive.
  apply validation_subject_cannot_escape_when_subject_dies.
  intro Hin.
  simpl in Hin.
  destruct Hin as [Hequal | Hin].
  - apply Hdistinct. symmetry. exact Hequal.
  - contradiction.
Qed.

Theorem exported_validation_support_also_covers_materialized_evidence :
  forall survivors context subject exported,
    ExportSupport
      survivors []
      (ValidationDecisionNativeSupport context subject)
      exported ->
    ExportSupport
      survivors []
      (MaterializedValidatedEvidenceSupport context subject)
      exported.
Proof.
  intros survivors context subject exported Hexport.
  exact Hexport.
Qed.
