From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

Definition SubjectId := nat.
Definition SubjectRebase := (SubjectId * SubjectId)%type.

Inductive SubjectFormula : Type :=
| SubjectRef : SubjectId -> SubjectFormula
| SubjectClosed : SubjectFormula
| SubjectPair : SubjectFormula -> SubjectFormula -> SubjectFormula
| SubjectBind : SubjectId -> SubjectFormula -> SubjectFormula.

Fixpoint formulaSupport
  (bound : list SubjectId)
  (formula : SubjectFormula) : list SubjectId :=
  match formula with
  | SubjectRef subject =>
      if in_dec Nat.eq_dec subject bound then [] else [subject]
  | SubjectClosed => []
  | SubjectPair lhs rhs =>
      formulaSupport bound lhs ++ formulaSupport bound rhs
  | SubjectBind subject body =>
      formulaSupport (subject :: bound) body
  end.

Theorem formula_support_excludes_bound_subjects :
  forall formula bound subject,
    In subject bound ->
    ~ In subject (formulaSupport bound formula).
Proof.
  induction formula as
    [ referenced
    |
    | lhs IHlhs rhs IHrhs
    | binder body IHbody ];
    intros bound subject Hbound; simpl.
  - destruct (in_dec Nat.eq_dec referenced bound) as [Hin | Hnotin].
    + intro Hsupport. inversion Hsupport.
    + intro Hsupport.
      simpl in Hsupport.
      destruct Hsupport as [Hequal | Hfalse].
      * subst subject. contradiction.
      * contradiction.
  - intro Hsupport. inversion Hsupport.
  - intro Hsupport.
    apply in_app_iff in Hsupport.
    destruct Hsupport as [Hleft | Hright].
    + eapply IHlhs; eauto.
    + eapply IHrhs; eauto.
  - eapply IHbody.
    + simpl. right. exact Hbound.
Qed.

Definition NoRebaseFrom
  (source : SubjectId)
  (rebases : list SubjectRebase) : Prop :=
  forall target, ~ In (source, target) rebases.

Inductive ExportSubject
  (survivors : list SubjectId)
  (rebases : list SubjectRebase)
  : SubjectId -> SubjectId -> Prop :=
| ExportSubject_survives :
    forall subject,
      In subject survivors ->
      ExportSubject survivors rebases subject subject
| ExportSubject_rebased :
    forall source target,
      ~ In source survivors ->
      In (source, target) rebases ->
      In target survivors ->
      ExportSubject survivors rebases source target.

Theorem exported_subject_is_supported :
  forall survivors rebases source target,
    ExportSubject survivors rebases source target ->
    In target survivors.
Proof.
  intros survivors rebases source target Hexport.
  inversion Hexport; subst; assumption.
Qed.

Inductive ExportSupport
  (survivors : list SubjectId)
  (rebases : list SubjectRebase)
  : list SubjectId -> list SubjectId -> Prop :=
| ExportSupport_nil :
    ExportSupport survivors rebases [] []
| ExportSupport_cons :
    forall source target sources targets,
      ExportSubject survivors rebases source target ->
      ExportSupport survivors rebases sources targets ->
      ExportSupport
        survivors rebases
        (source :: sources)
        (target :: targets).

Theorem exported_support_is_supported :
  forall survivors rebases sourceSupport exportedSupport,
    ExportSupport survivors rebases sourceSupport exportedSupport ->
    Forall (fun subject => In subject survivors) exportedSupport.
Proof.
  intros survivors rebases sourceSupport exportedSupport Hexport.
  induction Hexport.
  - constructor.
  - constructor.
    + eapply exported_subject_is_supported. exact H.
    + exact IHHexport.
Qed.

Theorem unsupported_subject_cannot_export :
  forall survivors rebases source target,
    ~ In source survivors ->
    NoRebaseFrom source rebases ->
    ~ ExportSubject survivors rebases source target.
Proof.
  intros survivors rebases source target HnotLive HnoRebase Hexport.
  inversion Hexport as
    [ subject Hin
    | source' target' HsourceNotLive Hpair HtargetLive ];
    subst.
  - contradiction.
  - eapply HnoRebase. exact Hpair.
Qed.

Lemma empty_rebase_has_no_source :
  forall source,
    NoRebaseFrom source [].
Proof.
  unfold NoRebaseFrom.
  intros source target Hin.
  inversion Hin.
Qed.

Theorem unsupported_subject_remains_unsupported_after_fresh_extension :
  forall survivors rebases source fresh target,
    source <> fresh ->
    ~ In source survivors ->
    NoRebaseFrom source rebases ->
    ~ ExportSubject (fresh :: survivors) rebases source target.
Proof.
  intros survivors rebases source fresh target
    Hdistinct HnotLive HnoRebase Hexport.
  inversion Hexport as
    [ subject Hin
    | source' target' HsourceNotLive Hpair HtargetLive ];
    subst.
  - simpl in Hin.
    destruct Hin as [Hequal | Hin].
    + apply Hdistinct. exact Hequal.
    + contradiction.
  - eapply HnoRebase. exact Hpair.
Qed.

Corollary fresh_distinct_subject_cannot_capture_unsupported_subject :
  forall survivors source fresh target,
    source <> fresh ->
    ~ In source survivors ->
    ~ ExportSubject (fresh :: survivors) [] source target.
Proof.
  intros survivors source fresh target Hdistinct HnotLive.
  eapply unsupported_subject_remains_unsupported_after_fresh_extension.
  - exact Hdistinct.
  - exact HnotLive.
  - apply empty_rebase_has_no_source.
Qed.

Theorem checked_rebase_exports_to_surviving_subject :
  forall survivors rebases source target,
    ~ In source survivors ->
    In (source, target) rebases ->
    In target survivors ->
    ExportSubject survivors rebases source target.
Proof.
  intros survivors rebases source target Hsource Hrebase Htarget.
  eapply ExportSubject_rebased; eauto.
Qed.

Inductive BranchSupportJoin
  (survivors : list SubjectId)
  (leftRebases rightRebases : list SubjectRebase)
  : list SubjectId -> list SubjectId -> list SubjectId -> Prop :=
| BranchSupportJoin_intro :
    forall leftSupport rightSupport joinedSupport,
      ExportSupport survivors leftRebases leftSupport joinedSupport ->
      ExportSupport survivors rightRebases rightSupport joinedSupport ->
      BranchSupportJoin
        survivors leftRebases rightRebases
        leftSupport rightSupport joinedSupport.

Theorem branch_join_has_common_logical_support :
  forall survivors leftRebases rightRebases
         leftSupport rightSupport joinedSupport,
    BranchSupportJoin
      survivors leftRebases rightRebases
      leftSupport rightSupport joinedSupport ->
    ExportSupport survivors leftRebases leftSupport joinedSupport /\
    ExportSupport survivors rightRebases rightSupport joinedSupport.
Proof.
  intros survivors leftRebases rightRebases
    leftSupport rightSupport joinedSupport Hjoin.
  inversion Hjoin; subst.
  split; assumption.
Qed.

Theorem branch_join_support_is_supported :
  forall survivors leftRebases rightRebases
         leftSupport rightSupport joinedSupport,
    BranchSupportJoin
      survivors leftRebases rightRebases
      leftSupport rightSupport joinedSupport ->
    Forall (fun subject => In subject survivors) joinedSupport.
Proof.
  intros survivors leftRebases rightRebases
    leftSupport rightSupport joinedSupport Hjoin.
  destruct
    (branch_join_has_common_logical_support
      survivors leftRebases rightRebases
      leftSupport rightSupport joinedSupport Hjoin)
    as [Hleft _].
  eapply exported_support_is_supported. exact Hleft.
Qed.

Theorem closed_support_joins :
  forall survivors leftRebases rightRebases,
    BranchSupportJoin
      survivors leftRebases rightRebases
      [] [] [].
Proof.
  intros survivors leftRebases rightRebases.
  constructor; constructor.
Qed.

Theorem independently_local_subjects_join_after_checked_rebase :
  forall survivors leftLocal rightLocal outer,
    ~ In leftLocal survivors ->
    ~ In rightLocal survivors ->
    In outer survivors ->
    BranchSupportJoin
      survivors
      [(leftLocal, outer)]
      [(rightLocal, outer)]
      [leftLocal]
      [rightLocal]
      [outer].
Proof.
  intros survivors leftLocal rightLocal outer
    HleftLocal HrightLocal Houter.
  constructor.
  - constructor.
    + eapply ExportSubject_rebased.
      * exact HleftLocal.
      * simpl. left. reflexivity.
      * exact Houter.
    + constructor.
  - constructor.
    + eapply ExportSubject_rebased.
      * exact HrightLocal.
      * simpl. left. reflexivity.
      * exact Houter.
    + constructor.
Qed.

Theorem unsupported_singleton_support_cannot_export :
  forall survivors source exportedSupport,
    ~ In source survivors ->
    ~ ExportSupport survivors [] [source] exportedSupport.
Proof.
  intros survivors source exportedSupport HnotLive Hexport.
  inversion Hexport as
    [
    | source' target sources targets Hsubject Hrest ];
    subst.
  apply
    (unsupported_subject_cannot_export
      survivors [] source target
      HnotLive
      (empty_rebase_has_no_source source)).
  exact Hsubject.
Qed.

Theorem unsupported_branch_local_subject_prevents_join :
  forall survivors rightRebases leftLocal rightSupport joinedSupport,
    ~ In leftLocal survivors ->
    ~ BranchSupportJoin
      survivors [] rightRebases
      [leftLocal] rightSupport joinedSupport.
Proof.
  intros survivors rightRebases leftLocal rightSupport joinedSupport
    HnotLive Hjoin.
  destruct
    (branch_join_has_common_logical_support
      survivors [] rightRebases
      [leftLocal] rightSupport joinedSupport Hjoin)
    as [Hleft _].
  apply
    (unsupported_singleton_support_cannot_export
      survivors leftLocal joinedSupport HnotLive).
  exact Hleft.
Qed.
