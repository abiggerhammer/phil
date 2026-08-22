From Stdlib Require Import Strings.String Lists.List Bool.Bool.
Import ListNotations.

Open Scope string_scope.

Definition ObligationId := string.
Definition CanonicalProp := string.
Definition RequiredPoint := string.
Definition EvidenceName := string.
Definition Certificate := string.

Record Obligation : Type := mkObligation
  { obligationId : ObligationId
  ; obligationProp : CanonicalProp
  ; obligationPoint : RequiredPoint
  }.

Record RuntimeBinding : Type := mkRuntimeBinding
  { runtimeId : ObligationId
  ; runtimeProp : CanonicalProp
  ; runtimePoint : RequiredPoint
  }.

Record ExportBinding : Type := mkExportBinding
  { exportId : ObligationId
  ; exportProp : CanonicalProp
  ; exportPoint : RequiredPoint
  }.

Parameter proposeCertificate : CanonicalProp -> option Certificate.
Parameter checkCertificate : CanonicalProp -> Certificate -> bool.

Inductive DecisionOutcome : Type :=
| DecisionStaticCertificate : Certificate -> DecisionOutcome
| DecisionNeedsExplicitMechanism : DecisionOutcome
| DecisionInvalidProducedCertificate : Certificate -> DecisionOutcome.

Definition decisionStage (proposition : CanonicalProp) : DecisionOutcome :=
  match proposeCertificate proposition with
  | None => DecisionNeedsExplicitMechanism
  | Some certificate =>
      if checkCertificate proposition certificate then
        DecisionStaticCertificate certificate
      else
        DecisionInvalidProducedCertificate certificate
  end.

(* PHIL-DISCH-CERT-001 *)
Theorem static_certificate_requires_checker_acceptance :
  forall proposition certificate,
    decisionStage proposition = DecisionStaticCertificate certificate ->
    proposeCertificate proposition = Some certificate /\
    checkCertificate proposition certificate = true.
Proof.
  intros proposition certificate Hstage.
  unfold decisionStage in Hstage.
  destruct (proposeCertificate proposition) as [proposed |] eqn:Hpropose.
  - destruct (checkCertificate proposition proposed) eqn:Hcheck.
    + inversion Hstage; subst proposed.
      split.
      * reflexivity.
      * exact Hcheck.
    + discriminate.
  - discriminate.
Qed.

Theorem no_proposal_requires_explicit_mechanism :
  forall proposition,
    proposeCertificate proposition = None ->
    decisionStage proposition = DecisionNeedsExplicitMechanism.
Proof.
  intros proposition Hnone.
  unfold decisionStage.
  now rewrite Hnone.
Qed.

Theorem rejected_proposal_never_static :
  forall proposition certificate,
    proposeCertificate proposition = Some certificate ->
    checkCertificate proposition certificate = false ->
    decisionStage proposition = DecisionInvalidProducedCertificate certificate.
Proof.
  intros proposition certificate Hpropose Hreject.
  unfold decisionStage.
  now rewrite Hpropose, Hreject.
Qed.

Inductive StaticDischarge : Type :=
| StaticByDefinition : StaticDischarge
| StaticByEvidence : EvidenceName -> StaticDischarge
| StaticByCertificate : Certificate -> StaticDischarge.

Inductive ObligationDisposition : Type :=
| StaticallyDischarged : StaticDischarge -> ObligationDisposition
| RuntimeBound : RuntimeBinding -> ObligationDisposition
| Exported : ExportBinding -> ObligationDisposition.

Definition ExactRuntimeBinding
  (obligation : Obligation) (binding : RuntimeBinding) : Prop :=
  runtimeId binding = obligationId obligation /\
  runtimeProp binding = obligationProp obligation /\
  runtimePoint binding = obligationPoint obligation.

Definition ExactExportBinding
  (obligation : Obligation) (binding : ExportBinding) : Prop :=
  exportId binding = obligationId obligation /\
  exportProp binding = obligationProp obligation /\
  exportPoint binding = obligationPoint obligation.

Inductive ResolutionSuccess : Obligation -> ObligationDisposition -> Prop :=
| Resolution_definition :
    forall obligation,
      ResolutionSuccess obligation (StaticallyDischarged StaticByDefinition)
| Resolution_evidence :
    forall obligation evidenceName,
      ResolutionSuccess obligation
        (StaticallyDischarged (StaticByEvidence evidenceName))
| Resolution_certificate :
    forall obligation certificate,
      checkCertificate (obligationProp obligation) certificate = true ->
      ResolutionSuccess obligation
        (StaticallyDischarged (StaticByCertificate certificate))
| Resolution_runtime :
    forall obligation binding,
      ExactRuntimeBinding obligation binding ->
      ResolutionSuccess obligation (RuntimeBound binding)
| Resolution_export :
    forall obligation binding,
      ExactExportBinding obligation binding ->
      ResolutionSuccess obligation (Exported binding).

(* PHIL-DISCH-BOUNDARY-001 *)
Theorem resolution_disposition_exact :
  forall obligation disposition,
    ResolutionSuccess obligation disposition ->
    disposition = StaticallyDischarged StaticByDefinition \/
    (exists evidenceName,
      disposition = StaticallyDischarged (StaticByEvidence evidenceName)) \/
    (exists certificate,
      disposition = StaticallyDischarged (StaticByCertificate certificate) /\
      checkCertificate (obligationProp obligation) certificate = true) \/
    (exists binding,
      disposition = RuntimeBound binding /\
      ExactRuntimeBinding obligation binding) \/
    (exists binding,
      disposition = Exported binding /\
      ExactExportBinding obligation binding).
Proof.
  intros obligation disposition Hresolution.
  destruct Hresolution as
    [ obligation
    | obligation evidenceName
    | obligation certificate Hcheck
    | obligation binding Hexact
    | obligation binding Hexact ].
  - left. reflexivity.
  - right. left. exists evidenceName. reflexivity.
  - right. right. left.
    exists certificate. split.
    + reflexivity.
    + exact Hcheck.
  - right. right. right. left.
    exists binding. split.
    + reflexivity.
    + exact Hexact.
  - right. right. right. right.
    exists binding. split.
    + reflexivity.
    + exact Hexact.
Qed.

Theorem runtime_resolution_requires_exact_identity :
  forall obligation binding,
    ResolutionSuccess obligation (RuntimeBound binding) ->
    ExactRuntimeBinding obligation binding.
Proof.
  intros obligation binding Hresolution.
  inversion Hresolution; subst; assumption.
Qed.

Theorem export_resolution_requires_exact_identity :
  forall obligation binding,
    ResolutionSuccess obligation (Exported binding) ->
    ExactExportBinding obligation binding.
Proof.
  intros obligation binding Hresolution.
  inversion Hresolution; subst; assumption.
Qed.

Inductive PrerequisiteDisposition : Type :=
| PrerequisiteLocal : CanonicalProp -> PrerequisiteDisposition
| PrerequisiteExported : CanonicalProp -> PrerequisiteDisposition.

Definition prerequisiteAssumption
  (disposition : PrerequisiteDisposition) : option CanonicalProp :=
  match disposition with
  | PrerequisiteLocal proposition => Some proposition
  | PrerequisiteExported _ => None
  end.

Fixpoint allPrerequisitesLocal
  (dispositions : list PrerequisiteDisposition) : bool :=
  match dispositions with
  | [] => true
  | PrerequisiteLocal _ :: rest => allPrerequisitesLocal rest
  | PrerequisiteExported _ :: _ => false
  end.

Definition ParentLocallyResolvable
  (dispositions : list PrerequisiteDisposition) : Prop :=
  allPrerequisitesLocal dispositions = true.

(* PHIL-DISCH-PREREQ-001 *)
Theorem exported_prerequisite_is_not_local_assumption :
  forall proposition,
    prerequisiteAssumption (PrerequisiteExported proposition) = None.
Proof.
  reflexivity.
Qed.

Theorem local_prerequisite_becomes_assumption :
  forall proposition,
    prerequisiteAssumption (PrerequisiteLocal proposition) = Some proposition.
Proof.
  reflexivity.
Qed.

Lemma exported_prerequisite_makes_allLocal_false :
  forall dispositions proposition,
    In (PrerequisiteExported proposition) dispositions ->
    allPrerequisitesLocal dispositions = false.
Proof.
  induction dispositions as [| disposition rest IH]; intros proposition Hin.
  - contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst disposition. reflexivity.
    + destruct disposition as [localProp | exportedProp].
      * simpl. apply IH with (proposition := proposition). exact Hin.
      * reflexivity.
Qed.

Theorem exported_prerequisite_blocks_local_parent :
  forall dispositions proposition,
    In (PrerequisiteExported proposition) dispositions ->
    ~ ParentLocallyResolvable dispositions.
Proof.
  intros dispositions proposition Hexport Hlocal.
  unfold ParentLocallyResolvable in Hlocal.
  pose proof
    (exported_prerequisite_makes_allLocal_false
      dispositions proposition Hexport) as Hfalse.
  rewrite Hfalse in Hlocal.
  discriminate.
Qed.
