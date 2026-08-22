From Stdlib Require Import Arith.PeanoNat Bool.Bool.

(*
  PHIL-SYS-RUNTIME-001 — proof-oriented model of runtime-evidence and ADR-011
  cost/profile realization in Phil.Systems.Verify.

  Concrete runtime-site enumeration and textual cost-shape rendering remain
  implementation correspondence boundaries.  The model proves the verifier's
  authority rules: runtime sites cite selected RuntimeEnforced evidence for the
  same revision and declared cost; retained-runtime uses have exactly one site;
  diagnostics obey the compilation profile; copies carry copy cost; and
  RemoveCheck cannot discard runtime-enforced evidence.
*)

Definition EvidenceId := nat.
Definition RevisionId := nat.
Definition CostRef := nat.
Definition SiteKind := nat.

Inductive EvidenceKind : Type :=
| RuntimeEnforcedKind
| OtherEvidenceKind.

Record RuntimeEvidenceEnvironment : Type := mkRuntimeEvidenceEnvironment {
  runtimeEvidenceSelected : EvidenceId -> bool;
  runtimeEvidenceKind : EvidenceId -> option EvidenceKind;
  runtimeEvidenceRevision : EvidenceId -> option RevisionId;
  runtimeEvidenceDeclaresCost : EvidenceId -> CostRef -> bool;
  runtimeExpectedSiteKind : EvidenceId -> option SiteKind
}.

Record RuntimeSite : Type := mkRuntimeSite {
  runtimeSiteEvidence : EvidenceId;
  runtimeSiteRevision : RevisionId;
  runtimeSiteCost : CostRef;
  runtimeSiteKind : SiteKind
}.

Definition RuntimeSiteVerificationSuccess
  (environment : RuntimeEvidenceEnvironment)
  (site : RuntimeSite) : Prop :=
  runtimeEvidenceSelected environment (runtimeSiteEvidence site) = true /\
  runtimeEvidenceKind environment (runtimeSiteEvidence site) =
    Some RuntimeEnforcedKind /\
  runtimeEvidenceRevision environment (runtimeSiteEvidence site) =
    Some (runtimeSiteRevision site) /\
  runtimeEvidenceDeclaresCost environment
    (runtimeSiteEvidence site) (runtimeSiteCost site) = true /\
  match runtimeExpectedSiteKind environment (runtimeSiteEvidence site) with
  | Some expected => expected = runtimeSiteKind site
  | None => True
  end.

Theorem verified_runtime_site_uses_selected_evidence :
  forall environment site,
    RuntimeSiteVerificationSuccess environment site ->
    runtimeEvidenceSelected environment (runtimeSiteEvidence site) = true.
Proof.
  intros environment site Hverified.
  destruct Hverified as [Hselected _].
  exact Hselected.
Qed.

Theorem verified_runtime_site_requires_runtime_enforced_kind :
  forall environment site,
    RuntimeSiteVerificationSuccess environment site ->
    runtimeEvidenceKind environment (runtimeSiteEvidence site) =
      Some RuntimeEnforcedKind.
Proof.
  intros environment site Hverified.
  destruct Hverified as [_ [Hkind _]].
  exact Hkind.
Qed.

Theorem verified_runtime_site_preserves_revision :
  forall environment site,
    RuntimeSiteVerificationSuccess environment site ->
    runtimeEvidenceRevision environment (runtimeSiteEvidence site) =
      Some (runtimeSiteRevision site).
Proof.
  intros environment site Hverified.
  destruct Hverified as [_ [_ [Hrevision _]]].
  exact Hrevision.
Qed.

Theorem verified_runtime_site_uses_declared_cost :
  forall environment site,
    RuntimeSiteVerificationSuccess environment site ->
    runtimeEvidenceDeclaresCost environment
      (runtimeSiteEvidence site) (runtimeSiteCost site) = true.
Proof.
  intros environment site Hverified.
  destruct Hverified as [_ [_ [_ [Hcost _]]]].
  exact Hcost.
Qed.

Theorem specified_runtime_site_kind_is_exact :
  forall environment site expected,
    RuntimeSiteVerificationSuccess environment site ->
    runtimeExpectedSiteKind environment (runtimeSiteEvidence site) = Some expected ->
    expected = runtimeSiteKind site.
Proof.
  intros environment site expected Hverified Hexpected.
  destruct Hverified as [_ [_ [_ [_ Hkind]]]].
  rewrite Hexpected in Hkind.
  exact Hkind.
Qed.

Record RetainedRuntimeUseModel : Type := mkRetainedRuntimeUseModel {
  retainedMatchingSiteCount : nat
}.

Definition RetainedRuntimeUseVerificationSuccess
  (use : RetainedRuntimeUseModel) : Prop :=
  retainedMatchingSiteCount use = 1.

Theorem verified_retained_runtime_use_has_exactly_one_site :
  forall use,
    RetainedRuntimeUseVerificationSuccess use ->
    retainedMatchingSiteCount use = 1.
Proof.
  intros use Hverified.
  exact Hverified.
Qed.

Theorem retained_runtime_use_with_no_site_is_rejected :
  forall use,
    retainedMatchingSiteCount use = 0 ->
    ~ RetainedRuntimeUseVerificationSuccess use.
Proof.
  intros use Hnone Hverified.
  unfold RetainedRuntimeUseVerificationSuccess in Hverified.
  rewrite Hnone in Hverified.
  discriminate.
Qed.

Theorem retained_runtime_use_with_duplicate_sites_is_rejected :
  forall use count,
    retainedMatchingSiteCount use = S (S count) ->
    ~ RetainedRuntimeUseVerificationSuccess use.
Proof.
  intros use count Hduplicates Hverified.
  unfold RetainedRuntimeUseVerificationSuccess in Hverified.
  rewrite Hduplicates in Hverified.
  discriminate.
Qed.

Inductive CompilationProfile : Type :=
| CheckedRuntimeProfile
| CertifiedReleaseProfile.

Inductive CostClass : Type :=
| DefensiveProfileCost
| OtherCostClass.

Definition DiagnosticVerificationSuccess
  (profile : CompilationProfile)
  (costClass : CostClass) : Prop :=
  match profile with
  | CertifiedReleaseProfile => False
  | CheckedRuntimeProfile => costClass = DefensiveProfileCost
  end.

Theorem certified_release_has_no_verified_diagnostic :
  forall costClass,
    ~ DiagnosticVerificationSuccess CertifiedReleaseProfile costClass.
Proof.
  intros costClass Hverified.
  exact Hverified.
Qed.

Theorem checked_runtime_diagnostic_requires_defensive_cost :
  forall costClass,
    DiagnosticVerificationSuccess CheckedRuntimeProfile costClass ->
    costClass = DefensiveProfileCost.
Proof.
  intros costClass Hverified.
  exact Hverified.
Qed.

Inductive LoweringAction : Type :=
| CopyAction
| RemoveCheckAction
| OtherAction.

Record CopyDecisionModel : Type := mkCopyDecisionModel {
  copyDecisionAction : LoweringAction;
  copyByteCostPresent : bool
}.

Definition CopyVerificationSuccess (decision : CopyDecisionModel) : Prop :=
  copyDecisionAction decision = CopyAction /\
  copyByteCostPresent decision = true.

Theorem verified_copy_requires_copy_lowering_decision :
  forall decision,
    CopyVerificationSuccess decision ->
    copyDecisionAction decision = CopyAction.
Proof.
  intros decision Hverified.
  destruct Hverified as [Haction _].
  exact Haction.
Qed.

Theorem verified_copy_has_explicit_byte_cost :
  forall decision,
    CopyVerificationSuccess decision ->
    copyByteCostPresent decision = true.
Proof.
  intros decision Hverified.
  destruct Hverified as [_ Hcost].
  exact Hcost.
Qed.

Record RemoveCheckModel : Type := mkRemoveCheckModel {
  removeCheckReferences : EvidenceId -> bool;
  removeCheckEvidenceKind : EvidenceId -> EvidenceKind
}.

Definition RemoveCheckVerificationSuccess (decision : RemoveCheckModel) : Prop :=
  forall evidence,
    removeCheckReferences decision evidence = true ->
    removeCheckEvidenceKind decision evidence <> RuntimeEnforcedKind.

Theorem verified_remove_check_cannot_drop_runtime_enforced_evidence :
  forall decision evidence,
    RemoveCheckVerificationSuccess decision ->
    removeCheckReferences decision evidence = true ->
    removeCheckEvidenceKind decision evidence = RuntimeEnforcedKind ->
    False.
Proof.
  intros decision evidence Hverified Hreferenced Hruntime.
  pose proof (Hverified evidence Hreferenced) as HnotRuntime.
  apply HnotRuntime.
  exact Hruntime.
Qed.
