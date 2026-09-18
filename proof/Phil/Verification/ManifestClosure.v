From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Assurance Require Import Manifest ValidityScope.
From Phil.Verification Require Import VerificationWorkflow.

(*
  PHIL-P1-MANIFEST-001 — witness-neutral VerificationBundle to
  AssuranceManifest closure.

  This theorem family starts after intrinsic verification has produced an exact
  VerificationBundle. It certifies the source-assurance closure boundary:
  exact obligation-domain/policy/architecture binding; explicit permitted
  evidence/runtime/assumption/export dispositions; exact current-ledger
  evidence identity and obligation revision; explicit assumption dependencies;
  validity-scope matching; and no silent inheritance of evidence absent from
  the current bundle/ledger.

  Concrete Text/Digest/Map/Set representation, SHA-256, manifest-id
  construction, provider/external evidence truth, and Haskell/Rocq toolchain
  correctness remain explicit correspondence/TCB boundaries.
*)

Definition P1PolicyRevision := nat.
Definition P1ArchitectureIdentity := nat.
Definition P1RevisionSet := nat -> bool.
Definition P1EvidenceKey := nat.
Definition P1AssumptionKey := nat.
Definition P1ExportKey := nat.

Record P1BundleFacts : Type := mkP1BundleFacts {
  p1BundleIntrinsicAccepted : bool;
  p1BundlePolicyRevision : P1PolicyRevision;
  p1BundleArchitectureIdentity : P1ArchitectureIdentity;
  p1BundleRevisions : P1RevisionSet;
  p1BundleAcceptedEvidence : P1EvidenceKey -> bool
}.

Record P1EvidenceFacts : Type := mkP1EvidenceFacts {
  p1EvidenceCurrentLedger : bool;
  p1EvidenceSelected : bool;
  p1EvidenceAccepted : bool;
  p1EvidenceTargetRevision : nat;
  p1EvidenceRuntimeEnforced : bool;
  p1EvidenceScope : ValidityMap;
  p1EvidenceAssumptionDependencies : P1AssumptionKey -> bool
}.

Record P1AssumptionFacts : Type := mkP1AssumptionFacts {
  p1AssumptionCurrentLedger : bool;
  p1AssumptionSelected : bool;
  p1AssumptionScope : ValidityMap
}.

Record P1ExportFacts : Type := mkP1ExportFacts {
  p1ExportCurrentLedger : bool;
  p1ExportSelected : bool;
  p1ExportPermitted : bool;
  p1ExportScope : ValidityMap
}.

Definition P1EvidenceEnvironment := P1EvidenceKey -> option P1EvidenceFacts.
Definition P1AssumptionEnvironment := P1AssumptionKey -> option P1AssumptionFacts.
Definition P1ExportEnvironment := P1ExportKey -> option P1ExportFacts.

Inductive P1ManifestDisposition : Type :=
| P1EvidenceDisposition : P1EvidenceKey -> P1ManifestDisposition
| P1RuntimeDisposition : P1EvidenceKey -> P1ManifestDisposition
| P1AssumptionDisposition : P1AssumptionKey -> P1ManifestDisposition
| P1ExportDisposition : P1ExportKey -> P1ManifestDisposition.

Record P1ManifestFacts : Type := mkP1ManifestFacts {
  p1ManifestPolicyRevision : P1PolicyRevision;
  p1ManifestArchitectureIdentity : P1ArchitectureIdentity;
  p1ManifestRevisions : P1RevisionSet;
  p1ManifestCertificationScope : P1RevisionSet;
  p1ManifestDisposition : nat -> option P1ManifestDisposition;
  p1ManifestEffectiveValidity : ValidityMap
}.

Record P1ManifestEnvironment : Type := mkP1ManifestEnvironment {
  p1ManifestEvidence : P1EvidenceEnvironment;
  p1ManifestAssumptions : P1AssumptionEnvironment;
  p1ManifestExports : P1ExportEnvironment
}.

Definition P1EvidenceValidFor
  (bundle : P1BundleFacts)
  (manifest : P1ManifestFacts)
  (environment : P1ManifestEnvironment)
  (revision : nat)
  (evidence : P1EvidenceKey)
  (runtimeRequired : bool) : Prop :=
  exists facts,
    p1ManifestEvidence environment evidence = Some facts /\
    p1EvidenceCurrentLedger facts = true /\
    p1EvidenceSelected facts = true /\
    p1EvidenceAccepted facts = true /\
    p1BundleAcceptedEvidence bundle evidence = true /\
    p1EvidenceTargetRevision facts = revision /\
    p1EvidenceRuntimeEnforced facts = runtimeRequired /\
    ScopeMatches
      (p1EvidenceScope facts)
      (p1ManifestEffectiveValidity manifest).

Definition P1AssumptionValid
  (manifest : P1ManifestFacts)
  (environment : P1ManifestEnvironment)
  (assumption : P1AssumptionKey) : Prop :=
  exists facts,
    p1ManifestAssumptions environment assumption = Some facts /\
    p1AssumptionCurrentLedger facts = true /\
    p1AssumptionSelected facts = true /\
    ScopeMatches
      (p1AssumptionScope facts)
      (p1ManifestEffectiveValidity manifest).

Definition P1ExportValid
  (manifest : P1ManifestFacts)
  (environment : P1ManifestEnvironment)
  (exportKey : P1ExportKey) : Prop :=
  exists facts,
    p1ManifestExports environment exportKey = Some facts /\
    p1ExportCurrentLedger facts = true /\
    p1ExportSelected facts = true /\
    p1ExportPermitted facts = true /\
    ScopeMatches
      (p1ExportScope facts)
      (p1ManifestEffectiveValidity manifest).

Definition P1DispositionValid
  (bundle : P1BundleFacts)
  (manifest : P1ManifestFacts)
  (environment : P1ManifestEnvironment)
  (revision : nat)
  (disposition : P1ManifestDisposition) : Prop :=
  match disposition with
  | P1EvidenceDisposition evidence =>
      P1EvidenceValidFor bundle manifest environment revision evidence false
  | P1RuntimeDisposition evidence =>
      P1EvidenceValidFor bundle manifest environment revision evidence true
  | P1AssumptionDisposition assumption =>
      P1AssumptionValid manifest environment assumption
  | P1ExportDisposition exportKey =>
      P1ExportValid manifest environment exportKey
  end.

Definition P1SelectedEvidenceAssumptionsExplicit
  (manifest : P1ManifestFacts)
  (environment : P1ManifestEnvironment) : Prop :=
  forall evidence evidenceFacts assumption,
    p1ManifestEvidence environment evidence = Some evidenceFacts ->
    p1EvidenceSelected evidenceFacts = true ->
    p1EvidenceAssumptionDependencies evidenceFacts assumption = true ->
    P1AssumptionValid manifest environment assumption.

Definition P1NoUnusedSelectedAssumptions
  (environment : P1ManifestEnvironment) : Prop :=
  forall assumption assumptionFacts,
    p1ManifestAssumptions environment assumption = Some assumptionFacts ->
    p1AssumptionSelected assumptionFacts = true ->
    exists evidence evidenceFacts,
      p1ManifestEvidence environment evidence = Some evidenceFacts /\
      p1EvidenceSelected evidenceFacts = true /\
      p1EvidenceAssumptionDependencies evidenceFacts assumption = true.

Definition P1ManifestClosureValid
  (bundle : P1BundleFacts)
  (manifest : P1ManifestFacts)
  (environment : P1ManifestEnvironment) : Prop :=
  p1BundleIntrinsicAccepted bundle = true /\
  p1ManifestPolicyRevision manifest = p1BundlePolicyRevision bundle /\
  p1ManifestArchitectureIdentity manifest =
    p1BundleArchitectureIdentity bundle /\
  SameRevisionSet
    (p1BundleRevisions bundle)
    (p1ManifestRevisions manifest) /\
  (forall revision,
    p1ManifestCertificationScope manifest revision = true ->
    p1ManifestRevisions manifest revision = true) /\
  (forall revision,
    p1ManifestRevisions manifest revision = true ->
    exists disposition,
      p1ManifestDisposition manifest revision = Some disposition /\
      P1DispositionValid bundle manifest environment revision disposition) /\
  P1SelectedEvidenceAssumptionsExplicit manifest environment /\
  P1NoUnusedSelectedAssumptions environment.

Theorem accepted_manifest_requires_intrinsic_acceptance :
  forall bundle manifest environment,
    P1ManifestClosureValid bundle manifest environment ->
    p1BundleIntrinsicAccepted bundle = true.
Proof.
  intros bundle manifest environment Hvalid.
  exact (proj1 Hvalid).
Qed.

Theorem accepted_manifest_preserves_exact_policy :
  forall bundle manifest environment,
    P1ManifestClosureValid bundle manifest environment ->
    p1ManifestPolicyRevision manifest = p1BundlePolicyRevision bundle.
Proof.
  intros bundle manifest environment Hvalid.
  exact (proj1 (proj2 Hvalid)).
Qed.

Theorem accepted_manifest_preserves_exact_architecture :
  forall bundle manifest environment,
    P1ManifestClosureValid bundle manifest environment ->
    p1ManifestArchitectureIdentity manifest =
      p1BundleArchitectureIdentity bundle.
Proof.
  intros bundle manifest environment Hvalid.
  exact (proj1 (proj2 (proj2 Hvalid))).
Qed.

Theorem accepted_manifest_covers_exact_bundle_obligation_domain :
  forall bundle manifest environment,
    P1ManifestClosureValid bundle manifest environment ->
    SameRevisionSet
      (p1BundleRevisions bundle)
      (p1ManifestRevisions manifest).
Proof.
  intros bundle manifest environment Hvalid.
  exact (proj1 (proj2 (proj2 (proj2 Hvalid)))).
Qed.

Theorem accepted_manifest_scope_is_inside_exact_domain :
  forall bundle manifest environment revision,
    P1ManifestClosureValid bundle manifest environment ->
    p1ManifestCertificationScope manifest revision = true ->
    p1ManifestRevisions manifest revision = true.
Proof.
  intros bundle manifest environment revision Hvalid Hscope.
  destruct Hvalid as [_ [_ [_ [_ [Hinside _]]]]].
  eapply Hinside.
  exact Hscope.
Qed.

Theorem accepted_manifest_every_revision_has_explicit_valid_disposition :
  forall bundle manifest environment revision,
    P1ManifestClosureValid bundle manifest environment ->
    p1ManifestRevisions manifest revision = true ->
    exists disposition,
      p1ManifestDisposition manifest revision = Some disposition /\
      P1DispositionValid bundle manifest environment revision disposition.
Proof.
  intros bundle manifest environment revision Hvalid Hrevision.
  destruct Hvalid as [_ [_ [_ [_ [_ [Hcoverage _]]]]]].
  eapply Hcoverage.
  exact Hrevision.
Qed.

Theorem evidence_disposition_requires_current_exact_accepted_reference :
  forall bundle manifest environment revision evidence,
    P1DispositionValid bundle manifest environment revision
      (P1EvidenceDisposition evidence) ->
    exists facts,
      p1ManifestEvidence environment evidence = Some facts /\
      p1EvidenceCurrentLedger facts = true /\
      p1EvidenceSelected facts = true /\
      p1EvidenceAccepted facts = true /\
      p1BundleAcceptedEvidence bundle evidence = true /\
      p1EvidenceTargetRevision facts = revision /\
      ScopeMatches
        (p1EvidenceScope facts)
        (p1ManifestEffectiveValidity manifest).
Proof.
  intros bundle manifest environment revision evidence Hvalid.
  unfold P1DispositionValid, P1EvidenceValidFor in Hvalid.
  destruct Hvalid as
    [facts [Hlookup [Hledger [Hselected [Haccepted
      [Hbundle [Hrevision [_ Hscope]]]]]]]].
  exists facts.
  repeat split; assumption.
Qed.

Theorem runtime_disposition_requires_exact_runtime_evidence :
  forall bundle manifest environment revision evidence,
    P1DispositionValid bundle manifest environment revision
      (P1RuntimeDisposition evidence) ->
    exists facts,
      p1ManifestEvidence environment evidence = Some facts /\
      p1EvidenceCurrentLedger facts = true /\
      p1EvidenceSelected facts = true /\
      p1EvidenceAccepted facts = true /\
      p1BundleAcceptedEvidence bundle evidence = true /\
      p1EvidenceTargetRevision facts = revision /\
      p1EvidenceRuntimeEnforced facts = true /\
      ScopeMatches
        (p1EvidenceScope facts)
        (p1ManifestEffectiveValidity manifest).
Proof.
  intros bundle manifest environment revision evidence Hvalid.
  exact Hvalid.
Qed.

Theorem assumption_disposition_is_explicit_and_validity_scoped :
  forall bundle manifest environment revision assumption,
    P1DispositionValid bundle manifest environment revision
      (P1AssumptionDisposition assumption) ->
    P1AssumptionValid manifest environment assumption.
Proof.
  intros.
  exact H.
Qed.

Theorem export_disposition_is_explicit_permitted_and_validity_scoped :
  forall bundle manifest environment revision exportKey,
    P1DispositionValid bundle manifest environment revision
      (P1ExportDisposition exportKey) ->
    P1ExportValid manifest environment exportKey.
Proof.
  intros.
  exact H.
Qed.

Theorem selected_evidence_assumption_dependencies_are_explicit :
  forall bundle manifest environment evidence evidenceFacts assumption,
    P1ManifestClosureValid bundle manifest environment ->
    p1ManifestEvidence environment evidence = Some evidenceFacts ->
    p1EvidenceSelected evidenceFacts = true ->
    p1EvidenceAssumptionDependencies evidenceFacts assumption = true ->
    P1AssumptionValid manifest environment assumption.
Proof.
  intros bundle manifest environment evidence evidenceFacts assumption
    Hvalid Hlookup Hselected Hdependency.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [Hexplicit _]]]]]]].
  eapply Hexplicit; eauto.
Qed.

Theorem selected_assumption_cannot_be_unused :
  forall bundle manifest environment assumption assumptionFacts,
    P1ManifestClosureValid bundle manifest environment ->
    p1ManifestAssumptions environment assumption = Some assumptionFacts ->
    p1AssumptionSelected assumptionFacts = true ->
    exists evidence evidenceFacts,
      p1ManifestEvidence environment evidence = Some evidenceFacts /\
      p1EvidenceSelected evidenceFacts = true /\
      p1EvidenceAssumptionDependencies evidenceFacts assumption = true.
Proof.
  intros bundle manifest environment assumption assumptionFacts
    Hvalid Hlookup Hselected.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ Hused]]]]]]].
  eapply Hused; eauto.
Qed.

Theorem evidence_absent_from_current_bundle_cannot_close :
  forall bundle manifest environment revision evidence runtimeRequired,
    p1BundleAcceptedEvidence bundle evidence = false ->
    ~ P1EvidenceValidFor
        bundle manifest environment revision evidence runtimeRequired.
Proof.
  intros bundle manifest environment revision evidence runtimeRequired
    Habsent Hvalid.
  destruct Hvalid as
    [facts [_ [_ [_ [_ [Hbundle _]]]]]].
  rewrite Habsent in Hbundle.
  discriminate.
Qed.

Theorem evidence_absent_from_current_ledger_cannot_close :
  forall bundle manifest environment revision evidence runtimeRequired facts,
    p1ManifestEvidence environment evidence = Some facts ->
    p1EvidenceCurrentLedger facts = false ->
    ~ P1EvidenceValidFor
        bundle manifest environment revision evidence runtimeRequired.
Proof.
  intros bundle manifest environment revision evidence runtimeRequired facts
    Hlookup Habsent Hvalid.
  destruct Hvalid as
    [actual [HactualLookup [Hledger _]]].
  rewrite Hlookup in HactualLookup.
  inversion HactualLookup; subst actual.
  rewrite Habsent in Hledger.
  discriminate.
Qed.

Theorem changed_bound_realization_dimension_invalidates_manifest_authority :
  forall scope oldContext newContext dimension expected,
    ScopeMatches scope oldContext ->
    scope dimension = Some expected ->
    newContext dimension <> Some expected ->
    ~ ScopeMatches scope newContext.
Proof.
  intros.
  eapply evidence_cannot_cross_changed_bound_dimension; eauto.
Qed.
