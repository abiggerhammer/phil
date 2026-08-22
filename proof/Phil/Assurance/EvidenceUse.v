From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Assurance Require Import Manifest.

(*
  Proof-oriented model of the remaining authority-bearing checks in
  Phil.Assurance.Verify.

  Manifest.v already proves certification-scope closure, non-vacuous evidence
  acceptance, and justification acyclicity.  This file proves the verifier
  gates that sit underneath and after that closure:

  - assumptions contribute authority only through exact selected/permitted/
    in-scope records and an explicit assumption boundary;
  - assurance kinds cannot silently upgrade incomplete evidence: artifact-
    backed kinds require the exact trusted artifact, and RuntimeEnforced
    requires a complete mechanism, runtime residue, and a known cost link;
  - erasure/runtime assurance uses are exact to an accepted in-scope revision,
    and append-only ledger extension preserves every existing node unchanged.

  Concrete SHA-256 collision resistance, Text/Map/Set correspondence, and the
  semantic truth of external artifacts remain explicit implementation/trust
  boundaries.  The theorems establish that verifier success is gated on those
  checks; they do not prove cryptographic injectivity or rerun external tools.
*)

Inductive GateResult : Type :=
| GateRejected
| GateAccepted.

(* -------------------------------------------------------------------------- *)
(* PHIL-ASSURE-ASSUME-001 — explicit assumption authority.                   *)
(* -------------------------------------------------------------------------- *)

Record AssumptionAuthority : Type := mkAssumptionAuthority {
  assumptionIdentityMatches : bool;
  assumptionDigestMatches : bool;
  assumptionSelectedByManifest : bool;
  assumptionPermittedByContext : bool;
  assumptionValidityMatches : bool
}.

Definition verifyAssumptionAuthority
  (assumption : AssumptionAuthority) : GateResult :=
  if assumptionIdentityMatches assumption then
    if assumptionDigestMatches assumption then
      if assumptionSelectedByManifest assumption then
        if assumptionPermittedByContext assumption then
          if assumptionValidityMatches assumption
          then GateAccepted
          else GateRejected
        else GateRejected
      else GateRejected
    else GateRejected
  else GateRejected.

Theorem successful_assumption_authority_is_exact :
  forall assumption,
    verifyAssumptionAuthority assumption = GateAccepted ->
    assumptionIdentityMatches assumption = true /\
    assumptionDigestMatches assumption = true /\
    assumptionSelectedByManifest assumption = true /\
    assumptionPermittedByContext assumption = true /\
    assumptionValidityMatches assumption = true.
Proof.
  intros assumption Hverify.
  unfold verifyAssumptionAuthority in Hverify.
  destruct (assumptionIdentityMatches assumption) eqn:Hidentity;
    [| discriminate].
  destruct (assumptionDigestMatches assumption) eqn:Hdigest;
    [| discriminate].
  destruct (assumptionSelectedByManifest assumption) eqn:Hselected;
    [| discriminate].
  destruct (assumptionPermittedByContext assumption) eqn:Hpermitted;
    [| discriminate].
  destruct (assumptionValidityMatches assumption) eqn:Hscope;
    [| discriminate].
  repeat split; assumption.
Qed.

Record AssumedEvidenceBoundary : Type := mkAssumedEvidenceBoundary {
  assumedEvidenceHasAssumptionDependency : bool;
  assumedEvidenceHasExplicitBoundaryRole : bool
}.

Definition verifyAssumedEvidenceAuthority
  (assumption : AssumptionAuthority)
  (boundary : AssumedEvidenceBoundary) : GateResult :=
  match verifyAssumptionAuthority assumption with
  | GateRejected => GateRejected
  | GateAccepted =>
      if assumedEvidenceHasAssumptionDependency boundary then
        if assumedEvidenceHasExplicitBoundaryRole boundary
        then GateAccepted
        else GateRejected
      else GateRejected
  end.

Theorem successful_assumed_evidence_has_explicit_authority_boundary :
  forall assumption boundary,
    verifyAssumedEvidenceAuthority assumption boundary = GateAccepted ->
    assumptionIdentityMatches assumption = true /\
    assumptionDigestMatches assumption = true /\
    assumptionSelectedByManifest assumption = true /\
    assumptionPermittedByContext assumption = true /\
    assumptionValidityMatches assumption = true /\
    assumedEvidenceHasAssumptionDependency boundary = true /\
    assumedEvidenceHasExplicitBoundaryRole boundary = true.
Proof.
  intros assumption boundary Hverify.
  unfold verifyAssumedEvidenceAuthority in Hverify.
  destruct (verifyAssumptionAuthority assumption) eqn:Hassumption;
    [discriminate |].
  destruct (assumedEvidenceHasAssumptionDependency boundary) eqn:Hdependency;
    [| discriminate].
  destruct (assumedEvidenceHasExplicitBoundaryRole boundary) eqn:Hboundary;
    [| discriminate].
  pose proof
    (successful_assumption_authority_is_exact assumption Hassumption)
    as Hexact.
  destruct Hexact as
    [Hidentity [Hdigest [Hselected [Hpermitted Hscope]]]].
  repeat split; assumption.
Qed.

Theorem unpermitted_assumption_cannot_contribute_authority :
  forall assumption,
    assumptionPermittedByContext assumption = false ->
    verifyAssumptionAuthority assumption <> GateAccepted.
Proof.
  intros assumption Hforbidden Haccepted.
  pose proof
    (successful_assumption_authority_is_exact assumption Haccepted)
    as Hexact.
  destruct Hexact as [_ [_ [_ [Hpermitted _]]]].
  rewrite Hforbidden in Hpermitted.
  discriminate.
Qed.

Theorem stale_assumption_scope_cannot_contribute_authority :
  forall assumption,
    assumptionValidityMatches assumption = false ->
    verifyAssumptionAuthority assumption <> GateAccepted.
Proof.
  intros assumption Hstale Haccepted.
  pose proof
    (successful_assumption_authority_is_exact assumption Haccepted)
    as Hexact.
  destruct Hexact as [_ [_ [_ [_ Hscope]]]].
  rewrite Hstale in Hscope.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* PHIL-ASSURE-EVID-001 — evidence-kind authority.                            *)
(* -------------------------------------------------------------------------- *)

Record ArtifactAuthority : Type := mkArtifactAuthority {
  artifactDeclared : bool;
  artifactIdentityMatches : bool;
  artifactDigestMatchesTrustedAvailability : bool
}.

Definition verifyArtifactAuthority
  (artifact : ArtifactAuthority) : GateResult :=
  if artifactDeclared artifact then
    if artifactIdentityMatches artifact then
      if artifactDigestMatchesTrustedAvailability artifact
      then GateAccepted
      else GateRejected
    else GateRejected
  else GateRejected.

Theorem successful_artifact_authority_is_exact :
  forall artifact,
    verifyArtifactAuthority artifact = GateAccepted ->
    artifactDeclared artifact = true /\
    artifactIdentityMatches artifact = true /\
    artifactDigestMatchesTrustedAvailability artifact = true.
Proof.
  intros artifact Hverify.
  unfold verifyArtifactAuthority in Hverify.
  destruct (artifactDeclared artifact) eqn:Hdeclared; [| discriminate].
  destruct (artifactIdentityMatches artifact) eqn:Hidentity; [| discriminate].
  destruct (artifactDigestMatchesTrustedAvailability artifact) eqn:Hdigest;
    [| discriminate].
  repeat split; assumption.
Qed.

Record RuntimeAuthority : Type := mkRuntimeAuthority {
  runtimeMechanismPresent : bool;
  runtimeMechanismComplete : bool;
  runtimeResiduePresent : bool;
  runtimeCostReferencePresent : bool;
  runtimeCostReferenceKnown : bool
}.

Definition verifyRuntimeAuthority
  (runtime : RuntimeAuthority) : GateResult :=
  if runtimeMechanismPresent runtime then
    if runtimeMechanismComplete runtime then
      if runtimeResiduePresent runtime then
        if runtimeCostReferencePresent runtime then
          if runtimeCostReferenceKnown runtime
          then GateAccepted
          else GateRejected
        else GateRejected
      else GateRejected
    else GateRejected
  else GateRejected.

Theorem successful_runtime_authority_is_complete :
  forall runtime,
    verifyRuntimeAuthority runtime = GateAccepted ->
    runtimeMechanismPresent runtime = true /\
    runtimeMechanismComplete runtime = true /\
    runtimeResiduePresent runtime = true /\
    runtimeCostReferencePresent runtime = true /\
    runtimeCostReferenceKnown runtime = true.
Proof.
  intros runtime Hverify.
  unfold verifyRuntimeAuthority in Hverify.
  destruct (runtimeMechanismPresent runtime) eqn:Hpresent; [| discriminate].
  destruct (runtimeMechanismComplete runtime) eqn:Hcomplete; [| discriminate].
  destruct (runtimeResiduePresent runtime) eqn:Hresidue; [| discriminate].
  destruct (runtimeCostReferencePresent runtime) eqn:Hcost; [| discriminate].
  destruct (runtimeCostReferenceKnown runtime) eqn:Hknown; [| discriminate].
  repeat split; assumption.
Qed.

Inductive ArtifactBackedKind : AssuranceKind -> Prop :=
| ArtifactProof : ArtifactBackedKind ProofKind
| ArtifactCertificate : ArtifactBackedKind CertificateKind
| ArtifactTranslation : ArtifactBackedKind TranslationKind
| ArtifactDifferential : ArtifactBackedKind DifferentialKind
| ArtifactProperty : ArtifactBackedKind PropertyKind.

Definition verifyKindAuthority
  (kind : AssuranceKind)
  (artifact : ArtifactAuthority)
  (runtime : RuntimeAuthority)
  (assumption : AssumptionAuthority)
  (assumedBoundary : AssumedEvidenceBoundary) : GateResult :=
  match kind with
  | KernelKind => GateAccepted
  | ProofKind => verifyArtifactAuthority artifact
  | CertificateKind => verifyArtifactAuthority artifact
  | TranslationKind => verifyArtifactAuthority artifact
  | DifferentialKind => verifyArtifactAuthority artifact
  | PropertyKind => verifyArtifactAuthority artifact
  | RuntimeKind => verifyRuntimeAuthority runtime
  | AssumedKind => verifyAssumedEvidenceAuthority assumption assumedBoundary
  end.

Theorem artifact_backed_kind_cannot_upgrade_incomplete_artifact :
  forall kind artifact runtime assumption assumedBoundary,
    ArtifactBackedKind kind ->
    verifyKindAuthority kind artifact runtime assumption assumedBoundary = GateAccepted ->
    artifactDeclared artifact = true /\
    artifactIdentityMatches artifact = true /\
    artifactDigestMatchesTrustedAvailability artifact = true.
Proof.
  intros kind artifact runtime assumption assumedBoundary Hkind Hverify.
  inversion Hkind; subst kind; simpl in Hverify;
    eapply successful_artifact_authority_is_exact; exact Hverify.
Qed.

Theorem runtime_kind_acceptance_requires_complete_runtime_authority :
  forall artifact runtime assumption assumedBoundary,
    verifyKindAuthority
      RuntimeKind artifact runtime assumption assumedBoundary = GateAccepted ->
    runtimeMechanismPresent runtime = true /\
    runtimeMechanismComplete runtime = true /\
    runtimeResiduePresent runtime = true /\
    runtimeCostReferencePresent runtime = true /\
    runtimeCostReferenceKnown runtime = true.
Proof.
  intros artifact runtime assumption assumedBoundary Hverify.
  simpl in Hverify.
  eapply successful_runtime_authority_is_complete.
  exact Hverify.
Qed.

Theorem assumed_kind_acceptance_requires_explicit_assumption_authority :
  forall artifact runtime assumption assumedBoundary,
    verifyKindAuthority
      AssumedKind artifact runtime assumption assumedBoundary = GateAccepted ->
    assumptionSelectedByManifest assumption = true /\
    assumptionPermittedByContext assumption = true /\
    assumptionValidityMatches assumption = true /\
    assumedEvidenceHasAssumptionDependency assumedBoundary = true /\
    assumedEvidenceHasExplicitBoundaryRole assumedBoundary = true.
Proof.
  intros artifact runtime assumption assumedBoundary Hverify.
  simpl in Hverify.
  pose proof
    (successful_assumed_evidence_has_explicit_authority_boundary
      assumption assumedBoundary Hverify)
    as Hexact.
  destruct Hexact as
    [_ [_ [Hselected [Hpermitted [Hscope [Hdependency Hboundary]]]]]].
  repeat split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* PHIL-ASSURE-USE-001 — assurance-use exactness and immutable history.       *)
(* -------------------------------------------------------------------------- *)

Definition CostRef := nat.
Definition CostSet := CostRef -> bool.

Record UseEvidenceEntry : Type := mkUseEvidenceEntry {
  useEntryRevision : RevisionId;
  useEntryKind : AssuranceKind;
  useEntryUsable : bool;
  useEntryCostRef : CostRef
}.

Definition UseEvidenceEnvironment := EvidenceId -> option UseEvidenceEntry.

Record AssuranceUseContext : Type := mkAssuranceUseContext {
  useCertificationScope : RevisionSet;
  useAcceptedRevisions : RevisionSet;
  useEvidenceEnvironment : UseEvidenceEnvironment;
  useKnownCostReferences : CostSet
}.

Definition EvidenceExactUsableFor
  (context : AssuranceUseContext)
  (revision : RevisionId)
  (evidence : EvidenceId) : Prop :=
  exists entry,
    useEvidenceEnvironment context evidence = Some entry /\
    useEntryRevision entry = revision /\
    useEntryUsable entry = true.

Definition ErasureUseVerified
  (context : AssuranceUseContext)
  (revision : RevisionId)
  (selected : EvidenceSet) : Prop :=
  useCertificationScope context revision = true /\
  useAcceptedRevisions context revision = true /\
  (exists evidence, selected evidence = true) /\
  (forall evidence,
    selected evidence = true ->
    EvidenceExactUsableFor context revision evidence).

Theorem verified_erasure_use_is_nonempty_and_exact :
  forall context revision selected,
    ErasureUseVerified context revision selected ->
    useCertificationScope context revision = true /\
    useAcceptedRevisions context revision = true /\
    exists evidence,
      selected evidence = true /\
      EvidenceExactUsableFor context revision evidence.
Proof.
  intros context revision selected Hverified.
  destruct Hverified as [Hscope [Haccepted [Hnonempty Hall]]].
  destruct Hnonempty as [evidence Hselected].
  repeat split.
  - exact Hscope.
  - exact Haccepted.
  - exists evidence.
    split.
    + exact Hselected.
    + apply Hall. exact Hselected.
Qed.

Definition RuntimeUseVerified
  (context : AssuranceUseContext)
  (revision : RevisionId)
  (evidence : EvidenceId)
  (costRef : CostRef) : Prop :=
  useCertificationScope context revision = true /\
  useAcceptedRevisions context revision = true /\
  exists entry,
    useEvidenceEnvironment context evidence = Some entry /\
    useEntryRevision entry = revision /\
    useEntryKind entry = RuntimeKind /\
    useEntryUsable entry = true /\
    useEntryCostRef entry = costRef /\
    useKnownCostReferences context costRef = true.

Theorem verified_runtime_use_is_exact_runtime_evidence_with_known_cost :
  forall context revision evidence costRef,
    RuntimeUseVerified context revision evidence costRef ->
    useCertificationScope context revision = true /\
    useAcceptedRevisions context revision = true /\
    exists entry,
      useEvidenceEnvironment context evidence = Some entry /\
      useEntryRevision entry = revision /\
      useEntryKind entry = RuntimeKind /\
      useEntryUsable entry = true /\
      useEntryCostRef entry = costRef /\
      useKnownCostReferences context costRef = true.
Proof.
  intros context revision evidence costRef Hverified.
  exact Hverified.
Qed.

Theorem non_runtime_evidence_cannot_authorize_retained_runtime_use :
  forall context revision evidence costRef entry,
    useEvidenceEnvironment context evidence = Some entry ->
    useEntryKind entry <> RuntimeKind ->
    ~ RuntimeUseVerified context revision evidence costRef.
Proof.
  intros context revision evidence costRef entry Hlookup HnotRuntime Hverified.
  destruct Hverified as
    [_ [_ [matched [HmatchedLookup [_ [Hkind _]]]]]].
  rewrite Hlookup in HmatchedLookup.
  inversion HmatchedLookup; subst matched.
  contradiction.
Qed.

Definition NodeMap := nat -> option nat.

Record LedgerView : Type := mkLedgerView {
  revisionNodes : NodeMap;
  evidenceNodes : NodeMap;
  assumptionNodes : NodeMap;
  exportNodes : NodeMap;
  assuranceUseNodes : NodeMap
}.

Definition PreservesMap (before after : NodeMap) : Prop :=
  forall key value,
    before key = Some value ->
    after key = Some value.

Record LedgerExtension
  (before after : LedgerView) : Prop := mkLedgerExtension {
  extensionPreservesRevisions :
    PreservesMap (revisionNodes before) (revisionNodes after);
  extensionPreservesEvidence :
    PreservesMap (evidenceNodes before) (evidenceNodes after);
  extensionPreservesAssumptions :
    PreservesMap (assumptionNodes before) (assumptionNodes after);
  extensionPreservesExports :
    PreservesMap (exportNodes before) (exportNodes after);
  extensionPreservesUses :
    PreservesMap (assuranceUseNodes before) (assuranceUseNodes after)
}.

Inductive LedgerNodeClass : Type :=
| RevisionNodeClass
| EvidenceNodeClass
| AssumptionNodeClass
| ExportNodeClass
| AssuranceUseNodeClass.

Definition nodesOf
  (class : LedgerNodeClass)
  (ledger : LedgerView) : NodeMap :=
  match class with
  | RevisionNodeClass => revisionNodes ledger
  | EvidenceNodeClass => evidenceNodes ledger
  | AssumptionNodeClass => assumptionNodes ledger
  | ExportNodeClass => exportNodes ledger
  | AssuranceUseNodeClass => assuranceUseNodes ledger
  end.

Theorem verified_ledger_extension_preserves_every_existing_node :
  forall before after class key value,
    LedgerExtension before after ->
    nodesOf class before key = Some value ->
    nodesOf class after key = Some value.
Proof.
  intros before after class key value Hextension Hold.
  destruct Hextension as [Hrevisions Hevidence Hassumptions Hexports Huses].
  destruct class; simpl in *.
  - eapply Hrevisions. exact Hold.
  - eapply Hevidence. exact Hold.
  - eapply Hassumptions. exact Hold.
  - eapply Hexports. exact Hold.
  - eapply Huses. exact Hold.
Qed.

Theorem verified_ledger_extension_forbids_in_place_rewrite :
  forall before after class key oldValue newValue,
    LedgerExtension before after ->
    nodesOf class before key = Some oldValue ->
    nodesOf class after key = Some newValue ->
    oldValue = newValue.
Proof.
  intros before after class key oldValue newValue Hextension Hold Hnew.
  pose proof
    (verified_ledger_extension_preserves_every_existing_node
      before after class key oldValue Hextension Hold)
    as Hpreserved.
  rewrite Hnew in Hpreserved.
  inversion Hpreserved.
  reflexivity.
Qed.
