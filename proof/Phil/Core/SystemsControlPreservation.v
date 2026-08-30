From Stdlib Require Import Bool.Bool.

(*
  PHIL-SYS-CONTROL-001 — cross-stage control/resource/protocol/boundary
  preservation for the bounded SYS-007--010 Systems chain.

  This is a normalized semantic model of the already implemented cumulative
  stage checkers.  Concrete Haskell Map/Set/list construction, CFG/value
  enumeration, exact diagnostics, and implementation equivalence remain
  explicit correspondence boundaries.
*)

Record BranchPreservationFacts : Type := mkBranchPreservationFacts {
  branchOutcomeDomainExact : bool;
  branchOwnerFateDomainExact : bool;
  branchOwnerFateRealizedExactlyOnce : bool;
  branchControlClassExact : bool;
  branchTrackedValuesAreOwners : bool
}.

Definition branchPreserved (facts : BranchPreservationFacts) : Prop :=
  branchOutcomeDomainExact facts = true /\
  branchOwnerFateDomainExact facts = true /\
  branchOwnerFateRealizedExactlyOnce facts = true /\
  branchControlClassExact facts = true /\
  branchTrackedValuesAreOwners facts = true.

Theorem branch_preservation_is_exact :
  forall facts,
    branchPreserved facts ->
    branchOutcomeDomainExact facts = true /\
    branchOwnerFateDomainExact facts = true /\
    branchOwnerFateRealizedExactlyOnce facts = true /\
    branchControlClassExact facts = true /\
    branchTrackedValuesAreOwners facts = true.
Proof.
  intros facts H.
  exact H.
Qed.

Theorem missing_owner_fate_cannot_preserve_branch :
  forall facts,
    branchOwnerFateDomainExact facts = false ->
    ~ branchPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [_ [Howner _]].
  rewrite Hbad in Howner.
  discriminate.
Qed.

Theorem unrealized_owner_fate_cannot_preserve_branch :
  forall facts,
    branchOwnerFateRealizedExactlyOnce facts = false ->
    ~ branchPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [_ [_ [Howner _]]].
  rewrite Hbad in Howner.
  discriminate.
Qed.

Theorem borrowed_view_cannot_stand_for_tracked_owner :
  forall facts,
    branchTrackedValuesAreOwners facts = false ->
    ~ branchPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [_ [_ [_ [_ Howner]]]].
  rewrite Hbad in Howner.
  discriminate.
Qed.

Theorem fatal_or_terminal_control_cannot_be_laundered :
  forall facts,
    branchControlClassExact facts = false ->
    ~ branchPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [_ [_ [_ [Hcontrol _]]]].
  rewrite Hbad in Hcontrol.
  discriminate.
Qed.

Record StateProjectionFacts : Type := mkStateProjectionFacts {
  stateProjectionKindExact : bool;
  stateSlotDomainExact : bool;
  stateRestrictedOwnerModeExact : bool;
  stateFixedSubjectExact : bool;
  stateRestrictedOwnerUnique : bool;
  stateLinearOwnersCovered : bool;
  stateScopedLoansDoNotEscape : bool;
  closureRestrictedCaptureHasOneCarrier : bool;
  closureRestrictedCarriersAreUnshared : bool
}.

Definition stateProjectionPreserved (facts : StateProjectionFacts) : Prop :=
  stateProjectionKindExact facts = true /\
  stateSlotDomainExact facts = true /\
  stateRestrictedOwnerModeExact facts = true /\
  stateFixedSubjectExact facts = true /\
  stateRestrictedOwnerUnique facts = true /\
  stateLinearOwnersCovered facts = true /\
  stateScopedLoansDoNotEscape facts = true /\
  closureRestrictedCaptureHasOneCarrier facts = true /\
  closureRestrictedCarriersAreUnshared facts = true.

Theorem state_projection_preserves_restricted_ownership :
  forall facts,
    stateProjectionPreserved facts ->
    stateRestrictedOwnerUnique facts = true /\
    stateLinearOwnersCovered facts = true /\
    stateScopedLoansDoNotEscape facts = true.
Proof.
  intros facts H.
  destruct H as [_ [_ [_ [_ [Hunique [Hcovered [Hloans _]]]]]]].
  split; [exact Hunique |].
  split; [exact Hcovered | exact Hloans].
Qed.

Theorem wrong_fixed_subject_cannot_cross_state_boundary :
  forall facts,
    stateFixedSubjectExact facts = false ->
    ~ stateProjectionPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [_ [_ [_ [Hsubject _]]]].
  rewrite Hbad in Hsubject.
  discriminate.
Qed.

Theorem duplicated_restricted_owner_cannot_cross_state_boundary :
  forall facts,
    stateRestrictedOwnerUnique facts = false ->
    ~ stateProjectionPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [_ [_ [_ [_ [Hunique _]]]]].
  rewrite Hbad in Hunique.
  discriminate.
Qed.

Theorem scoped_loan_escape_cannot_cross_state_boundary :
  forall facts,
    stateScopedLoansDoNotEscape facts = false ->
    ~ stateProjectionPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [_ [_ [_ [_ [_ [_ [Hloans _]]]]]]].
  rewrite Hbad in Hloans.
  discriminate.
Qed.

Record ProtocolPreservationFacts : Type := mkProtocolPreservationFacts {
  protocolBasisIsChecked : bool;
  protocolTargetSiteExact : bool;
  protocolTransportUseExact : bool;
  protocolOutcomeDomainExact : bool;
  protocolInstanceExact : bool;
  protocolRoleExact : bool;
  protocolSuccessorIsFresh : bool;
  protocolPredecessorConsumedOnce : bool;
  protocolSuccessorProducedOnce : bool;
  protocolLineageAcyclic : bool
}.

Definition protocolPreserved (facts : ProtocolPreservationFacts) : Prop :=
  protocolBasisIsChecked facts = true /\
  protocolTargetSiteExact facts = true /\
  protocolTransportUseExact facts = true /\
  protocolOutcomeDomainExact facts = true /\
  protocolInstanceExact facts = true /\
  protocolRoleExact facts = true /\
  protocolSuccessorIsFresh facts = true /\
  protocolPredecessorConsumedOnce facts = true /\
  protocolSuccessorProducedOnce facts = true /\
  protocolLineageAcyclic facts = true.

Theorem protocol_progression_preserves_identity_and_lineage :
  forall facts,
    protocolPreserved facts ->
    protocolInstanceExact facts = true /\
    protocolRoleExact facts = true /\
    protocolSuccessorIsFresh facts = true /\
    protocolPredecessorConsumedOnce facts = true /\
    protocolSuccessorProducedOnce facts = true /\
    protocolLineageAcyclic facts = true.
Proof.
  intros facts H.
  destruct H as [_ [_ [_ [_ [Hinstance [Hrole [Hfresh [Hconsume [Hproduce Hacyclic]]]]]]]]].
  split; [exact Hinstance |].
  split; [exact Hrole |].
  split; [exact Hfresh |].
  split; [exact Hconsume |].
  split; [exact Hproduce | exact Hacyclic].
Qed.

Theorem runtime_transport_coincidence_cannot_establish_protocol :
  forall facts,
    protocolBasisIsChecked facts = false ->
    ~ protocolPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [Hbasis _].
  rewrite Hbad in Hbasis.
  discriminate.
Qed.

Theorem stale_endpoint_reuse_cannot_preserve_protocol :
  forall facts,
    protocolSuccessorIsFresh facts = false ->
    ~ protocolPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [_ [_ [_ [_ [_ [_ [Hfresh _]]]]]]].
  rewrite Hbad in Hfresh.
  discriminate.
Qed.

Record BoundaryCommitFacts : Type := mkBoundaryCommitFacts {
  boundarySourceRuntimeFactExact : bool;
  boundaryTransportExact : bool;
  boundaryOwnerExact : bool;
  boundarySubjectExact : bool;
  boundaryLengthExact : bool;
  boundaryRuntimeKindExact : bool;
  boundaryRuntimeRevisionEvidenceExact : bool;
  boundaryProtocolTransitionExact : bool;
  boundaryCommitProducesSuccessor : bool;
  boundaryFailureRemainsTerminal : bool;
  boundaryCompleteBeforeSuccess : bool
}.

Definition boundaryCommitPreserved (facts : BoundaryCommitFacts) : Prop :=
  boundarySourceRuntimeFactExact facts = true /\
  boundaryTransportExact facts = true /\
  boundaryOwnerExact facts = true /\
  boundarySubjectExact facts = true /\
  boundaryLengthExact facts = true /\
  boundaryRuntimeKindExact facts = true /\
  boundaryRuntimeRevisionEvidenceExact facts = true /\
  boundaryProtocolTransitionExact facts = true /\
  boundaryCommitProducesSuccessor facts = true /\
  boundaryFailureRemainsTerminal facts = true /\
  boundaryCompleteBeforeSuccess facts = true.

Theorem boundary_commit_preserves_owner_length_and_protocol :
  forall facts,
    boundaryCommitPreserved facts ->
    boundaryOwnerExact facts = true /\
    boundarySubjectExact facts = true /\
    boundaryLengthExact facts = true /\
    boundaryProtocolTransitionExact facts = true /\
    boundaryCompleteBeforeSuccess facts = true.
Proof.
  intros facts H.
  destruct H as [_ [_ [Howner [Hsubject [Hlength [_ [_ [Hprotocol [_ [_ Hcomplete]]]]]]]]]].
  split; [exact Howner |].
  split; [exact Hsubject |].
  split; [exact Hlength |].
  split; [exact Hprotocol | exact Hcomplete].
Qed.

Theorem wrong_boundary_subject_cannot_commit :
  forall facts,
    boundarySubjectExact facts = false ->
    ~ boundaryCommitPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [_ [_ [_ [Hsubject _]]]].
  rewrite Hbad in Hsubject.
  discriminate.
Qed.

Theorem wrong_boundary_length_cannot_commit :
  forall facts,
    boundaryLengthExact facts = false ->
    ~ boundaryCommitPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [_ [_ [_ [_ [Hlength _]]]]].
  rewrite Hbad in Hlength.
  discriminate.
Qed.

Theorem early_boundary_success_cannot_commit :
  forall facts,
    boundaryCompleteBeforeSuccess facts = false ->
    ~ boundaryCommitPreserved facts.
Proof.
  intros facts Hbad H.
  destruct H as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hcomplete]]]]]]]]]].
  rewrite Hbad in Hcomplete.
  discriminate.
Qed.

Record SystemsControlFacts : Type := mkSystemsControlFacts {
  systemsBranchFacts : BranchPreservationFacts;
  systemsStateFacts : StateProjectionFacts;
  systemsProtocolFacts : ProtocolPreservationFacts;
  systemsBoundaryFacts : BoundaryCommitFacts
}.

Definition systemsControlPreserved (facts : SystemsControlFacts) : Prop :=
  branchPreserved (systemsBranchFacts facts) /\
  stateProjectionPreserved (systemsStateFacts facts) /\
  protocolPreserved (systemsProtocolFacts facts) /\
  boundaryCommitPreserved (systemsBoundaryFacts facts).

Theorem systems_control_preservation_is_cumulative :
  forall facts,
    systemsControlPreserved facts ->
    branchPreserved (systemsBranchFacts facts) /\
    stateProjectionPreserved (systemsStateFacts facts) /\
    protocolPreserved (systemsProtocolFacts facts) /\
    boundaryCommitPreserved (systemsBoundaryFacts facts).
Proof.
  intros facts H.
  exact H.
Qed.

Theorem successful_systems_control_stage_forbids_early_boundary_progression :
  forall facts,
    systemsControlPreserved facts ->
    boundaryCompleteBeforeSuccess (systemsBoundaryFacts facts) = true.
Proof.
  intros facts H.
  destruct H as [_ [_ [_ Hboundary]]].
  destruct Hboundary as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hcomplete]]]]]]]]]].
  exact Hcomplete.
Qed.

Theorem successful_systems_control_stage_preserves_protocol_lineage :
  forall facts,
    systemsControlPreserved facts ->
    protocolInstanceExact (systemsProtocolFacts facts) = true /\
    protocolRoleExact (systemsProtocolFacts facts) = true /\
    protocolSuccessorIsFresh (systemsProtocolFacts facts) = true.
Proof.
  intros facts H.
  destruct H as [_ [_ [Hprotocol _]]].
  destruct Hprotocol as [_ [_ [_ [_ [Hinstance [Hrole [Hfresh _]]]]]]].
  split; [exact Hinstance |].
  split; [exact Hrole | exact Hfresh].
Qed.
