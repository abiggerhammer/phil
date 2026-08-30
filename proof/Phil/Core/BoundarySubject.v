From Stdlib Require Import Arith.PeanoNat.

From Phil.Core Require Import DataSubject.

(*
  PHIL-BND-SUBJECT-001 — byte-subject transfer and zero-copy realization.

  This proof composes the already Certified DATA-SUBJECT transport semantics
  with the boundary-specific gates required by BND-012 and BND-013.

  Concrete Haskell Text/Map/Set representation, canonical stage revision
  construction, truth of copy/equality/transfer-law evidence, target layout and
  ABI facts, and Haskell implementation equivalence remain explicit
  correspondence boundaries.
*)

Record BoundarySubjectTransfer : Type := mkBoundarySubjectTransfer {
  boundaryDataTransport : DataSubjectTransport;
  boundaryCopyRelationRevision : nat;
  boundaryByteEqualityRevision : nat;
  boundaryEvidenceTransferLawRevision : nat;
  boundaryAllowedEvidenceReference : nat;
  boundaryValidityScopeRevision : nat
}.

(* The boundary checker adds copy/equality/proposition-transfer/scope facts to
   an explicit DATA-SUBJECT transport.  It does not manufacture the underlying
   semantic subject transport itself. *)
Record BoundarySubjectTransferAccepted
  (evidence : SubjectBoundEvidence)
  (transfer : BoundarySubjectTransfer) : Prop :=
  mkBoundarySubjectTransferAccepted {
    boundaryTransferKindIsCopy :
      dataSubjectTransportKind (boundaryDataTransport transfer) =
        SubjectCopyTransport;
    boundaryTransferCopyRevisionPresent :
      boundaryCopyRelationRevision transfer <> 0;
    boundaryTransferByteEqualityPresent :
      boundaryByteEqualityRevision transfer <> 0;
    boundaryTransferLawPresent :
      boundaryEvidenceTransferLawRevision transfer <> 0;
    boundaryTransferAllowedEvidenceExact :
      boundaryAllowedEvidenceReference transfer =
        subjectEvidenceReference evidence;
    boundaryTransferValidityScopePresent :
      boundaryValidityScopeRevision transfer <> 0
  }.

Inductive BoundaryTransferCandidate : Type :=
| CheckedBoundaryTransfer : BoundarySubjectTransfer -> BoundaryTransferCandidate
| RuntimeSubjectCoincidenceCandidate : nat -> BoundaryTransferCandidate.

Definition BoundaryTransferCandidateAccepted
  (evidence : SubjectBoundEvidence)
  (candidate : BoundaryTransferCandidate) : Prop :=
  match candidate with
  | CheckedBoundaryTransfer transfer =>
      BoundarySubjectTransferAccepted evidence transfer
  | RuntimeSubjectCoincidenceCandidate _ => False
  end.

Theorem checked_boundary_transfer_composes_data_subject_transport :
  forall update evidence transfer resultEvidence,
    CheckedDataSubjectUpdate
      update evidence (Some (boundaryDataTransport transfer)) resultEvidence ->
    BoundarySubjectTransferAccepted evidence transfer ->
    TransportValid update evidence (boundaryDataTransport transfer).
Proof.
  intros update evidence transfer resultEvidence Hchecked Hboundary.
  eapply checked_explicit_transport_is_valid.
  exact Hchecked.
Qed.

Theorem checked_boundary_transfer_preserves_all_boundary_gates :
  forall update evidence transfer resultEvidence,
    CheckedDataSubjectUpdate
      update evidence (Some (boundaryDataTransport transfer)) resultEvidence ->
    BoundarySubjectTransferAccepted evidence transfer ->
    TransportValid update evidence (boundaryDataTransport transfer) /\
    dataSubjectTransportKind (boundaryDataTransport transfer) =
      SubjectCopyTransport /\
    boundaryCopyRelationRevision transfer <> 0 /\
    boundaryByteEqualityRevision transfer <> 0 /\
    boundaryEvidenceTransferLawRevision transfer <> 0 /\
    boundaryAllowedEvidenceReference transfer =
      subjectEvidenceReference evidence /\
    boundaryValidityScopeRevision transfer <> 0.
Proof.
  intros update evidence transfer resultEvidence Hchecked Hboundary.
  destruct Hboundary as [Hkind Hcopy Hequality Hlaw Hevidence Hscope].
  split.
  - eapply checked_explicit_transport_is_valid.
    exact Hchecked.
  - repeat split; assumption.
Qed.

Corollary changed_subject_without_explicit_transport_rejects_at_boundary :
  forall update evidence resultEvidence,
    dataSubjectIdentity (dataSubjectUpdatePrior update) <>
      dataSubjectIdentity (dataSubjectUpdateReplacement update) ->
    ~ CheckedDataSubjectUpdate update evidence None resultEvidence.
Proof.
  exact distinct_subject_without_transport_rejects.
Qed.

Theorem runtime_subject_coincidence_never_authorizes_transfer :
  forall evidence token,
    ~ BoundaryTransferCandidateAccepted
        evidence (RuntimeSubjectCoincidenceCandidate token).
Proof.
  intros evidence token Haccepted.
  exact Haccepted.
Qed.

Theorem missing_copy_relation_rejects_boundary_transfer :
  forall evidence transfer,
    boundaryCopyRelationRevision transfer = 0 ->
    ~ BoundarySubjectTransferAccepted evidence transfer.
Proof.
  intros evidence transfer Hzero Haccepted.
  apply (boundaryTransferCopyRevisionPresent evidence transfer Haccepted).
  exact Hzero.
Qed.

Theorem missing_byte_equality_rejects_boundary_transfer :
  forall evidence transfer,
    boundaryByteEqualityRevision transfer = 0 ->
    ~ BoundarySubjectTransferAccepted evidence transfer.
Proof.
  intros evidence transfer Hzero Haccepted.
  apply (boundaryTransferByteEqualityPresent evidence transfer Haccepted).
  exact Hzero.
Qed.

Theorem missing_transfer_law_rejects_boundary_transfer :
  forall evidence transfer,
    boundaryEvidenceTransferLawRevision transfer = 0 ->
    ~ BoundarySubjectTransferAccepted evidence transfer.
Proof.
  intros evidence transfer Hzero Haccepted.
  apply (boundaryTransferLawPresent evidence transfer Haccepted).
  exact Hzero.
Qed.

Theorem missing_validity_scope_rejects_boundary_transfer :
  forall evidence transfer,
    boundaryValidityScopeRevision transfer = 0 ->
    ~ BoundarySubjectTransferAccepted evidence transfer.
Proof.
  intros evidence transfer Hzero Haccepted.
  apply (boundaryTransferValidityScopePresent evidence transfer Haccepted).
  exact Hzero.
Qed.

Theorem boundary_transfer_evidence_reference_is_exact :
  forall evidence transfer,
    BoundarySubjectTransferAccepted evidence transfer ->
    boundaryAllowedEvidenceReference transfer =
      subjectEvidenceReference evidence.
Proof.
  intros evidence transfer Haccepted.
  exact (boundaryTransferAllowedEvidenceExact evidence transfer Haccepted).
Qed.

(* BND-013: zero-copy is a target realization relation, not an identity
   shortcut.  The nat fields below are normalized identities of independently
   checked correspondence facts.  Nonzero means that an exact named fact is
   present; this proof does not claim the underlying target fact is true. *)
Record ZeroCopyRelation : Type := mkZeroCopyRelation {
  zeroCopyBaseStageRevision : nat;
  zeroCopyRelationStageRevision : nat;
  zeroCopyBoundaryRepresentationRevision : nat;
  zeroCopyGrammarRevision : nat;
  zeroCopyValueTypeRevision : nat;
  zeroCopySourceSemanticLayoutFact : nat;
  zeroCopyConcreteMemoryLayoutFact : nat;
  zeroCopyEndianAlignmentPaddingTaggingFact : nat;
  zeroCopyLifetimeRulesFact : nat;
  zeroCopyOwnershipRulesFact : nat;
  zeroCopyDeviceStorageConstraintsFact : nat;
  zeroCopyTargetAssumptionsCarriersFact : nat
}.

Record ZeroCopyRelationAccepted (relation : ZeroCopyRelation) : Prop :=
  mkZeroCopyRelationAccepted {
    zeroCopyStageRevisionExact :
      zeroCopyBaseStageRevision relation = zeroCopyRelationStageRevision relation;
    zeroCopyBoundaryRepresentationPresent :
      zeroCopyBoundaryRepresentationRevision relation <> 0;
    zeroCopyGrammarPresent : zeroCopyGrammarRevision relation <> 0;
    zeroCopyValueTypePresent : zeroCopyValueTypeRevision relation <> 0;
    zeroCopySourceSemanticLayoutPresent :
      zeroCopySourceSemanticLayoutFact relation <> 0;
    zeroCopyConcreteMemoryLayoutPresent :
      zeroCopyConcreteMemoryLayoutFact relation <> 0;
    zeroCopyEndianAlignmentPaddingTaggingPresent :
      zeroCopyEndianAlignmentPaddingTaggingFact relation <> 0;
    zeroCopyLifetimeRulesPresent : zeroCopyLifetimeRulesFact relation <> 0;
    zeroCopyOwnershipRulesPresent : zeroCopyOwnershipRulesFact relation <> 0;
    zeroCopyDeviceStorageConstraintsPresent :
      zeroCopyDeviceStorageConstraintsFact relation <> 0;
    zeroCopyTargetAssumptionsCarriersPresent :
      zeroCopyTargetAssumptionsCarriersFact relation <> 0
  }.

Inductive BoundaryTargetRealization : Type :=
| CheckedZeroCopyRealization : ZeroCopyRelation -> BoundaryTargetRealization
| PointerReinterpretationRealization : nat -> BoundaryTargetRealization.

Definition BoundaryTargetRealizationAccepted
  (realization : BoundaryTargetRealization) : Prop :=
  match realization with
  | CheckedZeroCopyRealization relation => ZeroCopyRelationAccepted relation
  | PointerReinterpretationRealization _ => False
  end.

Theorem checked_zero_copy_requires_exact_stage :
  forall relation,
    BoundaryTargetRealizationAccepted (CheckedZeroCopyRealization relation) ->
    zeroCopyBaseStageRevision relation = zeroCopyRelationStageRevision relation.
Proof.
  intros relation Haccepted.
  exact (zeroCopyStageRevisionExact relation Haccepted).
Qed.

Theorem checked_zero_copy_requires_all_correspondence_facts :
  forall relation,
    BoundaryTargetRealizationAccepted (CheckedZeroCopyRealization relation) ->
    zeroCopyBoundaryRepresentationRevision relation <> 0 /\
    zeroCopyGrammarRevision relation <> 0 /\
    zeroCopyValueTypeRevision relation <> 0 /\
    zeroCopySourceSemanticLayoutFact relation <> 0 /\
    zeroCopyConcreteMemoryLayoutFact relation <> 0 /\
    zeroCopyEndianAlignmentPaddingTaggingFact relation <> 0 /\
    zeroCopyLifetimeRulesFact relation <> 0 /\
    zeroCopyOwnershipRulesFact relation <> 0 /\
    zeroCopyDeviceStorageConstraintsFact relation <> 0 /\
    zeroCopyTargetAssumptionsCarriersFact relation <> 0.
Proof.
  intros relation Haccepted.
  destruct Haccepted as
    [Hstage Hrepresentation Hgrammar Hvalue Hsource Hmemory Hendian
     Hlifetime Hownership Hdevice Hassumptions].
  repeat split; assumption.
Qed.

Theorem missing_endian_alignment_fact_rejects_zero_copy :
  forall relation,
    zeroCopyEndianAlignmentPaddingTaggingFact relation = 0 ->
    ~ BoundaryTargetRealizationAccepted (CheckedZeroCopyRealization relation).
Proof.
  intros relation Hzero Haccepted.
  apply (zeroCopyEndianAlignmentPaddingTaggingPresent relation Haccepted).
  exact Hzero.
Qed.

Theorem missing_lifetime_fact_rejects_zero_copy :
  forall relation,
    zeroCopyLifetimeRulesFact relation = 0 ->
    ~ BoundaryTargetRealizationAccepted (CheckedZeroCopyRealization relation).
Proof.
  intros relation Hzero Haccepted.
  apply (zeroCopyLifetimeRulesPresent relation Haccepted).
  exact Hzero.
Qed.

Theorem missing_ownership_fact_rejects_zero_copy :
  forall relation,
    zeroCopyOwnershipRulesFact relation = 0 ->
    ~ BoundaryTargetRealizationAccepted (CheckedZeroCopyRealization relation).
Proof.
  intros relation Hzero Haccepted.
  apply (zeroCopyOwnershipRulesPresent relation Haccepted).
  exact Hzero.
Qed.

Theorem pointer_reinterpretation_never_authorizes_zero_copy :
  forall detail,
    ~ BoundaryTargetRealizationAccepted
        (PointerReinterpretationRealization detail).
Proof.
  intros detail Haccepted.
  exact Haccepted.
Qed.

Theorem complete_zero_copy_relation_is_admitted :
  forall relation,
    zeroCopyBaseStageRevision relation = zeroCopyRelationStageRevision relation ->
    zeroCopyBoundaryRepresentationRevision relation <> 0 ->
    zeroCopyGrammarRevision relation <> 0 ->
    zeroCopyValueTypeRevision relation <> 0 ->
    zeroCopySourceSemanticLayoutFact relation <> 0 ->
    zeroCopyConcreteMemoryLayoutFact relation <> 0 ->
    zeroCopyEndianAlignmentPaddingTaggingFact relation <> 0 ->
    zeroCopyLifetimeRulesFact relation <> 0 ->
    zeroCopyOwnershipRulesFact relation <> 0 ->
    zeroCopyDeviceStorageConstraintsFact relation <> 0 ->
    zeroCopyTargetAssumptionsCarriersFact relation <> 0 ->
    BoundaryTargetRealizationAccepted (CheckedZeroCopyRealization relation).
Proof.
  intros relation Hstage Hrepresentation Hgrammar Hvalue Hsource Hmemory
    Hendian Hlifetime Hownership Hdevice Hassumptions.
  constructor; assumption.
Qed.
