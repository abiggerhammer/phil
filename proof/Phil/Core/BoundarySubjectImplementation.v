From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import DataSubject BoundarySubject.

(*
  Mechanical implementation-refinement surface for PHIL-BND-SUBJECT-001.

  Concrete production code reflects Text/Set/Map/identity facts into booleans.
  This file gives those booleans one extracted decision authority while proving
  that the reflected fact bundles are exactly the Certified boundary-transfer
  and zero-copy admission predicates.
*)

Definition revisionPresent (revision : nat) : bool :=
  negb (Nat.eqb revision 0).

Lemma revision_present_iff :
  forall revision,
    revisionPresent revision = true <-> revision <> 0.
Proof.
  intro revision.
  unfold revisionPresent.
  rewrite Bool.negb_true_iff.
  apply Nat.eqb_neq.
Qed.

Definition transportKindIsCopy (transport : DataSubjectTransport) : bool :=
  match dataSubjectTransportKind transport with
  | SubjectCopyTransport => true
  | SubjectSuccessionTransport => false
  end.

Lemma transport_kind_is_copy_iff :
  forall transport,
    transportKindIsCopy transport = true <->
    dataSubjectTransportKind transport = SubjectCopyTransport.
Proof.
  intro transport.
  unfold transportKindIsCopy.
  destruct (dataSubjectTransportKind transport); split; intro H;
    try reflexivity; try discriminate.
Qed.

Inductive BoundarySubjectTransferDecision : Type :=
| BoundarySubjectTransferAcceptedDecision
| BoundarySubjectRuntimeCoincidenceDecision
| BoundarySubjectTransportKindDecision
| BoundarySubjectCopyRevisionDecision
| BoundarySubjectByteEqualityDecision
| BoundarySubjectTransferLawDecision
| BoundarySubjectEvidenceReferenceDecision
| BoundarySubjectValidityScopeDecision.

Definition decideBoundarySubjectTransferByFacts
  (checkedCandidate kindIsCopy copyRevisionPresent byteEqualityPresent
   transferLawPresent evidenceReferenceExact validityScopePresent : bool)
  : BoundarySubjectTransferDecision :=
  if checkedCandidate then
    if kindIsCopy then
      if copyRevisionPresent then
        if byteEqualityPresent then
          if transferLawPresent then
            if evidenceReferenceExact then
              if validityScopePresent then BoundarySubjectTransferAcceptedDecision
              else BoundarySubjectValidityScopeDecision
            else BoundarySubjectEvidenceReferenceDecision
          else BoundarySubjectTransferLawDecision
        else BoundarySubjectByteEqualityDecision
      else BoundarySubjectCopyRevisionDecision
    else BoundarySubjectTransportKindDecision
  else BoundarySubjectRuntimeCoincidenceDecision.

Definition BoundarySubjectTransferFactsSatisfied
  (checkedCandidate kindIsCopy copyRevisionPresent byteEqualityPresent
   transferLawPresent evidenceReferenceExact validityScopePresent : bool) : Prop :=
  checkedCandidate = true /\
  kindIsCopy = true /\
  copyRevisionPresent = true /\
  byteEqualityPresent = true /\
  transferLawPresent = true /\
  evidenceReferenceExact = true /\
  validityScopePresent = true.

Theorem boundary_subject_transfer_decision_accepted_iff :
  forall checkedCandidate kindIsCopy copyRevisionPresent byteEqualityPresent
    transferLawPresent evidenceReferenceExact validityScopePresent,
    decideBoundarySubjectTransferByFacts
      checkedCandidate kindIsCopy copyRevisionPresent byteEqualityPresent
      transferLawPresent evidenceReferenceExact validityScopePresent =
      BoundarySubjectTransferAcceptedDecision <->
    BoundarySubjectTransferFactsSatisfied
      checkedCandidate kindIsCopy copyRevisionPresent byteEqualityPresent
      transferLawPresent evidenceReferenceExact validityScopePresent.
Proof.
  intros a b c d e f g.
  unfold decideBoundarySubjectTransferByFacts,
    BoundarySubjectTransferFactsSatisfied.
  destruct a, b, c, d, e, f, g; simpl; intuition discriminate.
Qed.

Theorem reflected_checked_boundary_transfer_facts_exact :
  forall evidence transfer,
    BoundarySubjectTransferFactsSatisfied
      true
      (transportKindIsCopy (boundaryDataTransport transfer))
      (revisionPresent (boundaryCopyRelationRevision transfer))
      (revisionPresent (boundaryByteEqualityRevision transfer))
      (revisionPresent (boundaryEvidenceTransferLawRevision transfer))
      (Nat.eqb (boundaryAllowedEvidenceReference transfer)
        (subjectEvidenceReference evidence))
      (revisionPresent (boundaryValidityScopeRevision transfer)) <->
    BoundarySubjectTransferAccepted evidence transfer.
Proof.
  intros evidence transfer.
  unfold BoundarySubjectTransferFactsSatisfied.
  split.
  - intros [_ [Hkind [Hcopy [Hequality [Hlaw [Hevidence Hscope]]]]]].
    constructor.
    + exact ((proj1 (transport_kind_is_copy_iff
        (boundaryDataTransport transfer))) Hkind).
    + exact ((proj1 (revision_present_iff
        (boundaryCopyRelationRevision transfer))) Hcopy).
    + exact ((proj1 (revision_present_iff
        (boundaryByteEqualityRevision transfer))) Hequality).
    + exact ((proj1 (revision_present_iff
        (boundaryEvidenceTransferLawRevision transfer))) Hlaw).
    + exact ((proj1 (Nat.eqb_eq
        (boundaryAllowedEvidenceReference transfer)
        (subjectEvidenceReference evidence))) Hevidence).
    + exact ((proj1 (revision_present_iff
        (boundaryValidityScopeRevision transfer))) Hscope).
  - intro Haccepted.
    destruct Haccepted as [Hkind Hcopy Hequality Hlaw Hevidence Hscope].
    repeat split.
    + unfold transportKindIsCopy.
      destruct (dataSubjectTransportKind (boundaryDataTransport transfer))
        eqn:HtransportKind.
      * reflexivity.
      * discriminate Hkind.
    + exact ((proj2 (revision_present_iff
        (boundaryCopyRelationRevision transfer))) Hcopy).
    + exact ((proj2 (revision_present_iff
        (boundaryByteEqualityRevision transfer))) Hequality).
    + exact ((proj2 (revision_present_iff
        (boundaryEvidenceTransferLawRevision transfer))) Hlaw).
    + exact ((proj2 (Nat.eqb_eq
        (boundaryAllowedEvidenceReference transfer)
        (subjectEvidenceReference evidence))) Hevidence).
    + exact ((proj2 (revision_present_iff
        (boundaryValidityScopeRevision transfer))) Hscope).
Qed.

Corollary reflected_checked_boundary_transfer_decision_exact :
  forall evidence transfer,
    decideBoundarySubjectTransferByFacts
      true
      (transportKindIsCopy (boundaryDataTransport transfer))
      (revisionPresent (boundaryCopyRelationRevision transfer))
      (revisionPresent (boundaryByteEqualityRevision transfer))
      (revisionPresent (boundaryEvidenceTransferLawRevision transfer))
      (Nat.eqb (boundaryAllowedEvidenceReference transfer)
        (subjectEvidenceReference evidence))
      (revisionPresent (boundaryValidityScopeRevision transfer)) =
      BoundarySubjectTransferAcceptedDecision <->
    BoundarySubjectTransferAccepted evidence transfer.
Proof.
  intros evidence transfer.
  rewrite boundary_subject_transfer_decision_accepted_iff.
  apply reflected_checked_boundary_transfer_facts_exact.
Qed.

Theorem runtime_subject_coincidence_decision_rejects :
  forall kindIsCopy copyRevisionPresent byteEqualityPresent transferLawPresent
    evidenceReferenceExact validityScopePresent,
    decideBoundarySubjectTransferByFacts
      false kindIsCopy copyRevisionPresent byteEqualityPresent transferLawPresent
      evidenceReferenceExact validityScopePresent =
      BoundarySubjectRuntimeCoincidenceDecision.
Proof.
  intros; reflexivity.
Qed.

Inductive ZeroCopyRealizationDecision : Type :=
| ZeroCopyRealizationAcceptedDecision
| ZeroCopyPointerReinterpretationDecision
| ZeroCopyStageRevisionDecision
| ZeroCopyBoundaryRepresentationDecision
| ZeroCopyGrammarDecision
| ZeroCopyValueTypeDecision
| ZeroCopySourceSemanticLayoutDecision
| ZeroCopyConcreteMemoryLayoutDecision
| ZeroCopyEndianAlignmentPaddingTaggingDecision
| ZeroCopyLifetimeRulesDecision
| ZeroCopyOwnershipRulesDecision
| ZeroCopyDeviceStorageConstraintsDecision
| ZeroCopyTargetAssumptionsCarriersDecision.

Definition decideZeroCopyRealizationByFacts
  (checkedRealization stageExact boundaryRepresentationPresent grammarPresent
   valueTypePresent sourceSemanticLayoutPresent concreteMemoryLayoutPresent
   endianAlignmentPaddingTaggingPresent lifetimeRulesPresent ownershipRulesPresent
   deviceStorageConstraintsPresent targetAssumptionsCarriersPresent : bool)
  : ZeroCopyRealizationDecision :=
  if checkedRealization then
    if stageExact then
      if boundaryRepresentationPresent then
        if grammarPresent then
          if valueTypePresent then
            if sourceSemanticLayoutPresent then
              if concreteMemoryLayoutPresent then
                if endianAlignmentPaddingTaggingPresent then
                  if lifetimeRulesPresent then
                    if ownershipRulesPresent then
                      if deviceStorageConstraintsPresent then
                        if targetAssumptionsCarriersPresent then
                          ZeroCopyRealizationAcceptedDecision
                        else ZeroCopyTargetAssumptionsCarriersDecision
                      else ZeroCopyDeviceStorageConstraintsDecision
                    else ZeroCopyOwnershipRulesDecision
                  else ZeroCopyLifetimeRulesDecision
                else ZeroCopyEndianAlignmentPaddingTaggingDecision
              else ZeroCopyConcreteMemoryLayoutDecision
            else ZeroCopySourceSemanticLayoutDecision
          else ZeroCopyValueTypeDecision
        else ZeroCopyGrammarDecision
      else ZeroCopyBoundaryRepresentationDecision
    else ZeroCopyStageRevisionDecision
  else ZeroCopyPointerReinterpretationDecision.

Definition ZeroCopyFactsSatisfied
  (checkedRealization stageExact boundaryRepresentationPresent grammarPresent
   valueTypePresent sourceSemanticLayoutPresent concreteMemoryLayoutPresent
   endianAlignmentPaddingTaggingPresent lifetimeRulesPresent ownershipRulesPresent
   deviceStorageConstraintsPresent targetAssumptionsCarriersPresent : bool) : Prop :=
  checkedRealization = true /\
  stageExact = true /\
  boundaryRepresentationPresent = true /\
  grammarPresent = true /\
  valueTypePresent = true /\
  sourceSemanticLayoutPresent = true /\
  concreteMemoryLayoutPresent = true /\
  endianAlignmentPaddingTaggingPresent = true /\
  lifetimeRulesPresent = true /\
  ownershipRulesPresent = true /\
  deviceStorageConstraintsPresent = true /\
  targetAssumptionsCarriersPresent = true.

Theorem zero_copy_decision_accepted_iff :
  forall a b c d e f g h i j k l,
    decideZeroCopyRealizationByFacts a b c d e f g h i j k l =
      ZeroCopyRealizationAcceptedDecision <->
    ZeroCopyFactsSatisfied a b c d e f g h i j k l.
Proof.
  intros a b c d e f g h i j k l.
  unfold decideZeroCopyRealizationByFacts, ZeroCopyFactsSatisfied.
  destruct a, b, c, d, e, f, g, h, i, j, k, l; simpl;
    intuition discriminate.
Qed.

Theorem reflected_checked_zero_copy_facts_exact :
  forall relation,
    ZeroCopyFactsSatisfied
      true
      (Nat.eqb (zeroCopyBaseStageRevision relation)
        (zeroCopyRelationStageRevision relation))
      (revisionPresent (zeroCopyBoundaryRepresentationRevision relation))
      (revisionPresent (zeroCopyGrammarRevision relation))
      (revisionPresent (zeroCopyValueTypeRevision relation))
      (revisionPresent (zeroCopySourceSemanticLayoutFact relation))
      (revisionPresent (zeroCopyConcreteMemoryLayoutFact relation))
      (revisionPresent (zeroCopyEndianAlignmentPaddingTaggingFact relation))
      (revisionPresent (zeroCopyLifetimeRulesFact relation))
      (revisionPresent (zeroCopyOwnershipRulesFact relation))
      (revisionPresent (zeroCopyDeviceStorageConstraintsFact relation))
      (revisionPresent (zeroCopyTargetAssumptionsCarriersFact relation)) <->
    ZeroCopyRelationAccepted relation.
Proof.
  intro relation.
  unfold ZeroCopyFactsSatisfied.
  split.
  - intros [_ [Hstage [Hrepresentation [Hgrammar [Hvalue [Hsource [Hmemory
      [Hendian [Hlifetime [Hownership [Hdevice Hassumptions]]]]]]]]]]].
    constructor.
    + exact ((proj1 (Nat.eqb_eq
        (zeroCopyBaseStageRevision relation)
        (zeroCopyRelationStageRevision relation))) Hstage).
    + exact ((proj1 (revision_present_iff
        (zeroCopyBoundaryRepresentationRevision relation))) Hrepresentation).
    + exact ((proj1 (revision_present_iff
        (zeroCopyGrammarRevision relation))) Hgrammar).
    + exact ((proj1 (revision_present_iff
        (zeroCopyValueTypeRevision relation))) Hvalue).
    + exact ((proj1 (revision_present_iff
        (zeroCopySourceSemanticLayoutFact relation))) Hsource).
    + exact ((proj1 (revision_present_iff
        (zeroCopyConcreteMemoryLayoutFact relation))) Hmemory).
    + exact ((proj1 (revision_present_iff
        (zeroCopyEndianAlignmentPaddingTaggingFact relation))) Hendian).
    + exact ((proj1 (revision_present_iff
        (zeroCopyLifetimeRulesFact relation))) Hlifetime).
    + exact ((proj1 (revision_present_iff
        (zeroCopyOwnershipRulesFact relation))) Hownership).
    + exact ((proj1 (revision_present_iff
        (zeroCopyDeviceStorageConstraintsFact relation))) Hdevice).
    + exact ((proj1 (revision_present_iff
        (zeroCopyTargetAssumptionsCarriersFact relation))) Hassumptions).
  - intro Haccepted.
    destruct Haccepted as
      [Hstage Hrepresentation Hgrammar Hvalue Hsource Hmemory Hendian
       Hlifetime Hownership Hdevice Hassumptions].
    repeat split.
    + apply Nat.eqb_eq.
      exact Hstage.
    + exact ((proj2 (revision_present_iff
        (zeroCopyBoundaryRepresentationRevision relation))) Hrepresentation).
    + exact ((proj2 (revision_present_iff
        (zeroCopyGrammarRevision relation))) Hgrammar).
    + exact ((proj2 (revision_present_iff
        (zeroCopyValueTypeRevision relation))) Hvalue).
    + exact ((proj2 (revision_present_iff
        (zeroCopySourceSemanticLayoutFact relation))) Hsource).
    + exact ((proj2 (revision_present_iff
        (zeroCopyConcreteMemoryLayoutFact relation))) Hmemory).
    + exact ((proj2 (revision_present_iff
        (zeroCopyEndianAlignmentPaddingTaggingFact relation))) Hendian).
    + exact ((proj2 (revision_present_iff
        (zeroCopyLifetimeRulesFact relation))) Hlifetime).
    + exact ((proj2 (revision_present_iff
        (zeroCopyOwnershipRulesFact relation))) Hownership).
    + exact ((proj2 (revision_present_iff
        (zeroCopyDeviceStorageConstraintsFact relation))) Hdevice).
    + exact ((proj2 (revision_present_iff
        (zeroCopyTargetAssumptionsCarriersFact relation))) Hassumptions).
Qed.

Corollary reflected_checked_zero_copy_decision_exact :
  forall relation,
    decideZeroCopyRealizationByFacts
      true
      (Nat.eqb (zeroCopyBaseStageRevision relation)
        (zeroCopyRelationStageRevision relation))
      (revisionPresent (zeroCopyBoundaryRepresentationRevision relation))
      (revisionPresent (zeroCopyGrammarRevision relation))
      (revisionPresent (zeroCopyValueTypeRevision relation))
      (revisionPresent (zeroCopySourceSemanticLayoutFact relation))
      (revisionPresent (zeroCopyConcreteMemoryLayoutFact relation))
      (revisionPresent (zeroCopyEndianAlignmentPaddingTaggingFact relation))
      (revisionPresent (zeroCopyLifetimeRulesFact relation))
      (revisionPresent (zeroCopyOwnershipRulesFact relation))
      (revisionPresent (zeroCopyDeviceStorageConstraintsFact relation))
      (revisionPresent (zeroCopyTargetAssumptionsCarriersFact relation)) =
      ZeroCopyRealizationAcceptedDecision <->
    ZeroCopyRelationAccepted relation.
Proof.
  intro relation.
  rewrite zero_copy_decision_accepted_iff.
  apply reflected_checked_zero_copy_facts_exact.
Qed.

Theorem pointer_reinterpretation_decision_rejects :
  forall stageExact boundaryRepresentationPresent grammarPresent valueTypePresent
    sourceSemanticLayoutPresent concreteMemoryLayoutPresent
    endianAlignmentPaddingTaggingPresent lifetimeRulesPresent ownershipRulesPresent
    deviceStorageConstraintsPresent targetAssumptionsCarriersPresent,
    decideZeroCopyRealizationByFacts
      false stageExact boundaryRepresentationPresent grammarPresent valueTypePresent
      sourceSemanticLayoutPresent concreteMemoryLayoutPresent
      endianAlignmentPaddingTaggingPresent lifetimeRulesPresent ownershipRulesPresent
      deviceStorageConstraintsPresent targetAssumptionsCarriersPresent =
      ZeroCopyPointerReinterpretationDecision.
Proof.
  intros; reflexivity.
Qed.
