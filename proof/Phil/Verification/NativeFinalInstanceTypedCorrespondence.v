(*
  D-ARTIFACT-MANIFEST-REFLECTION-01, issue #1584.
  An intermediate *typed native-coordinate* correspondence, deliberately
  not a Haskell-to-Rocq extractor or an arbitrary nat encoding.
  All types and the optional architecture-occurrence/stage-instance relation
  remain parameters.  A model Prop cannot manufacture accepted native inputs.
*)
Section NativeFinalInstanceTypedCorrespondence.
  Context
    {ApplicationIdentity ArchitectureInstanceIdentity ManifestIdentity
     Digest SubjectRevision StageInstanceRevision RealizationRevision
     SystemsArtifactRevision Phase1StageContractRevision
     ClosedStageContractRevision VerifierProfileRevision StageClosureObject : Type}.

  Record NativeFinalInstanceCoordinates := {
    acceptedApplication : ApplicationIdentity;
    producedApplication : ApplicationIdentity;
    checkedArchitectureInstance : ArchitectureInstanceIdentity;
    producedManifest : ManifestIdentity;
    acceptedReleaseManifest : ManifestIdentity;
    sourceStageClosure : StageClosureObject;
    releaseStageClosure : StageClosureObject;
    manifestRawSystemsDigest : Digest;
    stageRawSystemsDigest : Digest;
    manifestLoweringLedgerRoot : Digest;
    stageLoweringLedgerRoot : Digest;
    stageSubjectRevision : SubjectRevision;
    stageInstanceRevision : StageInstanceRevision;
    stageRealizationRevision : RealizationRevision;
    stageNormalizedSystemsRevision : SystemsArtifactRevision;
    stageCommonContractRevision : Phase1StageContractRevision;
    stageClosedContractRevision : ClosedStageContractRevision;
    stageVerifierProfile : VerifierProfileRevision
  }.

  (* Exactly the native producer/accepted-consumer equalities.  The source
     declaration/actuals checks, independent acceptance, stage verification,
     and release trust checks must be supplied by competent native producers. *)
  Definition NativeProducerConsumerBound (w : NativeFinalInstanceCoordinates) : Prop :=
    acceptedApplication w = producedApplication w /\
    producedManifest w = acceptedReleaseManifest w /\
    sourceStageClosure w = releaseStageClosure w /\
    manifestRawSystemsDigest w = stageRawSystemsDigest w /\
    manifestLoweringLedgerRoot w = stageLoweringLedgerRoot w.

  Theorem bound_preserves_exact_native_coordinates :
    forall w, NativeProducerConsumerBound w ->
      acceptedApplication w = producedApplication w /\
      producedManifest w = acceptedReleaseManifest w /\
      sourceStageClosure w = releaseStageClosure w /\
      manifestRawSystemsDigest w = stageRawSystemsDigest w /\
      manifestLoweringLedgerRoot w = stageLoweringLedgerRoot w.
  Proof.
    intros w H. exact H.
  Qed.

  Theorem substituted_source_application_cannot_bind :
    forall w,
      acceptedApplication w <> producedApplication w ->
      ~ NativeProducerConsumerBound w.
  Proof.
    intros w Hdiff [Heq _]. exact (Hdiff Heq).
  Qed.

  Theorem substituted_manifest_cannot_bind :
    forall w,
      producedManifest w <> acceptedReleaseManifest w ->
      ~ NativeProducerConsumerBound w.
  Proof.
    intros w Hdiff [_ [Heq _]]. exact (Hdiff Heq).
  Qed.

  Theorem substituted_stage_closure_cannot_bind :
    forall w,
      sourceStageClosure w <> releaseStageClosure w ->
      ~ NativeProducerConsumerBound w.
  Proof.
    intros w Hdiff [_ [_ [Heq _]]]. exact (Hdiff Heq).
  Qed.

  Theorem raw_digest_drift_cannot_bind :
    forall w,
      manifestRawSystemsDigest w <> stageRawSystemsDigest w ->
      ~ NativeProducerConsumerBound w.
  Proof.
    intros w Hdiff [_ [_ [_ [Heq _]]]]. exact (Hdiff Heq).
  Qed.

  Theorem lowering_root_drift_cannot_bind :
    forall w,
      manifestLoweringLedgerRoot w <> stageLoweringLedgerRoot w ->
      ~ NativeProducerConsumerBound w.
  Proof.
    intros w Hdiff [_ [_ [_ [_ Heq]]]]. exact (Hdiff Heq).
  Qed.

  (* ArchitectureInstanceIdentity and the concrete stage's InstanceRevision
     are not interchangeable types.  This relation is an explicit independent
     premise, not manufactured from the producer/consumer equalities. *)
  Context (architectureOccurrenceRepresentsStageInstance :
    ArchitectureInstanceIdentity -> StageInstanceRevision -> Prop).

  Definition NativeWithStageInstancePremise
    (w : NativeFinalInstanceCoordinates) : Prop :=
    NativeProducerConsumerBound w /\
    architectureOccurrenceRepresentsStageInstance
      (checkedArchitectureInstance w) (stageInstanceRevision w).

  Theorem absent_stage_instance_premise_blocks_extension :
    forall w,
      ~ architectureOccurrenceRepresentsStageInstance
          (checkedArchitectureInstance w) (stageInstanceRevision w) ->
      ~ NativeWithStageInstancePremise w.
  Proof.
    intros w Hmissing [_ Hrelated]. exact (Hmissing Hrelated).
  Qed.

  Theorem extended_boundary_preserves_both_premises :
    forall w, NativeWithStageInstancePremise w ->
      NativeProducerConsumerBound w /\
      architectureOccurrenceRepresentsStageInstance
        (checkedArchitectureInstance w) (stageInstanceRevision w).
  Proof.
    intros w H. exact H.
  Qed.
End NativeFinalInstanceTypedCorrespondence.
