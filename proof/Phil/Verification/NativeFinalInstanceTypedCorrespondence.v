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

  (* Model-level representation of the distinct native producer gate:
     existing source/manifest/stage equalities do not imply checked-instance
     producer acceptance. This predicate is an explicit external premise, not
     an invented Haskell-to-Rocq authority or stage-production certificate. *)
  Context (checkedInstanceProducer : ArchitectureInstanceIdentity -> Prop).

  Definition NativeCheckedInstanceProducerBound (w : NativeFinalInstanceCoordinates) : Prop :=
    NativeProducerConsumerBound w /\
    checkedInstanceProducer (checkedArchitectureInstance w).

  Theorem declaration_only_source_cannot_bind_final_authority :
    forall w,
      ~ checkedInstanceProducer (checkedArchitectureInstance w) ->
      ~ NativeCheckedInstanceProducerBound w.
  Proof.
    intros w Hnot [_ Hchecked]. exact (Hnot Hchecked).
  Qed.

  Theorem checked_instance_token_preserves_existing_consumer_equalities :
    forall w, NativeCheckedInstanceProducerBound w -> NativeProducerConsumerBound w.
  Proof.
    intros w [Hbound _]. exact Hbound.
  Qed.

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
  (*
    The native instance identity contains a revision; the concrete StageClosure
    carries that revision but not the occurrence key. Equality is a necessary
    optional gate, and cannot construct the independent origin relation.
  *)
  Context (architectureIdentityRevision :
    ArchitectureInstanceIdentity -> StageInstanceRevision).

  Definition NativeStageRevisionEqualityOnly
    (w : NativeFinalInstanceCoordinates) : Prop :=
    NativeProducerConsumerBound w /\
    architectureIdentityRevision (checkedArchitectureInstance w) =
      stageInstanceRevision w.

  Theorem stage_revision_drift_blocks_equality_gate :
    forall w,
      architectureIdentityRevision (checkedArchitectureInstance w) <>
        stageInstanceRevision w ->
      ~ NativeStageRevisionEqualityOnly w.
  Proof.
    intros w Hdiff [_ Heq]. exact (Hdiff Heq).
  Qed.

  Theorem revision_equality_does_not_discharge_origin_premise :
    forall w,
      ~ architectureOccurrenceRepresentsStageInstance
          (checkedArchitectureInstance w) (stageInstanceRevision w) ->
      ~ (NativeStageRevisionEqualityOnly w /\
          architectureOccurrenceRepresentsStageInstance
            (checkedArchitectureInstance w) (stageInstanceRevision w)).
  Proof.
    intros w Hmissing [_ Hrelated]. exact (Hmissing Hrelated).
  Qed.

  (*
    Conditional transport into separately typed model domains. A function
    per field is only a PARAMETER: this neither constructs a native producer
    nor supplies an implementation, injectivity proof, or nat representation.
    In particular the raw Systems digest and lowering root share native
    Digest but have different model codomains and unrelated representation
    functions.
  *)
  Section ConditionalModelTransport.
    Context {ModelSource ModelManifest ModelStage ModelRawSystemsDigest
             ModelLoweringRoot : Type}.
    Context
      (representSource : ApplicationIdentity -> ModelSource)
      (representManifest : ManifestIdentity -> ModelManifest)
      (representStage : StageClosureObject -> ModelStage)
      (representRawSystemsDigest : Digest -> ModelRawSystemsDigest)
      (representLoweringRoot : Digest -> ModelLoweringRoot).

    Definition RepresentedConsumerEqualities
      (w : NativeFinalInstanceCoordinates) : Prop :=
      representSource (acceptedApplication w) =
        representSource (producedApplication w) /\
      representManifest (producedManifest w) =
        representManifest (acceptedReleaseManifest w) /\
      representStage (sourceStageClosure w) =
        representStage (releaseStageClosure w) /\
      representRawSystemsDigest (manifestRawSystemsDigest w) =
        representRawSystemsDigest (stageRawSystemsDigest w) /\
      representLoweringRoot (manifestLoweringLedgerRoot w) =
        representLoweringRoot (stageLoweringLedgerRoot w).

    Theorem native_bound_transports_to_typed_model_equalities :
      forall w,
        NativeProducerConsumerBound w ->
        RepresentedConsumerEqualities w.
    Proof.
      intros w [Ha [Hm [Hs [Hd Hr]]]].
      unfold RepresentedConsumerEqualities.
      repeat split;
        [ now rewrite Ha | now rewrite Hm | now rewrite Hs
        | now rewrite Hd | now rewrite Hr ].
    Qed.

    (*
      The reverse logical implication needs *each* representation to be
      injective. Even with these hypotheses it reconstructs only the five
      equalities, NOT the authority of independently accepted native objects.
    *)
    Theorem typed_model_equalities_reflect_only_with_injections :
      (forall x y : ApplicationIdentity,
          representSource x = representSource y -> x = y) ->
      (forall x y : ManifestIdentity,
          representManifest x = representManifest y -> x = y) ->
      (forall x y : StageClosureObject,
          representStage x = representStage y -> x = y) ->
      (forall x y : Digest,
          representRawSystemsDigest x = representRawSystemsDigest y -> x = y) ->
      (forall x y : Digest,
          representLoweringRoot x = representLoweringRoot y -> x = y) ->
      forall w,
        RepresentedConsumerEqualities w ->
        NativeProducerConsumerBound w.
    Proof.
      intros Hsource Hmanifest Hstage Hraw Hroot w
        [Ha [Hm [Hs [Hd Hr]]]].
      unfold NativeProducerConsumerBound.
      repeat split.
      - apply Hsource. exact Ha.
      - apply Hmanifest. exact Hm.
      - apply Hstage. exact Hs.
      - apply Hraw. exact Hd.
      - apply Hroot. exact Hr.
    Qed.
  End ConditionalModelTransport.

  (*
    Conditional transport of the SEVEN additional, independently typed
    concrete StageClosure coordinates.  These maps are parameters, not
    implemented Haskell encoders or established native authority.
    Source/raw-Systems/lowering-root maps remain separate above.
  *)
  Section ConditionalStageCoordinateTransport.
    Context
      {ModelSubject ModelInstance ModelRealization ModelNormalizedSystems
       ModelCommonContract ModelClosedContract ModelProfile : Type}.
    Context
      (representSubject : SubjectRevision -> ModelSubject)
      (representInstance : StageInstanceRevision -> ModelInstance)
      (representRealization : RealizationRevision -> ModelRealization)
      (representNormalizedSystems : SystemsArtifactRevision -> ModelNormalizedSystems)
      (representCommonContract : Phase1StageContractRevision -> ModelCommonContract)
      (representClosedContract : ClosedStageContractRevision -> ModelClosedContract)
      (representProfile : VerifierProfileRevision -> ModelProfile).

    Definition NativeStageCoordinatesAgree
      (left right : NativeFinalInstanceCoordinates) : Prop :=
      stageSubjectRevision left = stageSubjectRevision right /\
      stageInstanceRevision left = stageInstanceRevision right /\
      stageRealizationRevision left = stageRealizationRevision right /\
      stageNormalizedSystemsRevision left = stageNormalizedSystemsRevision right /\
      stageCommonContractRevision left = stageCommonContractRevision right /\
      stageClosedContractRevision left = stageClosedContractRevision right /\
      stageVerifierProfile left = stageVerifierProfile right.

    Definition RepresentedStageCoordinatesAgree
      (left right : NativeFinalInstanceCoordinates) : Prop :=
      representSubject (stageSubjectRevision left) =
        representSubject (stageSubjectRevision right) /\
      representInstance (stageInstanceRevision left) =
        representInstance (stageInstanceRevision right) /\
      representRealization (stageRealizationRevision left) =
        representRealization (stageRealizationRevision right) /\
      representNormalizedSystems (stageNormalizedSystemsRevision left) =
        representNormalizedSystems (stageNormalizedSystemsRevision right) /\
      representCommonContract (stageCommonContractRevision left) =
        representCommonContract (stageCommonContractRevision right) /\
      representClosedContract (stageClosedContractRevision left) =
        representClosedContract (stageClosedContractRevision right) /\
      representProfile (stageVerifierProfile left) =
        representProfile (stageVerifierProfile right).

    Theorem native_stage_coordinate_equalities_transport :
      forall left right,
        NativeStageCoordinatesAgree left right ->
        RepresentedStageCoordinatesAgree left right.
    Proof.
      intros left right [Hs [Hi [Hr [Hsys [Hcommon [Hclosed Hp]]]]]].
      unfold RepresentedStageCoordinatesAgree.
      repeat split;
        [ now rewrite Hs | now rewrite Hi | now rewrite Hr
        | now rewrite Hsys | now rewrite Hcommon
        | now rewrite Hclosed | now rewrite Hp ].
    Qed.

    (*
      The converse requires a separate injection for every source DOMAIN;
      even all seven injections recover only equalities.  They do not create
      accepted source, stage, or release evidence or authenticate the stage
      occurrence key / stage-production lineage.
    *)
    Theorem represented_stage_coordinates_reflect_only_with_injections :
      (forall x y : SubjectRevision,
        representSubject x = representSubject y -> x = y) ->
      (forall x y : StageInstanceRevision,
        representInstance x = representInstance y -> x = y) ->
      (forall x y : RealizationRevision,
        representRealization x = representRealization y -> x = y) ->
      (forall x y : SystemsArtifactRevision,
        representNormalizedSystems x = representNormalizedSystems y -> x = y) ->
      (forall x y : Phase1StageContractRevision,
        representCommonContract x = representCommonContract y -> x = y) ->
      (forall x y : ClosedStageContractRevision,
        representClosedContract x = representClosedContract y -> x = y) ->
      (forall x y : VerifierProfileRevision,
        representProfile x = representProfile y -> x = y) ->
      forall left right,
        RepresentedStageCoordinatesAgree left right ->
        NativeStageCoordinatesAgree left right.
    Proof.
      intros Hsubject Hinstance Hrealization Hsystems Hcommon Hclosed
        Hprofile left right
        [Hs [Hi [Hr [Hsys [Hc [Hf Hp]]]]]].
      unfold NativeStageCoordinatesAgree.
      repeat split.
      - apply Hsubject. exact Hs.
      - apply Hinstance. exact Hi.
      - apply Hrealization. exact Hr.
      - apply Hsystems. exact Hsys.
      - apply Hcommon. exact Hc.
      - apply Hclosed. exact Hf.
      - apply Hprofile. exact Hp.
    Qed.
  End ConditionalStageCoordinateTransport.

  (*
    A new necessary native gate on the exact, opaque accepted SOURCE assurance
    object, stronger than equality of GenericApplicationIdentity. The model
    only receives this as an explicit predicate; the proof cannot construct
    the native object's acceptance or the source-to-stage origin.
  *)
  Section ExactSourceAssuranceGate.
    Context {SourceAssurance : Type}.
    Context (sourceIdentity : SourceAssurance -> ApplicationIdentity).

    Definition NativeBoundWithExactSource
      (w : NativeFinalInstanceCoordinates)
      (producedSource acceptedSource : SourceAssurance) : Prop :=
      NativeProducerConsumerBound w /\
      producedSource = acceptedSource /\
      sourceIdentity producedSource = acceptedApplication w.

    Theorem exact_source_assurance_gate_preserves_consumer_identity :
      forall w producedSource acceptedSource,
        NativeBoundWithExactSource w producedSource acceptedSource ->
        NativeProducerConsumerBound w /\
        producedSource = acceptedSource /\
        sourceIdentity acceptedSource = producedApplication w.
    Proof.
      intros w producedSource acceptedSource [Hbound [Heq Hidentity]].
      split; [exact Hbound |].
      split; [exact Heq |].
      rewrite <- Heq. rewrite Hidentity.
      exact (proj1 Hbound).
    Qed.

    Theorem different_certified_source_assurance_cannot_bind :
      forall w producedSource acceptedSource,
        producedSource <> acceptedSource ->
        ~ NativeBoundWithExactSource w producedSource acceptedSource.
    Proof.
      intros w producedSource acceptedSource Hneq [_ [Heq _]].
      exact (Hneq Heq).
    Qed.
    (* The public lower-level binder needs the exact opaque source assurance;
       equality of its application identity projection cannot replace it.
       This is conditional model logic, not native authority construction. *)
    Theorem equal_source_identity_cannot_override_exact_binding :
      forall w producedSource acceptedSource,
        sourceIdentity producedSource = sourceIdentity acceptedSource ->
        producedSource <> acceptedSource ->
        ~ NativeBoundWithExactSource w producedSource acceptedSource.
    Proof.
      intros w producedSource acceptedSource _ Hneq Hbound.
      destruct Hbound as [_ [Heq _]].
      apply Hneq. exact Heq.
    Qed.
  End ExactSourceAssuranceGate.

  (*
    One necessary producer-level preservation: retain the entire checked
    ArchitectureInstanceDescriptor, not only its derived occurrence identity.
    Descriptor is an independent type and its identity projection may be
    noninjective in an abstract model. The checked producer, equality and
    descriptor-to-identity relation remain externally supplied premises;
    these lemmas do not construct native acceptance or stage origin.
  *)
  Section ExactCheckedDescriptorRetention.
    Context {ArchitectureInstanceDescriptor : Type}.
    Context (descriptorIdentity :
      ArchitectureInstanceDescriptor -> ArchitectureInstanceIdentity).

    Definition ExactCheckedDescriptorRetained
      (w : NativeFinalInstanceCoordinates)
      (producedDescriptor retainedDescriptor : ArchitectureInstanceDescriptor)
      : Prop :=
      NativeCheckedInstanceProducerBound w /\
      producedDescriptor = retainedDescriptor /\
      descriptorIdentity retainedDescriptor = checkedArchitectureInstance w.

    Theorem exact_checked_descriptor_retention_preserves_bound :
      forall w produced retained,
        ExactCheckedDescriptorRetained w produced retained ->
        NativeCheckedInstanceProducerBound w /\
        produced = retained /\
        descriptorIdentity produced = checkedArchitectureInstance w.
    Proof.
      intros w produced retained [Hnative [Heq Hid]].
      split; [exact Hnative |].
      split; [exact Heq |].
      rewrite Heq. exact Hid.
    Qed.

    Theorem different_checked_descriptor_cannot_bind :
      forall w produced retained,
        produced <> retained ->
        ~ ExactCheckedDescriptorRetained w produced retained.
    Proof.
      intros w produced retained Hdiff [_ [Heq _]].
      exact (Hdiff Heq).
    Qed.

    Theorem equal_descriptor_identity_cannot_override_exact_retention :
      forall w produced retained,
        descriptorIdentity produced = descriptorIdentity retained ->
        produced <> retained ->
        ~ ExactCheckedDescriptorRetained w produced retained.
    Proof.
      intros w produced retained _ Hdiff [_ [Heq _]].
      exact (Hdiff Heq).
    Qed.
  End ExactCheckedDescriptorRetention.


  (*
    A DISTINCT later native boundary: the source-manifest binding retains a
    full checked descriptor, but the final public witness must not project it
    down to an occurrence identity. These are still model premises, not an
    extraction of Haskell data or authority for concrete StageClosure origin.
  *)
  Section SourceTokenToFinalWitnessDescriptor.
    Context {ArchitectureInstanceDescriptor : Type}.
    Context (descriptorIdentity :
      ArchitectureInstanceDescriptor -> ArchitectureInstanceIdentity).

    Definition CheckedDescriptorPreservedToFinalWitness
      (w : NativeFinalInstanceCoordinates)
      (produced token exported : ArchitectureInstanceDescriptor) : Prop :=
      ExactCheckedDescriptorRetained descriptorIdentity w produced token /\
      token = exported.

    Theorem checked_source_descriptor_reaches_final_witness_exactly :
      forall w produced token exported,
        CheckedDescriptorPreservedToFinalWitness w produced token exported ->
        produced = exported /\
        descriptorIdentity exported = checkedArchitectureInstance w /\
        NativeCheckedInstanceProducerBound w.
    Proof.
      intros w produced token exported
        [[Hnative [Hproduced Hidentity]] Hexport].
      split.
      - exact (eq_trans Hproduced Hexport).
      - split.
        + rewrite <- Hexport. exact Hidentity.
        + exact Hnative.
    Qed.

    Theorem final_witness_substituted_descriptor_cannot_bind :
      forall w produced token exported,
        token <> exported ->
        ~ CheckedDescriptorPreservedToFinalWitness w produced token exported.
    Proof.
      intros w produced token exported Hdiff [_ Heq].
      exact (Hdiff Heq).
    Qed.

    Theorem final_witness_identity_projection_cannot_override_exact_descriptor :
      forall w produced token exported,
        descriptorIdentity token = descriptorIdentity exported ->
        token <> exported ->
        ~ CheckedDescriptorPreservedToFinalWitness w produced token exported.
    Proof.
      intros w produced token exported _ Hdiff [_ Heq].
      exact (Hdiff Heq).
    Qed.
  End SourceTokenToFinalWitnessDescriptor.

  (*
    A distinct exact accepted-source preservation boundary: the checked
    source-manifest token carries the complete GenericApplicationAssurance,
    and the exported final witness must retain that same value. No equality of
    application identities can substitute another checked-body assurance.
    The model's producer predicates and object equalities below remain
    explicitly supplied; no concrete Haskell-to-Rocq encoding is postulated.
  *)
  Section SourceTokenToFinalWitnessAssurance.
    Context {SourceAssurance : Type}.
    Context (sourceIdentity : SourceAssurance -> ApplicationIdentity).

    Definition CheckedSourceAssurancePreservedToFinalWitness
      (w : NativeFinalInstanceCoordinates)
      (produced accepted token exported : SourceAssurance) : Prop :=
      NativeBoundWithExactSource sourceIdentity w produced accepted /\
      produced = token /\
      token = exported.

    Theorem checked_source_assurance_reaches_final_witness_exactly :
      forall w produced accepted token exported,
        CheckedSourceAssurancePreservedToFinalWitness
          w produced accepted token exported ->
        exported = accepted /\
        sourceIdentity exported = producedApplication w /\
        NativeProducerConsumerBound w.
    Proof.
      intros w produced accepted token exported
        [[Hbound [Haccepted Hidentity]] [Htoken Hexport]].
      split.
      - rewrite <- Hexport. rewrite <- Htoken. exact Haccepted.
      - split.
        + rewrite <- Hexport. rewrite <- Htoken.
          rewrite Hidentity. exact (proj1 Hbound).
        + exact Hbound.
    Qed.

    Theorem substituted_source_witness_cannot_bind :
      forall w produced accepted token exported,
        token <> exported ->
        ~ CheckedSourceAssurancePreservedToFinalWitness
            w produced accepted token exported.
    Proof.
      intros w produced accepted token exported Hdiff [_ [_ Hexport]].
      exact (Hdiff Hexport).
    Qed.

    Theorem same_source_identity_does_not_override_witness_equality :
      forall w produced accepted token exported,
        sourceIdentity token = sourceIdentity exported ->
        token <> exported ->
        ~ CheckedSourceAssurancePreservedToFinalWitness
            w produced accepted token exported.
    Proof.
      intros w produced accepted token exported _ Hdiff [_ [_ Hexport]].
      exact (Hdiff Hexport).
    Qed.
  End SourceTokenToFinalWitnessAssurance.

  (*
    Independently accepted INT-002 manifest preservation is a distinct
    concrete native boundary from retaining only manifestId. The actual
    Haskell manifest has one Digest type for raw Systems and lowering root;
    the logical projections below intentionally have DIFFERENT codomains.
    Equalities and NativeProducerConsumerBound are EXTERNAL typed premises,
    not derived native acceptance or a Haskell-to-Rocq encoding.
  *)
  Section ManifestTokenToFinalWitness.
    Context {NativeManifest RawSystemsDigest LoweringLedgerRoot : Type}.
    Context (manifestIdentity : NativeManifest -> ManifestIdentity).
    Context (rawSystems : NativeManifest -> RawSystemsDigest).
    Context (loweringRoot : NativeManifest -> LoweringLedgerRoot).

    Definition ExactManifestPreservedToFinalWitness
      (w : NativeFinalInstanceCoordinates)
      (produced token accepted exported : NativeManifest) : Prop :=
      NativeProducerConsumerBound w /\
      produced = token /\
      token = accepted /\
      accepted = exported /\
      manifestIdentity produced = producedManifest w.

    Theorem checked_manifest_reaches_final_witness_exactly :
      forall w produced token accepted exported,
        ExactManifestPreservedToFinalWitness
          w produced token accepted exported ->
        exported = produced /\
        manifestIdentity exported = acceptedReleaseManifest w /\
        rawSystems exported = rawSystems produced /\
        loweringRoot exported = loweringRoot produced /\
        NativeProducerConsumerBound w.
    Proof.
      intros w produced token accepted exported
        [Hbound [Hpt [Hta [Hae Hid]]]].
      assert (Heq : exported = produced).
      { rewrite <- Hae, <- Hta, <- Hpt. reflexivity. }
      split; [exact Heq |].
      split.
      - rewrite Heq. rewrite Hid. exact (proj1 (proj2 Hbound)).
      - split.
        + rewrite Heq. reflexivity.
        + split.
          * rewrite Heq. reflexivity.
          * exact Hbound.
    Qed.

    Theorem substituted_full_manifest_cannot_bind :
      forall w produced token accepted exported,
        accepted <> exported ->
        ~ ExactManifestPreservedToFinalWitness
            w produced token accepted exported.
    Proof.
      intros w produced token accepted exported Hdiff
        [_ [_ [_ [Heq _]]]].
      exact (Hdiff Heq).
    Qed.

    Theorem equal_manifest_id_cannot_override_full_manifest :
      forall w produced token accepted exported,
        manifestIdentity accepted = manifestIdentity exported ->
        accepted <> exported ->
        ~ ExactManifestPreservedToFinalWitness
            w produced token accepted exported.
    Proof.
      intros w produced token accepted exported _ Hdiff
        [_ [_ [_ [Heq _]]]].
      exact (Hdiff Heq).
    Qed.
  End ManifestTokenToFinalWitness.

  (*
    Exact full StageClosure retention across the independently accepted
    VER-010 source / INT-005 release consumers and exported native witness.
    The model's NativeProducerConsumerBound and representation of these
    native objects are EXTERNAL premises. A same closed-contract revision is
    neither full-object equality nor authenticated architecture-stage origin.
  *)
  Section FullStageClosureToFinalWitness.
    Context (closedRevision : StageClosureObject -> ClosedStageContractRevision).

    Definition ExactStageClosurePreservedToFinalWitness
      (w : NativeFinalInstanceCoordinates)
      (source acceptedRelease exported : StageClosureObject) : Prop :=
      NativeProducerConsumerBound w /\
      source = sourceStageClosure w /\
      acceptedRelease = releaseStageClosure w /\
      acceptedRelease = exported.

    Theorem accepted_full_stage_closure_reaches_final_witness :
      forall w source acceptedRelease exported,
        ExactStageClosurePreservedToFinalWitness
          w source acceptedRelease exported ->
        source = exported /\
        exported = releaseStageClosure w /\
        NativeProducerConsumerBound w.
    Proof.
      intros w source acceptedRelease exported
        [Hbound [Hsource [Hrelease Hexport]]].
      assert (Hstage : sourceStageClosure w = releaseStageClosure w).
      { exact (proj1 (proj2 (proj2 Hbound))). }
      split.
      - rewrite Hsource. rewrite Hstage.
        rewrite <- Hrelease. exact Hexport.
      - split.
        + rewrite <- Hexport. exact Hrelease.
        + exact Hbound.
    Qed.

    Theorem substituted_full_stage_closure_cannot_bind :
      forall w source acceptedRelease exported,
        acceptedRelease <> exported ->
        ~ ExactStageClosurePreservedToFinalWitness
            w source acceptedRelease exported.
    Proof.
      intros w source acceptedRelease exported Hdiff
        [_ [_ [_ Heq]]].
      exact (Hdiff Heq).
    Qed.

    Theorem same_closed_revision_cannot_override_full_stage :
      forall w source acceptedRelease exported,
        closedRevision acceptedRelease = closedRevision exported ->
        acceptedRelease <> exported ->
        ~ ExactStageClosurePreservedToFinalWitness
            w source acceptedRelease exported.
    Proof.
      intros w source acceptedRelease exported _ Hdiff
        [_ [_ [_ Heq]]].
      exact (Hdiff Heq).
    Qed.
  End FullStageClosureToFinalWitness.

  (*
    Full independently certified INT-005 release retention at the exported
    native witness boundary. The native release contains LLVM and declared
    residual trust in addition to its manifest and stage. All projections,
    independent certification, and exact accepted-release equality are
    EXTERNAL typed premises; a supplied Prop proves no Haskell acceptance.
  *)
  Section FullCertifiedReleaseToFinalWitness.
    Context {CertifiedReleaseObject : Type}.
    Context (releaseStage : CertifiedReleaseObject -> StageClosureObject).
    Context (releaseManifestId : CertifiedReleaseObject -> ManifestIdentity).
    Context (certifiedByNativeProducer : CertifiedReleaseObject -> Prop).

    Definition ExactCertifiedReleasePreservedToFinalWitness
      (w : NativeFinalInstanceCoordinates)
      (accepted exported : CertifiedReleaseObject) : Prop :=
      NativeProducerConsumerBound w /\
      certifiedByNativeProducer accepted /\
      releaseStage accepted = releaseStageClosure w /\
      releaseManifestId accepted = acceptedReleaseManifest w /\
      accepted = exported.

    Theorem accepted_certified_release_reaches_final_witness_exactly :
      forall w accepted exported,
        ExactCertifiedReleasePreservedToFinalWitness
          w accepted exported ->
        accepted = exported /\
        releaseStage exported = releaseStageClosure w /\
        releaseManifestId exported = acceptedReleaseManifest w /\
        certifiedByNativeProducer accepted /\
        NativeProducerConsumerBound w.
    Proof.
      intros w accepted exported [Hbound [Hcert [Hstage [Hmanifest Heq]]]].
      split; [exact Heq |].
      split; [rewrite <- Heq; exact Hstage |].
      split; [rewrite <- Heq; exact Hmanifest |].
      split; [exact Hcert | exact Hbound].
    Qed.

    Theorem substituted_certified_release_cannot_bind :
      forall w accepted exported,
        accepted <> exported ->
        ~ ExactCertifiedReleasePreservedToFinalWitness
            w accepted exported.
    Proof.
      intros w accepted exported Hdiff [_ [_ [_ [_ Heq]]]].
      exact (Hdiff Heq).
    Qed.

    Theorem same_stage_and_manifest_id_cannot_override_exact_release :
      forall w accepted exported,
        releaseStage accepted = releaseStage exported ->
        releaseManifestId accepted = releaseManifestId exported ->
        accepted <> exported ->
        ~ ExactCertifiedReleasePreservedToFinalWitness
            w accepted exported.
    Proof.
      intros w accepted exported _ _ Hdiff [_ [_ [_ [_ Heq]]]].
      exact (Hdiff Heq).
    Qed.
  End FullCertifiedReleaseToFinalWitness.


  (*
    Another DISTINCT accepted native envelope: VER-010 certification binds
    complete accepted source proof to one exact StageClosure. Even though
    the previous witness retained both projections, those projections were
    not themselves a retained independently certified source object.
    Abstract object/acceptance/equalities below are explicit EXTERNAL
    premises, NOT a native producer, extraction, or Haskell-to-Rocq encoding.
  *)
  Section FullCertifiedSourceToFinalWitness.
    Context {CertifiedSourceObject SourceAssuranceObject : Type}.
    Context (sourceProof : CertifiedSourceObject -> SourceAssuranceObject).
    Context (sourceProofIdentity : SourceAssuranceObject -> ApplicationIdentity).
    Context (sourceStage : CertifiedSourceObject -> StageClosureObject).
    Context (acceptedByNativeSourceProducer : CertifiedSourceObject -> Prop).

    Definition ExactCertifiedSourcePreservedToFinalWitness
      (w : NativeFinalInstanceCoordinates)
      (accepted exported : CertifiedSourceObject) : Prop :=
      NativeProducerConsumerBound w /\
      acceptedByNativeSourceProducer accepted /\
      sourceProofIdentity (sourceProof accepted) = acceptedApplication w /\
      sourceStage accepted = sourceStageClosure w /\
      accepted = exported.

    Theorem accepted_certified_source_reaches_final_witness_exactly :
      forall w accepted exported,
        ExactCertifiedSourcePreservedToFinalWitness
          w accepted exported ->
        accepted = exported /\
        sourceProof exported = sourceProof accepted /\
        sourceStage exported = releaseStageClosure w /\
        acceptedByNativeSourceProducer accepted /\
        NativeProducerConsumerBound w.
    Proof.
      intros w accepted exported [Hbound [Hcert [Hsource [Hstage Heq]]]].
      split; [exact Heq |].
      split; [rewrite <- Heq; reflexivity |].
      split.
      - rewrite <- Heq. rewrite Hstage.
        exact (proj1 (proj2 (proj2 Hbound))).
      - split; [exact Hcert | exact Hbound].
    Qed.

    Theorem substituted_certified_source_cannot_bind :
      forall w accepted exported,
        accepted <> exported ->
        ~ ExactCertifiedSourcePreservedToFinalWitness
            w accepted exported.
    Proof.
      intros w accepted exported Hdiff [_ [_ [_ [_ Heq]]]].
      exact (Hdiff Heq).
    Qed.

    Theorem same_source_proof_cannot_override_certified_source_envelope :
      forall w accepted exported,
        sourceProof accepted = sourceProof exported ->
        accepted <> exported ->
        ~ ExactCertifiedSourcePreservedToFinalWitness
            w accepted exported.
    Proof.
      intros w accepted exported _ Hdiff [_ [_ [_ [_ Heq]]]].
      exact (Hdiff Heq).
    Qed.

    Theorem source_envelope_stage_drift_blocks_exact_retention :
      forall w accepted exported,
        sourceStage accepted <> sourceStageClosure w ->
        ~ ExactCertifiedSourcePreservedToFinalWitness
            w accepted exported.
    Proof.
      intros w accepted exported Hdiff [_ [_ [_ [Heq _]]]].
      exact (Hdiff Heq).
    Qed.
  End FullCertifiedSourceToFinalWitness.


  (*
    Preserve the exact opaque checked-instance source-manifest producer token
    across the final witness. Source and manifest projection equality alone is
    insufficient: the declaration-only native producer can share both while
    lacking the checked descriptor. All object representations and the native
    checked-producer predicate remain EXTERNAL typed premises; this model does
    not create native authority or StageClosure provenance.
  *)
  Section FullCheckedSourceManifestBindingToFinalWitness.
    Context
      {SourceManifestBindingObject SourceAssuranceObject NativeManifest
       ArchitectureInstanceDescriptor : Type}.
    Context (bindingSource :
      SourceManifestBindingObject -> SourceAssuranceObject).
    Context (bindingManifest :
      SourceManifestBindingObject -> NativeManifest).
    Context (bindingDescriptor :
      SourceManifestBindingObject -> option ArchitectureInstanceDescriptor).
    Context (sourceIdentity :
      SourceAssuranceObject -> ApplicationIdentity).
    Context (manifestIdentity :
      NativeManifest -> ManifestIdentity).
    Context (descriptorIdentity :
      ArchitectureInstanceDescriptor -> ArchitectureInstanceIdentity).
    Context (checkedByNativeInstanceProducer :
      SourceManifestBindingObject -> Prop).

    Definition ExactCheckedSourceManifestBindingPreservedToFinalWitness
      (w : NativeFinalInstanceCoordinates)
      (checked exported : SourceManifestBindingObject) : Prop :=
      NativeProducerConsumerBound w /\
      checkedByNativeInstanceProducer checked /\
      sourceIdentity (bindingSource checked) = producedApplication w /\
      manifestIdentity (bindingManifest checked) = producedManifest w /\
      (exists descriptor,
        bindingDescriptor checked = Some descriptor /\
        descriptorIdentity descriptor = checkedArchitectureInstance w) /\
      checked = exported.

    Theorem checked_source_manifest_binding_reaches_final_witness_exactly :
      forall w checked exported,
        ExactCheckedSourceManifestBindingPreservedToFinalWitness
          w checked exported ->
        checked = exported /\
        sourceIdentity (bindingSource exported) = producedApplication w /\
        manifestIdentity (bindingManifest exported) = producedManifest w /\
        (exists descriptor,
          bindingDescriptor exported = Some descriptor /\
          descriptorIdentity descriptor = checkedArchitectureInstance w) /\
        checkedByNativeInstanceProducer checked /\
        NativeProducerConsumerBound w.
    Proof.
      intros w checked exported
        [Hbound [Hchecked [Hsource [Hmanifest [Hdescriptor Heq]]]]].
      split; [exact Heq |].
      split.
      - rewrite <- Heq. exact Hsource.
      - split.
        + rewrite <- Heq. exact Hmanifest.
        + split.
          * destruct Hdescriptor as [descriptor [Hsome Hid]].
            exists descriptor. rewrite <- Heq. split; assumption.
          * split; [exact Hchecked | exact Hbound].
    Qed.

    Theorem substituted_checked_source_manifest_binding_cannot_bind :
      forall w checked exported,
        checked <> exported ->
        ~ ExactCheckedSourceManifestBindingPreservedToFinalWitness
            w checked exported.
    Proof.
      intros w checked exported Hdiff
        [_ [_ [_ [_ [_ Heq]]]]].
      exact (Hdiff Heq).
    Qed.

    Theorem declaration_only_binding_cannot_replace_checked_instance_token :
      forall w checked exported,
        bindingDescriptor exported = None ->
        ~ ExactCheckedSourceManifestBindingPreservedToFinalWitness
            w checked exported.
    Proof.
      intros w checked exported Hnone
        [_ [_ [_ [_ [Hdescriptor Heq]]]]].
      destruct Hdescriptor as [descriptor [Hsome _]].
      rewrite Heq in Hsome. rewrite Hnone in Hsome. discriminate.
    Qed.

    Theorem same_source_and_manifest_cannot_upgrade_declaration_only_binding :
      forall w checked exported,
        bindingSource checked = bindingSource exported ->
        bindingManifest checked = bindingManifest exported ->
        bindingDescriptor exported = None ->
        ~ ExactCheckedSourceManifestBindingPreservedToFinalWitness
            w checked exported.
    Proof.
      intros w checked exported _ _ Hnone.
      now apply declaration_only_binding_cannot_replace_checked_instance_token.
    Qed.
  End FullCheckedSourceManifestBindingToFinalWitness.

End NativeFinalInstanceTypedCorrespondence.

(*
  Separately typed model of the native replay of *actual full objects*:
  checked source-manifest producer, independently accepted VER-010 source,
  independently accepted INT-005 release, raw Systems digest, lowering root,
  normalized Systems revision and the three distinct stage contract identities.
  This conditional theorem is NOT a Haskell extraction, acceptance producer,
  instance-to-stage origin proof, or conversion into nat.
*)
Section NativeExactManifestStageReplay.
  Context
    {CheckedProducer NativeManifest NativeStage CertifiedSource CertifiedRelease
     NativeRawDigest NativeLoweringRoot SubjectRevision StageInstanceRevision
     RealizationRevision NormalizedSystemsRevision CommonStageContractRevision
     ClosedStageContractRevision VerifierProfileRevision : Type}.
  Context (producerManifest : CheckedProducer -> NativeManifest).
  Context (releaseManifest : CertifiedRelease -> NativeManifest).
  Context (sourceStage : CertifiedSource -> NativeStage).
  Context (releaseStage : CertifiedRelease -> NativeStage).
  Context (manifestRaw : NativeManifest -> NativeRawDigest).
  Context (stageRaw : NativeStage -> NativeRawDigest).
  Context (manifestRoot : NativeManifest -> NativeLoweringRoot).
  Context (stageRoot : NativeStage -> NativeLoweringRoot).
  Context (stageSubject : NativeStage -> SubjectRevision).
  Context (stageInstance : NativeStage -> StageInstanceRevision).
  Context (stageRealization : NativeStage -> RealizationRevision).
  Context (stageSystems : NativeStage -> NormalizedSystemsRevision).
  Context (stageCommon : NativeStage -> CommonStageContractRevision).
  Context (stageClosed : NativeStage -> ClosedStageContractRevision).
  Context (stageProfile : NativeStage -> VerifierProfileRevision).

  (* All six premises are external representations of distinct native
     *object-level* gates. A model Prop cannot establish that the input
     constructors were accepted by Haskell or that this stage was produced
     by the checked architecture occurrence. *)
  Definition NativeExactManifestStageReplayBound
    (producer : CheckedProducer) (source : CertifiedSource)
    (release : CertifiedRelease) (manifest : NativeManifest)
    (stage : NativeStage) : Prop :=
      producerManifest producer = manifest /\
      releaseManifest release = manifest /\
      sourceStage source = stage /\
      releaseStage release = stage /\
      manifestRaw manifest = stageRaw stage /\
      manifestRoot manifest = stageRoot stage.

  Theorem exact_manifest_stage_replay_preserves_full_consumers :
    forall producer source release manifest stage,
      NativeExactManifestStageReplayBound producer source release manifest stage ->
      producerManifest producer = releaseManifest release /\
      sourceStage source = releaseStage release /\
      manifestRaw manifest = stageRaw stage /\
      manifestRoot manifest = stageRoot stage.
  Proof.
    intros producer source release manifest stage
      [Hproducer [Hrelease [Hsource [Hstage [Hraw Hroot]]]]].
    repeat split.
    - rewrite Hproducer, Hrelease. reflexivity.
    - rewrite Hsource, Hstage. reflexivity.
    - exact Hraw.
    - exact Hroot.
  Qed.

  Theorem native_replay_raw_systems_drift_rejected :
    forall producer source release manifest stage,
      manifestRaw manifest <> stageRaw stage ->
      ~ NativeExactManifestStageReplayBound producer source release manifest stage.
  Proof.
    intros producer source release manifest stage Hneq
      [_ [_ [_ [_ [Heq _]]]]].
    exact (Hneq Heq).
  Qed.

  Theorem native_replay_lowering_root_drift_rejected :
    forall producer source release manifest stage,
      manifestRoot manifest <> stageRoot stage ->
      ~ NativeExactManifestStageReplayBound producer source release manifest stage.
  Proof.
    intros producer source release manifest stage Hneq
      [_ [_ [_ [_ [_ Heq]]]]].
    exact (Hneq Heq).
  Qed.

  Theorem equal_raw_and_root_cannot_replace_full_manifest :
    forall producer source release manifest stage,
      producerManifest producer <> manifest ->
      manifestRaw (producerManifest producer) = manifestRaw manifest ->
      manifestRoot (producerManifest producer) = manifestRoot manifest ->
      ~ NativeExactManifestStageReplayBound producer source release manifest stage.
  Proof.
    intros producer source release manifest stage Hneq _ _
      [Heq _].
    exact (Hneq Heq).
  Qed.

  Theorem exact_release_stage_preserves_separately_typed_stage_coordinates :
    forall producer source release manifest stage,
      NativeExactManifestStageReplayBound producer source release manifest stage ->
      stageSubject stage = stageSubject (releaseStage release) /\
      stageInstance stage = stageInstance (releaseStage release) /\
      stageRealization stage = stageRealization (releaseStage release) /\
      stageSystems stage = stageSystems (releaseStage release) /\
      stageCommon stage = stageCommon (releaseStage release) /\
      stageClosed stage = stageClosed (releaseStage release) /\
      stageProfile stage = stageProfile (releaseStage release).
  Proof.
    intros producer source release manifest stage
      [_ [_ [_ [Hstage _]]]].
    rewrite Hstage. repeat split; reflexivity.
  Qed.
End NativeExactManifestStageReplay.

(* A concrete logical counterexample, NOT an encoding of Haskell identity
   values into nat: two distinct occurrence keys can carry one revision.
   The actual native equality decision also compares the occurrence key. *)
Record RevisionCollisionOccurrence := {
  collisionKey : nat;
  collisionRevision : nat
}.

Theorem same_revision_does_not_identify_occurrence :
  exists a b : RevisionCollisionOccurrence,
    collisionRevision a = collisionRevision b /\
    collisionKey a <> collisionKey b.
Proof.
  exists {| collisionKey := 1; collisionRevision := 3 |}.
  exists {| collisionKey := 2; collisionRevision := 3 |}.
  simpl. split; [reflexivity | discriminate].
Qed.

(*
  Logical counterexample, not an encoding of native Haskell Digests.
  A non-injective model representation can make distinct native values look
  equal. Model equality alone therefore cannot authenticate native equality.
*)
Theorem noninjective_representation_hides_digest_drift :
  exists (representation : bool -> unit) (sourceDigest stageDigest : bool),
    sourceDigest <> stageDigest /\
    representation sourceDigest = representation stageDigest.
Proof.
  exists (fun _ : bool => tt), true, false.
  split; [discriminate | reflexivity].
Qed.


(*
  Typed logical example, NOT Haskell revision encodings.  Even distinct
  native/common and closed-stage model domains can each be noninjective:
  their two image equalities do not force either native revision equality.
*)
Inductive ExampleNativeCommonStage : Type :=
  | NativeCommonA | NativeCommonB.
Inductive ExampleNativeClosedStage : Type :=
  | NativeClosedA | NativeClosedB.
Inductive ExampleModelCommonStage : Type := ModelCommonOnly.
Inductive ExampleModelClosedStage : Type := ModelClosedOnly.

Theorem separate_noninjective_stage_models_hide_common_and_closed_drift :
  exists
    (commonModel : ExampleNativeCommonStage -> ExampleModelCommonStage)
    (closedModel : ExampleNativeClosedStage -> ExampleModelClosedStage),
    NativeCommonA <> NativeCommonB /\
    NativeClosedA <> NativeClosedB /\
    commonModel NativeCommonA = commonModel NativeCommonB /\
    closedModel NativeClosedA = closedModel NativeClosedB.
Proof.
  exists (fun _ => ModelCommonOnly), (fun _ => ModelClosedOnly).
  repeat split; try discriminate; reflexivity.
Qed.

(* Logical collision only: distinct assurance objects can have identical
   application identities. No bool/unit is a Haskell/Rocq encoding. *)
Theorem equal_application_identity_does_not_authenticate_source_assurance :
  exists (sourceIdentity : bool -> unit)
         (producedSource acceptedSource : bool),
    producedSource <> acceptedSource /\
    sourceIdentity producedSource = sourceIdentity acceptedSource.
Proof.
  exists (fun _ : bool => tt), true, false.
  split; [discriminate | reflexivity].
Qed.

(* Logical collision only: identity equality does not establish descriptor
   equality without a proved injectivity premise. No Haskell encoder here. *)
Theorem equal_architecture_identity_does_not_authenticate_descriptor :
  exists (descriptorIdentity : bool -> unit)
         (producedDescriptor retainedDescriptor : bool),
    producedDescriptor <> retainedDescriptor /\
    descriptorIdentity producedDescriptor =
      descriptorIdentity retainedDescriptor.
Proof.
  exists (fun _ : bool => tt), true, false.
  split; [discriminate | reflexivity].
Qed.

(* #1584: exact *whole native object* replay is stronger than coordinate
   replay. Every equality below is a typed external premise; the model never
   constructs a checked producer, certified source or selected release. *)
Section NativeExactAcceptedConsumerObjectReplay.
  Context {CheckedSourceManifestToken CertifiedSourceObject
           CertifiedReleaseObject NativeManifest NativeStage
           NativeReleaseTrust : Type}.
  Context (producerManifest : CheckedSourceManifestToken -> NativeManifest).
  Context (sourceStage : CertifiedSourceObject -> NativeStage).
  Context (releaseManifest : CertifiedReleaseObject -> NativeManifest).
  Context (releaseStage : CertifiedReleaseObject -> NativeStage).
  Context (releaseTrust : CertifiedReleaseObject -> NativeReleaseTrust).

  Definition NativeExactAcceptedConsumerObjectsBound
    (retainedProducer suppliedProducer : CheckedSourceManifestToken)
    (retainedSource suppliedSource : CertifiedSourceObject)
    (retainedRelease suppliedRelease : CertifiedReleaseObject) : Prop :=
      retainedProducer = suppliedProducer /\
      retainedSource = suppliedSource /\
      retainedRelease = suppliedRelease /\
      producerManifest retainedProducer = releaseManifest retainedRelease /\
      sourceStage retainedSource = releaseStage retainedRelease.

  Theorem exact_accepted_consumer_replay_retains_all_full_objects :
    forall retainedProducer suppliedProducer retainedSource suppliedSource
           retainedRelease suppliedRelease,
      NativeExactAcceptedConsumerObjectsBound
        retainedProducer suppliedProducer retainedSource suppliedSource
        retainedRelease suppliedRelease ->
      retainedProducer = suppliedProducer /\
      retainedSource = suppliedSource /\
      retainedRelease = suppliedRelease.
  Proof.
    intros rp cp rs cs rr cr [Hp [Hs [Hr _]]].
    repeat split; assumption.
  Qed.

  Theorem same_full_manifest_cannot_replace_checked_producer :
    forall retainedProducer suppliedProducer retainedSource suppliedSource
           retainedRelease suppliedRelease,
      retainedProducer <> suppliedProducer ->
      producerManifest retainedProducer = producerManifest suppliedProducer ->
      ~ NativeExactAcceptedConsumerObjectsBound
          retainedProducer suppliedProducer retainedSource suppliedSource
          retainedRelease suppliedRelease.
  Proof.
    intros rp cp rs cs rr cr Hdiff _ [Heq _].
    exact (Hdiff Heq).
  Qed.

  Theorem same_source_stage_cannot_replace_certified_source_object :
    forall retainedProducer suppliedProducer retainedSource suppliedSource
           retainedRelease suppliedRelease,
      retainedSource <> suppliedSource ->
      sourceStage retainedSource = sourceStage suppliedSource ->
      ~ NativeExactAcceptedConsumerObjectsBound
          retainedProducer suppliedProducer retainedSource suppliedSource
          retainedRelease suppliedRelease.
  Proof.
    intros rp cp rs cs rr cr Hdiff _ [_ [Heq _]].
    exact (Hdiff Heq).
  Qed.

  Theorem same_release_manifest_stage_cannot_replace_trust_different_release :
    forall retainedProducer suppliedProducer retainedSource suppliedSource
           retainedRelease suppliedRelease,
      releaseManifest retainedRelease = releaseManifest suppliedRelease ->
      releaseStage retainedRelease = releaseStage suppliedRelease ->
      releaseTrust retainedRelease <> releaseTrust suppliedRelease ->
      ~ NativeExactAcceptedConsumerObjectsBound
          retainedProducer suppliedProducer retainedSource suppliedSource
          retainedRelease suppliedRelease.
  Proof.
    intros rp cp rs cs rr cr _ _ Hdiff [_ [_ [Heq _]]].
    apply Hdiff. now rewrite Heq.
  Qed.
End NativeExactAcceptedConsumerObjectReplay.

(*
  #1584: the FIRST concrete native-to-model data-wire slice covers ONLY
  native raw Systems Digest versus lowering-ledger-root Digest. Both native
  values are Text under distinct Haskell newtypes; the existing replay reads
  them from independently accepted manifest/stage objects. We can prove the
  role-tag constructor is injective and disjoint for Rocq string payloads,
  without inventing a nat encoding, authority predicate or equality between
  these two digest domains. A full Unicode Text <-> Rocq string reflection
  and accepted-object representation remain independent premises.
*)
From Stdlib Require Import Strings.String Strings.Ascii.
Open Scope string_scope.

Record NativeRawSystemsDigestRole := mkNativeRawSystemsDigestRole {
  rawSystemsDigestPayload : string
}.
Record NativeLoweringRootDigestRole := mkNativeLoweringRootDigestRole {
  loweringRootDigestPayload : string
}.

Definition nativeRawSystemsDigestWire (d : NativeRawSystemsDigestRole) : string :=
  "R" ++ rawSystemsDigestPayload d.
Definition nativeLoweringRootWire (d : NativeLoweringRootDigestRole) : string :=
  "L" ++ loweringRootDigestPayload d.

Definition nativeDecodeRawSystemsDigestWire (wire : string)
  : option NativeRawSystemsDigestRole :=
  match wire with
  | EmptyString => None
  | String role payload =>
      if Ascii.eqb role "R"%char
      then Some (mkNativeRawSystemsDigestRole payload)
      else None
  end.

Definition nativeDecodeLoweringRootWire (wire : string)
  : option NativeLoweringRootDigestRole :=
  match wire with
  | EmptyString => None
  | String role payload =>
      if Ascii.eqb role "L"%char
      then Some (mkNativeLoweringRootDigestRole payload)
      else None
  end.

Theorem native_raw_digest_wire_injective :
  forall a b, nativeRawSystemsDigestWire a = nativeRawSystemsDigestWire b -> a = b.
Proof.
  intros [a] [b] H.
  unfold nativeRawSystemsDigestWire in H.
  simpl in H.
  injection H as Heq. now subst.
Qed.

Theorem native_lowering_root_wire_injective :
  forall a b, nativeLoweringRootWire a = nativeLoweringRootWire b -> a = b.
Proof.
  intros [a] [b] H.
  unfold nativeLoweringRootWire in H.
  simpl in H.
  injection H as Heq. now subst.
Qed.

Theorem native_raw_digest_wire_roundtrip :
  forall a, nativeDecodeRawSystemsDigestWire (nativeRawSystemsDigestWire a) = Some a.
Proof. intros [a]. reflexivity. Qed.

Theorem native_lowering_root_wire_roundtrip :
  forall a, nativeDecodeLoweringRootWire (nativeLoweringRootWire a) = Some a.
Proof. intros [a]. reflexivity. Qed.

Theorem native_digest_roles_have_disjoint_wires :
  forall raw root, nativeRawSystemsDigestWire raw <> nativeLoweringRootWire root.
Proof.
  intros [raw] [root] H.
  unfold nativeRawSystemsDigestWire, nativeLoweringRootWire in H.
  simpl in H. discriminate H.
Qed.

Theorem native_wrong_role_decoding_fails :
  forall raw root,
    nativeDecodeRawSystemsDigestWire (nativeLoweringRootWire root) = None /\
    nativeDecodeLoweringRootWire (nativeRawSystemsDigestWire raw) = None.
Proof. intros [raw] [root]. split; reflexivity. Qed.
