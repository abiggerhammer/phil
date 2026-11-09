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

(*
  #1584: second narrowly bounded native data-wire fragment. The native Haskell
  newtypes SystemsArtifactRevision, Phase1StageContractRevision, and
  ClosedStageContractRevision each wrap Text but carry INDEPENDENT meanings.
  The S/C/F ASCII role tags are reversible and disjoint from one another and
  the R/L raw digest/lowering-root tags. The string model proves algebraic
  properties of the wire shape ONLY; it does not assume a Unicode Text ->
  Rocq string serializer, independently accepted stage-production authority,
  or a native digest/revision -> nat encoding.
*)
Record NativeSystemsRevisionRole := mkNativeSystemsRevisionRole {
  systemsRevisionPayload : string
}.
Record NativeCommonRevisionRole := mkNativeCommonRevisionRole {
  commonRevisionPayload : string
}.
Record NativeClosedRevisionRole := mkNativeClosedRevisionRole {
  closedRevisionPayload : string
}.

Definition nativeSystemsRevisionWire (r : NativeSystemsRevisionRole) : string :=
  "S" ++ systemsRevisionPayload r.
Definition nativeCommonRevisionWire (r : NativeCommonRevisionRole) : string :=
  "C" ++ commonRevisionPayload r.
Definition nativeClosedRevisionWire (r : NativeClosedRevisionRole) : string :=
  "F" ++ closedRevisionPayload r.

Definition nativeDecodeSystemsRevisionWire (wire : string)
  : option NativeSystemsRevisionRole :=
  match wire with
  | EmptyString => None
  | String role payload =>
      if Ascii.eqb role "S"%char
      then Some (mkNativeSystemsRevisionRole payload)
      else None
  end.
Definition nativeDecodeCommonRevisionWire (wire : string)
  : option NativeCommonRevisionRole :=
  match wire with
  | EmptyString => None
  | String role payload =>
      if Ascii.eqb role "C"%char
      then Some (mkNativeCommonRevisionRole payload)
      else None
  end.
Definition nativeDecodeClosedRevisionWire (wire : string)
  : option NativeClosedRevisionRole :=
  match wire with
  | EmptyString => None
  | String role payload =>
      if Ascii.eqb role "F"%char
      then Some (mkNativeClosedRevisionRole payload)
      else None
  end.

Theorem native_systems_revision_wire_injective :
  forall a b, nativeSystemsRevisionWire a = nativeSystemsRevisionWire b -> a = b.
Proof.
  intros [a] [b] H.
  unfold nativeSystemsRevisionWire in H.
  simpl in H.
  injection H as Heq. now subst.
Qed.
Theorem native_common_revision_wire_injective :
  forall a b, nativeCommonRevisionWire a = nativeCommonRevisionWire b -> a = b.
Proof.
  intros [a] [b] H.
  unfold nativeCommonRevisionWire in H.
  simpl in H.
  injection H as Heq. now subst.
Qed.
Theorem native_closed_revision_wire_injective :
  forall a b, nativeClosedRevisionWire a = nativeClosedRevisionWire b -> a = b.
Proof.
  intros [a] [b] H.
  unfold nativeClosedRevisionWire in H.
  simpl in H.
  injection H as Heq. now subst.
Qed.

Theorem native_systems_revision_wire_roundtrip :
  forall a, nativeDecodeSystemsRevisionWire (nativeSystemsRevisionWire a) = Some a.
Proof. intros [a]. reflexivity. Qed.
Theorem native_common_revision_wire_roundtrip :
  forall a, nativeDecodeCommonRevisionWire (nativeCommonRevisionWire a) = Some a.
Proof. intros [a]. reflexivity. Qed.
Theorem native_closed_revision_wire_roundtrip :
  forall a, nativeDecodeClosedRevisionWire (nativeClosedRevisionWire a) = Some a.
Proof. intros [a]. reflexivity. Qed.

Theorem native_revision_role_wires_pairwise_disjoint :
  forall s c f,
    nativeSystemsRevisionWire s <> nativeCommonRevisionWire c /\
    nativeSystemsRevisionWire s <> nativeClosedRevisionWire f /\
    nativeCommonRevisionWire c <> nativeClosedRevisionWire f.
Proof.
  intros [s] [c] [f].
  repeat split; intro H;
    unfold nativeSystemsRevisionWire, nativeCommonRevisionWire,
      nativeClosedRevisionWire in H;
    simpl in H; discriminate H.
Qed.

Theorem native_revision_wrong_role_decoding_fails :
  forall s c f,
    nativeDecodeSystemsRevisionWire (nativeCommonRevisionWire c) = None /\
    nativeDecodeSystemsRevisionWire (nativeClosedRevisionWire f) = None /\
    nativeDecodeCommonRevisionWire (nativeSystemsRevisionWire s) = None /\
    nativeDecodeCommonRevisionWire (nativeClosedRevisionWire f) = None /\
    nativeDecodeClosedRevisionWire (nativeSystemsRevisionWire s) = None /\
    nativeDecodeClosedRevisionWire (nativeCommonRevisionWire c) = None.
Proof. intros [s] [c] [f]. repeat split; reflexivity. Qed.

Theorem native_revision_and_digest_wire_images_disjoint :
  forall raw root s c f,
    nativeRawSystemsDigestWire raw <> nativeSystemsRevisionWire s /\
    nativeRawSystemsDigestWire raw <> nativeCommonRevisionWire c /\
    nativeRawSystemsDigestWire raw <> nativeClosedRevisionWire f /\
    nativeLoweringRootWire root <> nativeSystemsRevisionWire s /\
    nativeLoweringRootWire root <> nativeCommonRevisionWire c /\
    nativeLoweringRootWire root <> nativeClosedRevisionWire f.
Proof.
  intros [raw] [root] [s] [c] [f].
  repeat split; intro H;
    unfold nativeRawSystemsDigestWire, nativeLoweringRootWire,
      nativeSystemsRevisionWire, nativeCommonRevisionWire,
      nativeClosedRevisionWire in H;
    simpl in H; discriminate H.
Qed.

(* #1584: a third, separate role-tagged NATIVE DATA fragment. Concrete
   StageClosure subject/instance/realization revisions are distinct Haskell
   Text newtypes. InstanceRevision is NOT an occurrence InstanceKey.
   B/I/A tags preserve the entire payload; the Rocq string representation
   here is a conditional string model, not a proof of Haskell Unicode
   serialization or authenticated StageClosure production. *)
Record NativeSubjectRevisionRole := mkNativeSubjectRevisionRole {
  nativeSubjectRevisionPayload : string
}.
Record NativeInstanceRevisionRole := mkNativeInstanceRevisionRole {
  nativeInstanceRevisionPayload : string
}.
Record NativeRealizationRevisionRole := mkNativeRealizationRevisionRole {
  nativeRealizationRevisionPayload : string
}.

Definition nativeSubjectRevisionWire (r : NativeSubjectRevisionRole) : string :=
  "B" ++ nativeSubjectRevisionPayload r.
Definition nativeInstanceRevisionWire (r : NativeInstanceRevisionRole) : string :=
  "I" ++ nativeInstanceRevisionPayload r.
Definition nativeRealizationRevisionWire (r : NativeRealizationRevisionRole) : string :=
  "A" ++ nativeRealizationRevisionPayload r.

Definition nativeDecodeSubjectRevisionWire (wire : string)
  : option NativeSubjectRevisionRole :=
  match wire with
  | EmptyString => None
  | String role payload =>
      if Ascii.eqb role "B"%char
      then Some (mkNativeSubjectRevisionRole payload)
      else None
  end.
Definition nativeDecodeInstanceRevisionWire (wire : string)
  : option NativeInstanceRevisionRole :=
  match wire with
  | EmptyString => None
  | String role payload =>
      if Ascii.eqb role "I"%char
      then Some (mkNativeInstanceRevisionRole payload)
      else None
  end.
Definition nativeDecodeRealizationRevisionWire (wire : string)
  : option NativeRealizationRevisionRole :=
  match wire with
  | EmptyString => None
  | String role payload =>
      if Ascii.eqb role "A"%char
      then Some (mkNativeRealizationRevisionRole payload)
      else None
  end.

Theorem native_subject_revision_wire_injective :
  forall a b, nativeSubjectRevisionWire a = nativeSubjectRevisionWire b -> a = b.
Proof.
  intros [a] [b] H.
  unfold nativeSubjectRevisionWire in H.
  simpl in H. injection H as Heq. now subst.
Qed.
Theorem native_instance_revision_wire_injective :
  forall a b, nativeInstanceRevisionWire a = nativeInstanceRevisionWire b -> a = b.
Proof.
  intros [a] [b] H.
  unfold nativeInstanceRevisionWire in H.
  simpl in H. injection H as Heq. now subst.
Qed.
Theorem native_realization_revision_wire_injective :
  forall a b, nativeRealizationRevisionWire a = nativeRealizationRevisionWire b -> a = b.
Proof.
  intros [a] [b] H.
  unfold nativeRealizationRevisionWire in H.
  simpl in H. injection H as Heq. now subst.
Qed.

Theorem native_subject_revision_wire_roundtrip :
  forall a, nativeDecodeSubjectRevisionWire (nativeSubjectRevisionWire a) = Some a.
Proof. intros [a]. reflexivity. Qed.
Theorem native_instance_revision_wire_roundtrip :
  forall a, nativeDecodeInstanceRevisionWire (nativeInstanceRevisionWire a) = Some a.
Proof. intros [a]. reflexivity. Qed.
Theorem native_realization_revision_wire_roundtrip :
  forall a, nativeDecodeRealizationRevisionWire (nativeRealizationRevisionWire a) = Some a.
Proof. intros [a]. reflexivity. Qed.

Theorem native_stage_identity_wires_disjoint :
  forall s i r,
    nativeSubjectRevisionWire s <> nativeInstanceRevisionWire i /\
    nativeSubjectRevisionWire s <> nativeRealizationRevisionWire r /\
    nativeInstanceRevisionWire i <> nativeRealizationRevisionWire r.
Proof.
  intros [s] [i] [r].
  repeat split; intro H;
    unfold nativeSubjectRevisionWire, nativeInstanceRevisionWire,
      nativeRealizationRevisionWire in H;
    simpl in H; discriminate H.
Qed.

Theorem native_stage_identity_wrong_role_decoding_fails :
  forall s i r,
    nativeDecodeSubjectRevisionWire (nativeInstanceRevisionWire i) = None /\
    nativeDecodeSubjectRevisionWire (nativeRealizationRevisionWire r) = None /\
    nativeDecodeInstanceRevisionWire (nativeSubjectRevisionWire s) = None /\
    nativeDecodeInstanceRevisionWire (nativeRealizationRevisionWire r) = None /\
    nativeDecodeRealizationRevisionWire (nativeSubjectRevisionWire s) = None /\
    nativeDecodeRealizationRevisionWire (nativeInstanceRevisionWire i) = None.
Proof. intros [s] [i] [r]. repeat split; reflexivity. Qed.

Theorem native_stage_identity_and_digest_revision_wires_disjoint :
  forall raw root sys common closed subject inst real,
    nativeSubjectRevisionWire subject <> nativeRawSystemsDigestWire raw /\
    nativeSubjectRevisionWire subject <> nativeLoweringRootWire root /\
    nativeSubjectRevisionWire subject <> nativeSystemsRevisionWire sys /\
    nativeSubjectRevisionWire subject <> nativeCommonRevisionWire common /\
    nativeSubjectRevisionWire subject <> nativeClosedRevisionWire closed /\
    nativeInstanceRevisionWire inst <> nativeRawSystemsDigestWire raw /\
    nativeInstanceRevisionWire inst <> nativeLoweringRootWire root /\
    nativeInstanceRevisionWire inst <> nativeSystemsRevisionWire sys /\
    nativeInstanceRevisionWire inst <> nativeCommonRevisionWire common /\
    nativeInstanceRevisionWire inst <> nativeClosedRevisionWire closed /\
    nativeRealizationRevisionWire real <> nativeRawSystemsDigestWire raw /\
    nativeRealizationRevisionWire real <> nativeLoweringRootWire root /\
    nativeRealizationRevisionWire real <> nativeSystemsRevisionWire sys /\
    nativeRealizationRevisionWire real <> nativeCommonRevisionWire common /\
    nativeRealizationRevisionWire real <> nativeClosedRevisionWire closed.
Proof.
  intros [raw] [root] [sys] [common] [closed] [subject] [inst] [real].
  repeat split; intro H;
    unfold nativeSubjectRevisionWire, nativeInstanceRevisionWire,
      nativeRealizationRevisionWire, nativeRawSystemsDigestWire,
      nativeLoweringRootWire, nativeSystemsRevisionWire,
      nativeCommonRevisionWire, nativeClosedRevisionWire in H;
    simpl in H; discriminate H.
Qed.

(* #1584: The actual native Phase1Stage verifier profile is plain Text,
   not a nominal Haskell profile revision. This P-tagged string model
   covers a read-only data role, NOT native acceptance, Unicode Text
   serialization, an unproved nat encoding, or stage-origin evidence. *)
Record NativeVerifierProfileTextRole := mkNativeVerifierProfileTextRole {
  nativeVerifierProfileTextPayload : string
}.
Definition nativeVerifierProfileTextWire (p : NativeVerifierProfileTextRole) : string :=
  "P" ++ nativeVerifierProfileTextPayload p.
Definition nativeDecodeVerifierProfileTextWire (wire : string)
  : option NativeVerifierProfileTextRole :=
  match wire with
  | EmptyString => None
  | String role payload =>
      if Ascii.eqb role "P"%char
      then Some (mkNativeVerifierProfileTextRole payload)
      else None
  end.

Theorem native_verifier_profile_text_wire_injective :
  forall a b, nativeVerifierProfileTextWire a = nativeVerifierProfileTextWire b -> a = b.
Proof.
  intros [a] [b] H.
  unfold nativeVerifierProfileTextWire in H.
  simpl in H. injection H as Heq. now subst.
Qed.

Theorem native_verifier_profile_text_wire_roundtrip :
  forall p, nativeDecodeVerifierProfileTextWire (nativeVerifierProfileTextWire p) = Some p.
Proof. intros [p]. reflexivity. Qed.

Theorem native_verifier_profile_text_wire_disjoint_from_eight_roles :
  forall raw root sys common closed subject inst real profile,
    nativeVerifierProfileTextWire profile <> nativeRawSystemsDigestWire raw /\
    nativeVerifierProfileTextWire profile <> nativeLoweringRootWire root /\
    nativeVerifierProfileTextWire profile <> nativeSystemsRevisionWire sys /\
    nativeVerifierProfileTextWire profile <> nativeCommonRevisionWire common /\
    nativeVerifierProfileTextWire profile <> nativeClosedRevisionWire closed /\
    nativeVerifierProfileTextWire profile <> nativeSubjectRevisionWire subject /\
    nativeVerifierProfileTextWire profile <> nativeInstanceRevisionWire inst /\
    nativeVerifierProfileTextWire profile <> nativeRealizationRevisionWire real.
Proof.
  intros [raw] [root] [sys] [common] [closed] [subject] [inst] [real] [profile].
  repeat split; intro H;
    unfold nativeVerifierProfileTextWire, nativeRawSystemsDigestWire,
      nativeLoweringRootWire, nativeSystemsRevisionWire,
      nativeCommonRevisionWire, nativeClosedRevisionWire,
      nativeSubjectRevisionWire, nativeInstanceRevisionWire,
      nativeRealizationRevisionWire in H;
    simpl in H; discriminate H.
Qed.

Theorem native_verifier_profile_text_wrong_role_decoders_fail :
  forall raw root sys common closed subject inst real,
    nativeDecodeVerifierProfileTextWire (nativeRawSystemsDigestWire raw) = None /\
    nativeDecodeVerifierProfileTextWire (nativeLoweringRootWire root) = None /\
    nativeDecodeVerifierProfileTextWire (nativeSystemsRevisionWire sys) = None /\
    nativeDecodeVerifierProfileTextWire (nativeCommonRevisionWire common) = None /\
    nativeDecodeVerifierProfileTextWire (nativeClosedRevisionWire closed) = None /\
    nativeDecodeVerifierProfileTextWire (nativeSubjectRevisionWire subject) = None /\
    nativeDecodeVerifierProfileTextWire (nativeInstanceRevisionWire inst) = None /\
    nativeDecodeVerifierProfileTextWire (nativeRealizationRevisionWire real) = None.
Proof.
  intros [raw] [root] [sys] [common] [closed] [subject] [inst] [real].
  repeat split; reflexivity.
Qed.

(* #1584: the checked architecture occurrence has a native InstanceKey
   newtype separate from concrete StageClosure InstanceRevision. K is a
   reversible data role, never a StageClosure-origin certificate. Nine
   existing wire roles cannot decode as a checked occurrence key. Neither
   a Unicode Text serializer nor native-to-Rocq nat translation is assumed. *)
Record NativeOccurrenceKeyRole := mkNativeOccurrenceKeyRole {
  nativeOccurrenceKeyPayload : string
}.
Definition nativeOccurrenceKeyWire (k : NativeOccurrenceKeyRole) : string :=
  "K" ++ nativeOccurrenceKeyPayload k.
Definition nativeDecodeOccurrenceKeyWire (wire : string)
  : option NativeOccurrenceKeyRole :=
  match wire with
  | EmptyString => None
  | String role payload =>
      if Ascii.eqb role "K"%char
      then Some (mkNativeOccurrenceKeyRole payload)
      else None
  end.

Theorem native_occurrence_key_wire_injective :
  forall a b, nativeOccurrenceKeyWire a = nativeOccurrenceKeyWire b -> a = b.
Proof.
  intros [a] [b] H.
  unfold nativeOccurrenceKeyWire in H.
  simpl in H. injection H as Heq. now subst.
Qed.

Theorem native_occurrence_key_wire_roundtrip :
  forall k, nativeDecodeOccurrenceKeyWire (nativeOccurrenceKeyWire k) = Some k.
Proof. intros [k]. reflexivity. Qed.

Theorem native_occurrence_key_wire_disjoint_from_nine_roles :
  forall raw root sys common closed subject inst real profile key,
    nativeOccurrenceKeyWire key <> nativeRawSystemsDigestWire raw /\
    nativeOccurrenceKeyWire key <> nativeLoweringRootWire root /\
    nativeOccurrenceKeyWire key <> nativeSystemsRevisionWire sys /\
    nativeOccurrenceKeyWire key <> nativeCommonRevisionWire common /\
    nativeOccurrenceKeyWire key <> nativeClosedRevisionWire closed /\
    nativeOccurrenceKeyWire key <> nativeSubjectRevisionWire subject /\
    nativeOccurrenceKeyWire key <> nativeInstanceRevisionWire inst /\
    nativeOccurrenceKeyWire key <> nativeRealizationRevisionWire real /\
    nativeOccurrenceKeyWire key <> nativeVerifierProfileTextWire profile.
Proof.
  intros [raw] [root] [sys] [common] [closed] [subject] [inst] [real] [profile] [key].
  repeat split; intro H;
    unfold nativeOccurrenceKeyWire, nativeRawSystemsDigestWire,
      nativeLoweringRootWire, nativeSystemsRevisionWire,
      nativeCommonRevisionWire, nativeClosedRevisionWire,
      nativeSubjectRevisionWire, nativeInstanceRevisionWire,
      nativeRealizationRevisionWire, nativeVerifierProfileTextWire in H;
    simpl in H; discriminate H.
Qed.

Theorem native_occurrence_key_wrong_role_decoders_fail :
  forall raw root sys common closed subject inst real profile,
    nativeDecodeOccurrenceKeyWire (nativeRawSystemsDigestWire raw) = None /\
    nativeDecodeOccurrenceKeyWire (nativeLoweringRootWire root) = None /\
    nativeDecodeOccurrenceKeyWire (nativeSystemsRevisionWire sys) = None /\
    nativeDecodeOccurrenceKeyWire (nativeCommonRevisionWire common) = None /\
    nativeDecodeOccurrenceKeyWire (nativeClosedRevisionWire closed) = None /\
    nativeDecodeOccurrenceKeyWire (nativeSubjectRevisionWire subject) = None /\
    nativeDecodeOccurrenceKeyWire (nativeInstanceRevisionWire inst) = None /\
    nativeDecodeOccurrenceKeyWire (nativeRealizationRevisionWire real) = None /\
    nativeDecodeOccurrenceKeyWire (nativeVerifierProfileTextWire profile) = None.
Proof.
  intros [raw] [root] [sys] [common] [closed] [subject] [inst] [real] [profile].
  repeat split; reflexivity.
Qed.

(* #1584: complete, bounded PAIR data-model for the checked architecture
   occurrence identity. The K component is the occurrence's InstanceKey,
   while the I component is its own InstanceRevision, NOT a claim that an
   independently accepted StageClosure was produced by this occurrence.
   This does not supply a Haskell Text/Rocq string serializer or authority. *)
Record NativeCheckedOccurrenceIdentityPair := mkNativeCheckedOccurrenceIdentityPair {
  checkedOccurrencePairKey : NativeOccurrenceKeyRole;
  checkedOccurrencePairRevision : NativeInstanceRevisionRole
}.
Definition nativeCheckedOccurrenceIdentityPairWires
  (p : NativeCheckedOccurrenceIdentityPair) : string * string :=
  (nativeOccurrenceKeyWire (checkedOccurrencePairKey p),
   nativeInstanceRevisionWire (checkedOccurrencePairRevision p)).
Definition nativeDecodeCheckedOccurrenceIdentityPairWires
  (w : string * string) : option NativeCheckedOccurrenceIdentityPair :=
  match nativeDecodeOccurrenceKeyWire (fst w),
        nativeDecodeInstanceRevisionWire (snd w) with
  | Some key, Some revision =>
      Some (mkNativeCheckedOccurrenceIdentityPair key revision)
  | _, _ => None
  end.

Theorem native_checked_occurrence_identity_pair_roundtrip :
  forall p, nativeDecodeCheckedOccurrenceIdentityPairWires
              (nativeCheckedOccurrenceIdentityPairWires p) = Some p.
Proof.
  intros [[key] [revision]]. reflexivity.
Qed.

Theorem native_checked_occurrence_identity_pair_injective :
  forall a b, nativeCheckedOccurrenceIdentityPairWires a =
              nativeCheckedOccurrenceIdentityPairWires b -> a = b.
Proof.
  intros [ka ra] [kb rb] H.
  pose proof (f_equal fst H) as Hkey.
  pose proof (f_equal snd H) as Hrevision.
  simpl in Hkey, Hrevision.
  apply native_occurrence_key_wire_injective in Hkey.
  apply native_instance_revision_wire_injective in Hrevision.
  now subst.
Qed.

Theorem native_checked_occurrence_identity_pair_wrong_roles_reject :
  forall key revision,
    nativeDecodeCheckedOccurrenceIdentityPairWires
      (nativeInstanceRevisionWire revision, nativeOccurrenceKeyWire key) = None.
Proof. intros [key] [revision]. reflexivity. Qed.

Theorem native_checked_occurrence_same_revision_not_same_identity :
  forall key1 key2 revision, key1 <> key2 ->
    nativeCheckedOccurrenceIdentityPairWires
      (mkNativeCheckedOccurrenceIdentityPair key1 revision) <>
    nativeCheckedOccurrenceIdentityPairWires
      (mkNativeCheckedOccurrenceIdentityPair key2 revision).
Proof.
  intros key1 key2 revision Hdiff Heq.
  apply Hdiff.
  apply native_occurrence_key_wire_injective.
  exact (f_equal fst Heq).
Qed.


(* #1584: actual GenericApplicationIdentity has (DeclarationKey,
   InterfaceRevision, Map GenericStaticParameterKey SemanticForm).
   These D/V role-tagged string-model wires represent ONLY the first TWO
   native Text newtype components; semantic actuals are not serialized.
   They cannot establish generic application identity or native authority. *)
Record NativeGenericDeclarationRole := mkNativeGenericDeclarationRole {
  nativeGenericDeclarationPayload : string
}.
Record NativeGenericInterfaceRevisionRole := mkNativeGenericInterfaceRevisionRole {
  nativeGenericInterfaceRevisionPayload : string
}.
Definition nativeGenericDeclarationWire (d : NativeGenericDeclarationRole) : string :=
  "D" ++ nativeGenericDeclarationPayload d.
Definition nativeGenericInterfaceWire (v : NativeGenericInterfaceRevisionRole) : string :=
  "V" ++ nativeGenericInterfaceRevisionPayload v.
Definition nativeDecodeGenericDeclarationWire (w : string)
  : option NativeGenericDeclarationRole :=
  match w with
  | EmptyString => None
  | String tag payload =>
      if Ascii.eqb tag "D"%char
      then Some (mkNativeGenericDeclarationRole payload) else None
  end.
Definition nativeDecodeGenericInterfaceWire (w : string)
  : option NativeGenericInterfaceRevisionRole :=
  match w with
  | EmptyString => None
  | String tag payload =>
      if Ascii.eqb tag "V"%char
      then Some (mkNativeGenericInterfaceRevisionRole payload) else None
  end.
Record NativeGenericScalarProjection := mkNativeGenericScalarProjection {
  nativeGenericScalarDeclaration : NativeGenericDeclarationRole;
  nativeGenericScalarInterface : NativeGenericInterfaceRevisionRole
}.
Definition nativeGenericScalarWires (p : NativeGenericScalarProjection)
  : string * string :=
  (nativeGenericDeclarationWire (nativeGenericScalarDeclaration p),
   nativeGenericInterfaceWire (nativeGenericScalarInterface p)).
Definition nativeDecodeGenericScalarWires (w : string * string)
  : option NativeGenericScalarProjection :=
  match nativeDecodeGenericDeclarationWire (fst w),
        nativeDecodeGenericInterfaceWire (snd w) with
  | Some d, Some v => Some (mkNativeGenericScalarProjection d v)
  | _, _ => None
  end.
Theorem native_generic_declaration_wire_roundtrip :
  forall d, nativeDecodeGenericDeclarationWire (nativeGenericDeclarationWire d) = Some d.
Proof. intros [d]. reflexivity. Qed.
Theorem native_generic_interface_wire_roundtrip :
  forall v, nativeDecodeGenericInterfaceWire (nativeGenericInterfaceWire v) = Some v.
Proof. intros [v]. reflexivity. Qed.
Theorem native_generic_declaration_wire_injective :
  forall a b, nativeGenericDeclarationWire a = nativeGenericDeclarationWire b -> a = b.
Proof.
  intros [a] [b] H. unfold nativeGenericDeclarationWire in H.
  simpl in H. injection H as Heq. now subst.
Qed.
Theorem native_generic_interface_wire_injective :
  forall a b, nativeGenericInterfaceWire a = nativeGenericInterfaceWire b -> a = b.
Proof.
  intros [a] [b] H. unfold nativeGenericInterfaceWire in H.
  simpl in H. injection H as Heq. now subst.
Qed.
Theorem native_generic_scalar_projection_roundtrip :
  forall p, nativeDecodeGenericScalarWires (nativeGenericScalarWires p) = Some p.
Proof. intros [[d] [v]]. reflexivity. Qed.
Theorem native_generic_scalar_wrong_role_reject :
  forall key revision declaration interfaceRevision,
    nativeDecodeGenericScalarWires
      (nativeOccurrenceKeyWire key, nativeGenericInterfaceWire interfaceRevision) = None /\
    nativeDecodeGenericScalarWires
      (nativeGenericDeclarationWire declaration, nativeInstanceRevisionWire revision) = None /\
    nativeGenericDeclarationWire declaration <> nativeGenericInterfaceWire interfaceRevision.
Proof.
  intros [key] [revision] [declaration] [interfaceRevision].
  repeat split; try reflexivity.
  intro H; unfold nativeGenericDeclarationWire, nativeGenericInterfaceWire in H;
    simpl in H; discriminate H.
Qed.
(* Countermodel: even perfect reversible D/V data loses the native semantic
   actuals field. The bool is an explicitly supplied model component, NOT
   a claimed mapping of native SemanticForm or accepted proof evidence. *)
Record NativeGenericWithModelActuals := mkNativeGenericWithModelActuals {
  nativeGenericModelScalars : NativeGenericScalarProjection;
  nativeGenericModelActuals : bool
}.
Theorem native_generic_scalar_wires_cannot_identify_actuals :
  exists a b : NativeGenericWithModelActuals,
    a <> b /\
    nativeGenericScalarWires (nativeGenericModelScalars a) =
      nativeGenericScalarWires (nativeGenericModelScalars b).
Proof.
  set (p := mkNativeGenericScalarProjection
      (mkNativeGenericDeclarationRole EmptyString)
      (mkNativeGenericInterfaceRevisionRole EmptyString)).
  exists (mkNativeGenericWithModelActuals p true).
  exists (mkNativeGenericWithModelActuals p false).
  split.
  - intro H. apply (f_equal nativeGenericModelActuals) in H.
    discriminate H.
  - reflexivity.
Qed.

(* #1584 Q: checked semantic-actuals map KEY role only. This Rocq string
   model does not serialize native SemanticForm, Map ordering, or Unicode
   Data.Text. A decoded key is not an accepted generic application. *)
Record NativeGenericStaticKeyRole := mkNativeGenericStaticKeyRole {
  nativeGenericStaticKeyPayload : string
}.
Definition nativeGenericStaticKeyWire (k : NativeGenericStaticKeyRole) : string :=
  "Q" ++ nativeGenericStaticKeyPayload k.
Definition nativeDecodeGenericStaticKeyWire (w : string)
  : option NativeGenericStaticKeyRole :=
  match w with
  | EmptyString => None
  | String tag payload =>
      if Ascii.eqb tag "Q"%char
      then Some (mkNativeGenericStaticKeyRole payload) else None
  end.
Theorem native_generic_static_key_wire_roundtrip :
  forall k, nativeDecodeGenericStaticKeyWire (nativeGenericStaticKeyWire k) = Some k.
Proof. intros [k]. reflexivity. Qed.
Theorem native_generic_static_key_wire_injective :
  forall a b, nativeGenericStaticKeyWire a = nativeGenericStaticKeyWire b -> a = b.
Proof.
  intros [a] [b] H. unfold nativeGenericStaticKeyWire in H.
  simpl in H. injection H as Heq. now subst.
Qed.
Theorem native_generic_static_key_wrong_role_reject :
  forall key declaration interfaceRevision occurrence,
    nativeDecodeGenericStaticKeyWire (nativeGenericDeclarationWire declaration) = None /\
    nativeDecodeGenericStaticKeyWire (nativeGenericInterfaceWire interfaceRevision) = None /\
    nativeDecodeGenericStaticKeyWire (nativeOccurrenceKeyWire occurrence) = None /\
    nativeGenericStaticKeyWire key <> nativeGenericDeclarationWire declaration.
Proof.
  intros [key] [declaration] [interfaceRevision] [occurrence].
  repeat split; try reflexivity.
  intro H.
  unfold nativeGenericStaticKeyWire, nativeGenericDeclarationWire in H.
  simpl in H. discriminate H.
Qed.
(* A supplied bool is ONLY a countermodel value, not native SemanticForm. *)
Record NativeGenericStaticKeyWithModelValue := mkNativeGenericStaticKeyWithModelValue {
  nativeGenericStaticKeyModelKey : NativeGenericStaticKeyRole;
  nativeGenericStaticKeyModelValue : bool
}.
Theorem native_generic_static_key_wire_cannot_identify_value :
  exists a b : NativeGenericStaticKeyWithModelValue,
    a <> b /\
    nativeGenericStaticKeyWire (nativeGenericStaticKeyModelKey a) =
    nativeGenericStaticKeyWire (nativeGenericStaticKeyModelKey b).
Proof.
  set (key := mkNativeGenericStaticKeyRole EmptyString).
  exists (mkNativeGenericStaticKeyWithModelValue key true).
  exists (mkNativeGenericStaticKeyWithModelValue key false).
  split.
  - intro H. apply (f_equal nativeGenericStaticKeyModelValue) in H.
    discriminate H.
  - reflexivity.
Qed.

(* #1584 M: native SemanticForm has four distinct constructors; only
   SemanticAtom Text has a reversible M wire. This is a conditional Rocq
   string model, NOT a Data.Text Unicode correspondence or native acceptance. *)
Record NativeSemanticAtomRole := mkNativeSemanticAtomRole {
  nativeSemanticAtomPayload : string
}.
Definition nativeSemanticAtomWire (a : NativeSemanticAtomRole) : string :=
  "M" ++ nativeSemanticAtomPayload a.
Definition nativeDecodeSemanticAtomWire (w : string)
  : option NativeSemanticAtomRole :=
  match w with
  | EmptyString => None
  | String tag payload =>
      if Ascii.eqb tag "M"%char
      then Some (mkNativeSemanticAtomRole payload) else None
  end.
Theorem native_semantic_atom_wire_roundtrip :
  forall a, nativeDecodeSemanticAtomWire (nativeSemanticAtomWire a) = Some a.
Proof. intros [a]. reflexivity. Qed.
Theorem native_semantic_atom_wire_injective :
  forall a b, nativeSemanticAtomWire a = nativeSemanticAtomWire b -> a = b.
Proof.
  intros [a] [b] H. unfold nativeSemanticAtomWire in H.
  simpl in H. injection H as Heq. now subst.
Qed.
Theorem native_semantic_atom_wrong_role_reject :
  forall atom key declaration interfaceRevision,
    nativeDecodeSemanticAtomWire (nativeGenericStaticKeyWire key) = None /\
    nativeDecodeSemanticAtomWire (nativeGenericDeclarationWire declaration) = None /\
    nativeDecodeSemanticAtomWire (nativeGenericInterfaceWire interfaceRevision) = None /\
    nativeSemanticAtomWire atom <> nativeGenericStaticKeyWire key.
Proof.
  intros [atom] [key] [declaration] [interfaceRevision].
  repeat split; try reflexivity.
  intro H.
  unfold nativeSemanticAtomWire, nativeGenericStaticKeyWire in H.
  simpl in H. discriminate H.
Qed.
(* Constructor distinctions are explicitly SUPPLIED model data. This
   model never claims to encode native SemanticOrdered/Unordered/Record. *)
Inductive NativeSemanticConstructorModel : Type :=
  | NativeModelSemanticAtom (payload : NativeSemanticAtomRole)
  | NativeModelSemanticOrdered
  | NativeModelSemanticUnordered
  | NativeModelSemanticRecord.
Definition nativeModelEncodeSemanticAtom (form : NativeSemanticConstructorModel)
  : option string :=
  match form with
  | NativeModelSemanticAtom a => Some (nativeSemanticAtomWire a)
  | _ => None
  end.
Theorem native_semantic_atom_model_nonatoms_fail_closed :
  nativeModelEncodeSemanticAtom NativeModelSemanticOrdered = None /\
  nativeModelEncodeSemanticAtom NativeModelSemanticUnordered = None /\
  nativeModelEncodeSemanticAtom NativeModelSemanticRecord = None.
Proof. repeat split; reflexivity. Qed.

(* #1584 successor: partial *ordered atom-only* native SemanticOrdered
   projection. This uses a typed vector of M-role strings, not a flattened
   Text wire, cross-runtime list codec, nat serializer or accepted authority. *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Fixpoint nativeEncodeOrderedAtomListModel
  (atoms : list NativeSemanticAtomRole) : list string :=
  match atoms with
  | [] => []
  | atom :: rest =>
      nativeSemanticAtomWire atom :: nativeEncodeOrderedAtomListModel rest
  end.
Fixpoint nativeDecodeOrderedAtomListModel
  (wires : list string) : option (list NativeSemanticAtomRole) :=
  match wires with
  | [] => Some []
  | wire :: rest =>
      match nativeDecodeSemanticAtomWire wire,
            nativeDecodeOrderedAtomListModel rest with
      | Some atom, Some atoms => Some (atom :: atoms)
      | _, _ => None
      end
  end.
Theorem native_ordered_atom_list_model_roundtrip :
  forall atoms,
    nativeDecodeOrderedAtomListModel
      (nativeEncodeOrderedAtomListModel atoms) = Some atoms.
Proof.
  induction atoms as [|atom rest IH].
  - reflexivity.
  - destruct atom as [payload]. simpl.
    rewrite IH. reflexivity.
Qed.
Theorem native_ordered_atom_list_model_injective :
  forall left right,
    nativeEncodeOrderedAtomListModel left =
      nativeEncodeOrderedAtomListModel right -> left = right.
Proof.
  induction left as [|atom rest IH]; intros right H.
  - destruct right; simpl in H; try discriminate. reflexivity.
  - destruct right as [|other others]; simpl in H; try discriminate.
    injection H as Hhead Htail.
    f_equal.
    + destruct atom as [leftPayload], other as [rightPayload].
      simpl in Hhead. subst. reflexivity.
    + apply IH. exact Htail.
Qed.
Theorem native_ordered_atom_list_model_foreign_key_rejected :
  forall prefix suffix key,
    nativeDecodeOrderedAtomListModel
      (nativeEncodeOrderedAtomListModel prefix ++
       nativeGenericStaticKeyWire key ::
       nativeEncodeOrderedAtomListModel suffix) = None.
Proof.
  intros prefix.
  induction prefix as [|atom rest IH]; intros suffix key.
  - simpl. destruct key as [value]. reflexivity.
  - destruct atom as [payload]. simpl.
    rewrite IH. reflexivity.
Qed.
Theorem native_ordered_atom_list_model_order_sensitive :
  forall a b, a <> b ->
    nativeEncodeOrderedAtomListModel [a; b] <>
      nativeEncodeOrderedAtomListModel [b; a].
Proof.
  intros a b Hdifferent Heq.
  apply native_ordered_atom_list_model_injective in Heq.
  injection Heq as Hfirst _.
  apply Hdifferent. exact Hfirst.
Qed.

(* #1584 successor: Q/M atom-only semantic-actuals association as a typed
   Rocq string-list MODEL, not a native Data.Text/Map codec or authority. *)
Definition nativeEncodeGenericAtomActualPairModel
  (entry : NativeGenericStaticKeyRole * NativeSemanticAtomRole)
  : string * string :=
  (nativeGenericStaticKeyWire (fst entry),
   nativeSemanticAtomWire (snd entry)).
Definition nativeDecodeGenericAtomActualPairModel
  (wires : string * string)
  : option (NativeGenericStaticKeyRole * NativeSemanticAtomRole) :=
  match nativeDecodeGenericStaticKeyWire (fst wires),
        nativeDecodeSemanticAtomWire (snd wires) with
  | Some key, Some atom => Some (key, atom)
  | _, _ => None
  end.
Fixpoint nativeEncodeGenericAtomActualPairsModel
  (entries : list (NativeGenericStaticKeyRole * NativeSemanticAtomRole))
  : list (string * string) :=
  match entries with
  | [] => []
  | entry :: rest =>
      nativeEncodeGenericAtomActualPairModel entry ::
      nativeEncodeGenericAtomActualPairsModel rest
  end.
Fixpoint nativeDecodeGenericAtomActualPairsModel
  (wires : list (string * string))
  : option (list (NativeGenericStaticKeyRole * NativeSemanticAtomRole)) :=
  match wires with
  | [] => Some []
  | wirePair :: rest =>
      match nativeDecodeGenericAtomActualPairModel wirePair,
            nativeDecodeGenericAtomActualPairsModel rest with
      | Some entry, Some entries => Some (entry :: entries)
      | _, _ => None
      end
  end.
Theorem native_generic_atom_actual_pairs_model_roundtrip :
  forall entries,
    nativeDecodeGenericAtomActualPairsModel
      (nativeEncodeGenericAtomActualPairsModel entries) = Some entries.
Proof.
  induction entries as [|[key atom] rest IH].
  - reflexivity.
  - destruct key as [keyText], atom as [atomText].
    simpl. rewrite IH. reflexivity.
Qed.
Theorem native_generic_atom_actual_pairs_model_injective :
  forall left right,
    nativeEncodeGenericAtomActualPairsModel left =
    nativeEncodeGenericAtomActualPairsModel right -> left = right.
Proof.
  intros left right H.
  apply (f_equal nativeDecodeGenericAtomActualPairsModel) in H.
  rewrite !native_generic_atom_actual_pairs_model_roundtrip in H.
  injection H as Heq. exact Heq.
Qed.
Theorem native_generic_atom_actual_pair_model_swapped_roles_reject :
  forall key atom,
    nativeDecodeGenericAtomActualPairModel
      (nativeSemanticAtomWire atom, nativeGenericStaticKeyWire key) = None /\
    nativeDecodeGenericAtomActualPairModel
      (nativeGenericStaticKeyWire key, nativeGenericStaticKeyWire key) = None.
Proof. intros [key] [atom]; split; reflexivity. Qed.
Theorem native_generic_atom_actual_pair_model_association_sensitive :
  forall key first second, first <> second ->
    nativeEncodeGenericAtomActualPairModel (key, first) <>
    nativeEncodeGenericAtomActualPairModel (key, second).
Proof.
  intros key first second Hneq Heq.
  apply Hneq.
  apply native_semantic_atom_wire_injective.
  exact (f_equal snd Heq).
Qed.

(* #1584 native SemanticUnordered atom-only *candidate* string-list MODEL.
   NoDup is an externally supplied canonicality condition: no theorem here
   derives the native Set Ord comparator or Data.Text/Rocq string transport. *)
Definition nativeUnorderedAtomCandidateEncodeModel
  (atoms : list NativeSemanticAtomRole) : list string :=
  nativeEncodeOrderedAtomListModel atoms.
Definition nativeUnorderedAtomCandidateDecodeModel
  (wires : list string) : option (list NativeSemanticAtomRole) :=
  nativeDecodeOrderedAtomListModel wires.
Definition nativeUnorderedAtomCanonicalPremiseModel
  (atoms : list NativeSemanticAtomRole) : Prop := NoDup atoms.
Theorem native_unordered_atom_candidate_model_roundtrip :
  forall atoms, nativeUnorderedAtomCanonicalPremiseModel atoms ->
    nativeUnorderedAtomCandidateDecodeModel
      (nativeUnorderedAtomCandidateEncodeModel atoms) = Some atoms.
Proof.
  intros atoms _. apply native_ordered_atom_list_model_roundtrip.
Qed.
Theorem native_unordered_atom_candidate_model_injective :
  forall left right,
    nativeUnorderedAtomCandidateEncodeModel left =
    nativeUnorderedAtomCandidateEncodeModel right -> left = right.
Proof.
  intros left right H.
  exact (native_ordered_atom_list_model_injective left right H).
Qed.
Theorem native_unordered_atom_candidate_model_foreign_key_rejected :
  forall prefix suffix key,
    nativeUnorderedAtomCandidateDecodeModel
      (nativeUnorderedAtomCandidateEncodeModel prefix ++
       nativeGenericStaticKeyWire key ::
       nativeUnorderedAtomCandidateEncodeModel suffix) = None.
Proof.
  intros prefix suffix key.
  apply native_ordered_atom_list_model_foreign_key_rejected.
Qed.
Theorem native_unordered_atom_repeated_member_not_canonical_model :
  forall atom rest,
    ~ nativeUnorderedAtomCanonicalPremiseModel (atom :: atom :: rest).
Proof.
  intros atom rest H.
  apply NoDup_cons_iff in H.
  destruct H as [Hnot _].
  apply Hnot. left. reflexivity.
Qed.


(* #1584 bounded native SemanticRecord (Map Text SemanticForm) partial
   ATOM-ONLY field projection. H is a distinct record FIELD NAME role,
   not raw Systems R, architecture K/I or generic Q/M. Rocq lists here
   are candidate strings; Map Ord and Data.Text Unicode remain external. *)
Record NativeSemanticRecordFieldRole := mkNativeSemanticRecordFieldRole {
  nativeSemanticRecordFieldPayload : string
}.
Definition nativeSemanticRecordFieldWire
  (field : NativeSemanticRecordFieldRole) : string :=
  "H" ++ nativeSemanticRecordFieldPayload field.
Definition nativeDecodeSemanticRecordFieldWire
  (wire : string) : option NativeSemanticRecordFieldRole :=
  match wire with
  | EmptyString => None
  | String tag payload =>
      if Ascii.eqb tag "H"%char
      then Some (mkNativeSemanticRecordFieldRole payload) else None
  end.
Definition nativeEncodeRecordAtomPairModel
  (entry : NativeSemanticRecordFieldRole * NativeSemanticAtomRole)
  : string * string :=
  (nativeSemanticRecordFieldWire (fst entry),
   nativeSemanticAtomWire (snd entry)).
Definition nativeDecodeRecordAtomPairModel
  (entry : string * string)
  : option (NativeSemanticRecordFieldRole * NativeSemanticAtomRole) :=
  match nativeDecodeSemanticRecordFieldWire (fst entry),
        nativeDecodeSemanticAtomWire (snd entry) with
  | Some field, Some atom => Some (field, atom)
  | _, _ => None
  end.
Fixpoint nativeEncodeRecordAtomEntriesModel
  (entries : list (NativeSemanticRecordFieldRole * NativeSemanticAtomRole))
  : list (string * string) :=
  match entries with
  | [] => []
  | entry :: rest =>
      nativeEncodeRecordAtomPairModel entry
        :: nativeEncodeRecordAtomEntriesModel rest
  end.
Fixpoint nativeDecodeRecordAtomEntriesModel
  (entries : list (string * string))
  : option (list (NativeSemanticRecordFieldRole * NativeSemanticAtomRole)) :=
  match entries with
  | [] => Some []
  | entry :: rest =>
      match nativeDecodeRecordAtomPairModel entry,
            nativeDecodeRecordAtomEntriesModel rest with
      | Some decoded, Some decodedRest => Some (decoded :: decodedRest)
      | _, _ => None
      end
  end.
Definition nativeRecordAtomUniqueFieldsPremiseModel
  (entries : list (NativeSemanticRecordFieldRole * NativeSemanticAtomRole))
  : Prop := NoDup (map fst entries).
Theorem native_record_atom_entries_model_roundtrip :
  forall entries,
    nativeDecodeRecordAtomEntriesModel
      (nativeEncodeRecordAtomEntriesModel entries) = Some entries.
Proof.
  induction entries as [|[field atom] rest IH].
  - reflexivity.
  - destruct field as [fieldText], atom as [atomText].
    simpl. rewrite IH. reflexivity.
Qed.
Theorem native_record_atom_entries_model_injective :
  forall left right,
    nativeEncodeRecordAtomEntriesModel left =
    nativeEncodeRecordAtomEntriesModel right -> left = right.
Proof.
  intros left right H.
  apply (f_equal nativeDecodeRecordAtomEntriesModel) in H.
  rewrite !native_record_atom_entries_model_roundtrip in H.
  now injection H.
Qed.
Theorem native_record_atom_pair_model_wrong_role_reject :
  forall field atom key,
    nativeDecodeRecordAtomPairModel
      (nativeSemanticAtomWire atom, nativeSemanticRecordFieldWire field)
        = None /\
    nativeDecodeRecordAtomPairModel
      (nativeGenericStaticKeyWire key, nativeSemanticAtomWire atom)
        = None.
Proof. intros [field] [atom] [key]; split; reflexivity. Qed.
Theorem native_record_atom_pair_model_association_sensitive :
  forall field first second, first <> second ->
    nativeEncodeRecordAtomPairModel (field, first) <>
    nativeEncodeRecordAtomPairModel (field, second).
Proof.
  intros field first second Hneq Heq.
  apply Hneq.
  apply native_semantic_atom_wire_injective.
  exact (f_equal snd Heq).
Qed.
Theorem native_record_atom_duplicate_field_not_canonical_model :
  forall field left right rest,
    ~ nativeRecordAtomUniqueFieldsPremiseModel
        ((field, left) :: (field, right) :: rest).
Proof.
  intros field left right rest H.
  unfold nativeRecordAtomUniqueFieldsPremiseModel in H.
  simpl in H.
  apply NoDup_cons_iff in H.
  destruct H as [Hnot _].
  apply Hnot. left. reflexivity.
Qed.

(* #1584 composed bounded D/V/Q/M DATA model: the actual native checked
   GenericApplicationIdentity has D declaration, V interface and a Q/M
   Map GenericStaticParameterKey SemanticForm. The model is valid only for
   atom-valued actuals and externally supplied canonical candidate pairs;
   there is NO Data.Text to Rocq string or Map Ord transport theorem. *)
Record NativeGenericAtomApplicationModel := mkNativeGenericAtomApplicationModel {
  nativeGenericAtomApplicationScalars : NativeGenericScalarProjection;
  nativeGenericAtomApplicationPairs :
    list (NativeGenericStaticKeyRole * NativeSemanticAtomRole)
}.
Definition nativeEncodeGenericAtomApplicationModel
  (application : NativeGenericAtomApplicationModel)
  : (string * string) * list (string * string) :=
  ( nativeGenericScalarWires (nativeGenericAtomApplicationScalars application),
    nativeEncodeGenericAtomActualPairsModel
      (nativeGenericAtomApplicationPairs application) ).
Definition nativeDecodeGenericAtomApplicationModel
  (wires : (string * string) * list (string * string))
  : option NativeGenericAtomApplicationModel :=
  match nativeDecodeGenericScalarWires (fst wires),
        nativeDecodeGenericAtomActualPairsModel (snd wires) with
  | Some scalars, Some pairs =>
      Some (mkNativeGenericAtomApplicationModel scalars pairs)
  | _, _ => None
  end.
Theorem native_generic_atom_application_model_roundtrip :
  forall application,
    nativeDecodeGenericAtomApplicationModel
      (nativeEncodeGenericAtomApplicationModel application) = Some application.
Proof.
  intros [scalars entries]. destruct scalars as [[d] [v]].
  unfold nativeEncodeGenericAtomApplicationModel,
    nativeDecodeGenericAtomApplicationModel. simpl.
  rewrite native_generic_atom_actual_pairs_model_roundtrip. reflexivity.
Qed.
Theorem native_generic_atom_application_model_injective :
  forall first second,
    nativeEncodeGenericAtomApplicationModel first =
      nativeEncodeGenericAtomApplicationModel second -> first = second.
Proof.
  intros first second H.
  apply (f_equal nativeDecodeGenericAtomApplicationModel) in H.
  rewrite !native_generic_atom_application_model_roundtrip in H.
  now injection H.
Qed.
Theorem native_generic_atom_application_model_swapped_scalar_roles_reject :
  forall scalars entries,
    nativeDecodeGenericAtomApplicationModel
      ((nativeGenericInterfaceWire (nativeGenericScalarInterface scalars),
        nativeGenericDeclarationWire (nativeGenericScalarDeclaration scalars)),
       nativeEncodeGenericAtomActualPairsModel entries) = None.
Proof. intros [[d] [v]] entries. reflexivity. Qed.
Theorem native_generic_atom_application_model_actuals_sensitive :
  forall scalars first second, first <> second ->
    nativeEncodeGenericAtomApplicationModel
      (mkNativeGenericAtomApplicationModel scalars first) <>
    nativeEncodeGenericAtomApplicationModel
      (mkNativeGenericAtomApplicationModel scalars second).
Proof.
  intros scalars first second Hneq Heq.
  apply Hneq.
  apply native_generic_atom_actual_pairs_model_injective.
  exact (f_equal snd Heq).
Qed.

(* Issue #1584: data-only composition of the actual atom-only generic
   D/V/Q/M shape with the INDEPENDENT manifest R raw Systems digest and
   L lowering-ledger root domains. This model does not project accepted
   Haskell objects or prove a Text -> Rocq string serializer; native accepted
   producer/consumer replay is a separate executable Haskell gate. *)
Record NativeAtomApplicationManifestDataModel :=
  mkNativeAtomApplicationManifestDataModel {
    nativeAtomManifestApplicationData : NativeGenericAtomApplicationModel;
    nativeAtomManifestRawData : NativeRawSystemsDigestRole;
    nativeAtomManifestLoweringData : NativeLoweringRootDigestRole
  }.

Definition nativeEncodeAtomApplicationManifestDataModel
  (data : NativeAtomApplicationManifestDataModel)
  : ((string * string) * list (string * string)) * (string * string) :=
  (nativeEncodeGenericAtomApplicationModel
     (nativeAtomManifestApplicationData data),
   (nativeRawSystemsDigestWire (nativeAtomManifestRawData data),
    nativeLoweringRootWire (nativeAtomManifestLoweringData data))).

Definition nativeDecodeAtomApplicationManifestDataModel
  (wires : ((string * string) * list (string * string)) * (string * string))
  : option NativeAtomApplicationManifestDataModel :=
  match nativeDecodeGenericAtomApplicationModel (fst wires),
        nativeDecodeRawSystemsDigestWire (fst (snd wires)),
        nativeDecodeLoweringRootWire (snd (snd wires)) with
  | Some app, Some raw, Some root =>
      Some (mkNativeAtomApplicationManifestDataModel app raw root)
  | _, _, _ => None
  end.

Theorem native_atom_manifest_data_model_roundtrip :
  forall data,
    nativeDecodeAtomApplicationManifestDataModel
      (nativeEncodeAtomApplicationManifestDataModel data) = Some data.
Proof.
  intros [app raw root].
  unfold nativeDecodeAtomApplicationManifestDataModel,
    nativeEncodeAtomApplicationManifestDataModel.
  simpl (fst (_, _)). simpl (snd (_, _)).
  rewrite native_generic_atom_application_model_roundtrip.
  (* The R/L wire decoders have already reduced under simpl. Expose the
     remaining record projections; the distinct roles then compute exactly. *)
  destruct raw as [rawPayload].
  destruct root as [rootPayload].
  reflexivity.
Qed.

Theorem native_atom_manifest_data_model_injective :
  forall first second,
    nativeEncodeAtomApplicationManifestDataModel first =
      nativeEncodeAtomApplicationManifestDataModel second -> first = second.
Proof.
  intros first second H.
  apply (f_equal nativeDecodeAtomApplicationManifestDataModel) in H.
  rewrite !native_atom_manifest_data_model_roundtrip in H.
  now injection H.
Qed.

Theorem native_atom_manifest_data_model_swapped_digest_roles_reject :
  forall app raw root,
    nativeDecodeAtomApplicationManifestDataModel
      (nativeEncodeGenericAtomApplicationModel app,
       (nativeLoweringRootWire root, nativeRawSystemsDigestWire raw)) = None.
Proof.
  intros app [raw] [root].
  unfold nativeDecodeAtomApplicationManifestDataModel.
  simpl.
  destruct (nativeDecodeGenericAtomApplicationModel
    (nativeEncodeGenericAtomApplicationModel app)); reflexivity.
Qed.

Theorem native_atom_manifest_data_model_application_sensitive :
  forall first second raw root, first <> second ->
    nativeEncodeAtomApplicationManifestDataModel
      (mkNativeAtomApplicationManifestDataModel first raw root) <>
    nativeEncodeAtomApplicationManifestDataModel
      (mkNativeAtomApplicationManifestDataModel second raw root).
Proof.
  intros first second raw root Hneq Heq.
  apply Hneq.
  apply native_generic_atom_application_model_injective.
  exact (f_equal fst Heq).
Qed.

(* Conditional string model only. No native Text, map order, accepted
   authority or architecture-occurrence -> concrete StageClosure theorem. *)
Record NativeAtomManifestSystemsDataModel :=
  mkNativeAtomManifestSystemsDataModel {
    nativeAtomManifestSystemsBaseData : NativeAtomApplicationManifestDataModel;
    nativeAtomManifestSystemsRevisionData : NativeSystemsRevisionRole
  }.

Definition nativeEncodeAtomManifestSystemsDataModel
  (data : NativeAtomManifestSystemsDataModel)
  : (((string * string) * list (string * string)) * (string * string)) * string :=
  (nativeEncodeAtomApplicationManifestDataModel
     (nativeAtomManifestSystemsBaseData data),
   nativeSystemsRevisionWire (nativeAtomManifestSystemsRevisionData data)).

Definition nativeDecodeAtomManifestSystemsDataModel
  (wires : (((string * string) * list (string * string)) * (string * string)) * string)
  : option NativeAtomManifestSystemsDataModel :=
  match nativeDecodeAtomApplicationManifestDataModel (fst wires),
        nativeDecodeSystemsRevisionWire (snd wires) with
  | Some previous, Some revision =>
      Some (mkNativeAtomManifestSystemsDataModel previous revision)
  | _, _ => None
  end.

Theorem native_atom_manifest_systems_data_model_roundtrip :
  forall data,
    nativeDecodeAtomManifestSystemsDataModel
      (nativeEncodeAtomManifestSystemsDataModel data) = Some data.
Proof.
  intros [previous [revision]].
  unfold nativeDecodeAtomManifestSystemsDataModel,
    nativeEncodeAtomManifestSystemsDataModel.
  simpl (fst (_, _)). simpl (snd (_, _)).
  rewrite native_atom_manifest_data_model_roundtrip.
  reflexivity.
Qed.

Theorem native_atom_manifest_systems_data_model_injective :
  forall first second,
    nativeEncodeAtomManifestSystemsDataModel first =
      nativeEncodeAtomManifestSystemsDataModel second -> first = second.
Proof.
  intros first second H.
  apply (f_equal nativeDecodeAtomManifestSystemsDataModel) in H.
  rewrite !native_atom_manifest_systems_data_model_roundtrip in H.
  now injection H.
Qed.

Theorem native_atom_manifest_systems_data_model_wrong_role_reject :
  forall previous raw root common closed,
    nativeDecodeAtomManifestSystemsDataModel
      (nativeEncodeAtomApplicationManifestDataModel previous,
       nativeRawSystemsDigestWire raw) = None /\
    nativeDecodeAtomManifestSystemsDataModel
      (nativeEncodeAtomApplicationManifestDataModel previous,
       nativeLoweringRootWire root) = None /\
    nativeDecodeAtomManifestSystemsDataModel
      (nativeEncodeAtomApplicationManifestDataModel previous,
       nativeCommonRevisionWire common) = None /\
    nativeDecodeAtomManifestSystemsDataModel
      (nativeEncodeAtomApplicationManifestDataModel previous,
       nativeClosedRevisionWire closed) = None.
Proof.
  intros previous [raw] [root] [common] [closed].
  repeat split;
    unfold nativeDecodeAtomManifestSystemsDataModel;
    simpl;
    destruct (nativeDecodeAtomApplicationManifestDataModel
      (nativeEncodeAtomApplicationManifestDataModel previous)); reflexivity.
Qed.

Theorem native_atom_manifest_systems_data_model_revision_sensitive :
  forall previous first second, first <> second ->
    nativeEncodeAtomManifestSystemsDataModel
      (mkNativeAtomManifestSystemsDataModel previous first) <>
    nativeEncodeAtomManifestSystemsDataModel
      (mkNativeAtomManifestSystemsDataModel previous second).
Proof.
  intros previous first second Hneq Heq.
  apply Hneq.
  apply native_systems_revision_wire_injective.
  exact (f_equal snd Heq).
Qed.


(* #1584: conditional STRING model of native common contract C after the
   typed S/R/L diagnostic. This constructs NO Haskell Text/Rocq string
   serializer, authenticated StageClosure origin or accepted authority. *)
Record NativeAtomManifestCommonDataModel :=
  mkNativeAtomManifestCommonDataModel {
    nativeAtomManifestCommonBaseData : NativeAtomManifestSystemsDataModel;
    nativeAtomManifestCommonRevisionData : NativeCommonRevisionRole
  }.

Definition nativeEncodeAtomManifestCommonDataModel
  (data : NativeAtomManifestCommonDataModel)
  : ((((string * string) * list (string * string)) * (string * string)) * string) * string :=
  (nativeEncodeAtomManifestSystemsDataModel
    (nativeAtomManifestCommonBaseData data),
   nativeCommonRevisionWire (nativeAtomManifestCommonRevisionData data)).

Definition nativeDecodeAtomManifestCommonDataModel
  (wires : ((((string * string) * list (string * string)) * (string * string)) * string) * string)
  : option NativeAtomManifestCommonDataModel :=
  match nativeDecodeAtomManifestSystemsDataModel (fst wires),
        nativeDecodeCommonRevisionWire (snd wires) with
  | Some baseData, Some revision =>
      Some (mkNativeAtomManifestCommonDataModel baseData revision)
  | _, _ => None
  end.

Theorem native_atom_manifest_common_data_model_roundtrip :
  forall data,
    nativeDecodeAtomManifestCommonDataModel
      (nativeEncodeAtomManifestCommonDataModel data) = Some data.
Proof.
  intros [previous [revision]].
  unfold nativeDecodeAtomManifestCommonDataModel,
    nativeEncodeAtomManifestCommonDataModel.
  simpl (fst (_, _)). simpl (snd (_, _)).
  rewrite native_atom_manifest_systems_data_model_roundtrip.
  reflexivity.
Qed.

Theorem native_atom_manifest_common_data_model_injective :
  forall first second,
    nativeEncodeAtomManifestCommonDataModel first =
      nativeEncodeAtomManifestCommonDataModel second -> first = second.
Proof.
  intros first second H.
  apply (f_equal nativeDecodeAtomManifestCommonDataModel) in H.
  rewrite !native_atom_manifest_common_data_model_roundtrip in H.
  now injection H.
Qed.

Theorem native_atom_manifest_common_data_model_wrong_role_reject :
  forall previous raw root systems closed,
    nativeDecodeAtomManifestCommonDataModel
      (nativeEncodeAtomManifestSystemsDataModel previous,
       nativeRawSystemsDigestWire raw) = None /\
    nativeDecodeAtomManifestCommonDataModel
      (nativeEncodeAtomManifestSystemsDataModel previous,
       nativeLoweringRootWire root) = None /\
    nativeDecodeAtomManifestCommonDataModel
      (nativeEncodeAtomManifestSystemsDataModel previous,
       nativeSystemsRevisionWire systems) = None /\
    nativeDecodeAtomManifestCommonDataModel
      (nativeEncodeAtomManifestSystemsDataModel previous,
       nativeClosedRevisionWire closed) = None.
Proof.
  intros previous [raw] [root] [systems] [closed].
  repeat split;
    unfold nativeDecodeAtomManifestCommonDataModel;
    simpl;
    destruct (nativeDecodeAtomManifestSystemsDataModel
      (nativeEncodeAtomManifestSystemsDataModel previous)); reflexivity.
Qed.

Theorem native_atom_manifest_common_data_model_revision_sensitive :
  forall previous first second, first <> second ->
    nativeEncodeAtomManifestCommonDataModel
      (mkNativeAtomManifestCommonDataModel previous first) <>
    nativeEncodeAtomManifestCommonDataModel
      (mkNativeAtomManifestCommonDataModel previous second).
Proof.
  intros previous first second Hneq Heq.
  apply Hneq.
  apply native_common_revision_wire_injective.
  exact (f_equal snd Heq).
Qed.

(* #1584: conditional STRING model of closed revision F atop disjoint
   C/S/R/L native diagnostic roles. This is not accepted authority. *)
Record NativeAtomManifestClosedDataModel :=
  mkNativeAtomManifestClosedDataModel {
    nativeAtomManifestClosedBaseData : NativeAtomManifestCommonDataModel;
    nativeAtomManifestClosedRevisionData : NativeClosedRevisionRole
  }.

Definition nativeEncodeAtomManifestClosedDataModel
  (data : NativeAtomManifestClosedDataModel)
  : (((((string * string) * list (string * string)) * (string * string)) * string) * string) * string :=
  (nativeEncodeAtomManifestCommonDataModel
    (nativeAtomManifestClosedBaseData data),
   nativeClosedRevisionWire (nativeAtomManifestClosedRevisionData data)).

Definition nativeDecodeAtomManifestClosedDataModel
  (wires : (((((string * string) * list (string * string)) * (string * string)) * string) * string) * string)
  : option NativeAtomManifestClosedDataModel :=
  match nativeDecodeAtomManifestCommonDataModel (fst wires),
        nativeDecodeClosedRevisionWire (snd wires) with
  | Some baseData, Some revision =>
      Some (mkNativeAtomManifestClosedDataModel baseData revision)
  | _, _ => None
  end.

Theorem native_atom_manifest_closed_data_model_roundtrip :
  forall data,
    nativeDecodeAtomManifestClosedDataModel
      (nativeEncodeAtomManifestClosedDataModel data) = Some data.
Proof.
  intros [previous [revision]].
  unfold nativeDecodeAtomManifestClosedDataModel,
    nativeEncodeAtomManifestClosedDataModel.
  simpl (fst (_, _)). simpl (snd (_, _)).
  rewrite native_atom_manifest_common_data_model_roundtrip.
  reflexivity.
Qed.

Theorem native_atom_manifest_closed_data_model_injective :
  forall first second,
    nativeEncodeAtomManifestClosedDataModel first =
      nativeEncodeAtomManifestClosedDataModel second -> first = second.
Proof.
  intros first second H.
  apply (f_equal nativeDecodeAtomManifestClosedDataModel) in H.
  rewrite !native_atom_manifest_closed_data_model_roundtrip in H.
  now injection H.
Qed.

Theorem native_atom_manifest_closed_data_model_wrong_role_reject :
  forall previous raw root systems common,
    nativeDecodeAtomManifestClosedDataModel
      (nativeEncodeAtomManifestCommonDataModel previous,
       nativeRawSystemsDigestWire raw) = None /\
    nativeDecodeAtomManifestClosedDataModel
      (nativeEncodeAtomManifestCommonDataModel previous,
       nativeLoweringRootWire root) = None /\
    nativeDecodeAtomManifestClosedDataModel
      (nativeEncodeAtomManifestCommonDataModel previous,
       nativeSystemsRevisionWire systems) = None /\
    nativeDecodeAtomManifestClosedDataModel
      (nativeEncodeAtomManifestCommonDataModel previous,
       nativeCommonRevisionWire common) = None.
Proof.
  intros previous [raw] [root] [systems] [common].
  repeat split;
    unfold nativeDecodeAtomManifestClosedDataModel;
    simpl;
    destruct (nativeDecodeAtomManifestCommonDataModel
      (nativeEncodeAtomManifestCommonDataModel previous)); reflexivity.
Qed.

Theorem native_atom_manifest_closed_data_model_revision_sensitive :
  forall previous first second, first <> second ->
    nativeEncodeAtomManifestClosedDataModel
      (mkNativeAtomManifestClosedDataModel previous first) <>
    nativeEncodeAtomManifestClosedDataModel
      (mkNativeAtomManifestClosedDataModel previous second).
Proof.
  intros previous first second Hneq Heq.
  apply Hneq.
  apply native_closed_revision_wire_injective.
  exact (f_equal snd Heq).
Qed.

(* #1584: conditional STRING model of concrete subject B after exact
   accepted D/V/Q/M/R/L/S/C/F native diagnostic data. This is NOT a proof
   of Data.Text Unicode transport or StageClosure origin/acceptance. *)
Record NativeAtomManifestSubjectDataModel :=
  mkNativeAtomManifestSubjectDataModel {
    nativeAtomManifestSubjectBaseData : NativeAtomManifestClosedDataModel;
    nativeAtomManifestSubjectRevisionData : NativeSubjectRevisionRole
  }.

Definition nativeEncodeAtomManifestSubjectDataModel
  (data : NativeAtomManifestSubjectDataModel)
  : ((((((string * string) * list (string * string)) * (string * string)) * string) * string) * string) * string :=
  (nativeEncodeAtomManifestClosedDataModel
    (nativeAtomManifestSubjectBaseData data),
   nativeSubjectRevisionWire (nativeAtomManifestSubjectRevisionData data)).

Definition nativeDecodeAtomManifestSubjectDataModel
  (wires : ((((((string * string) * list (string * string)) * (string * string)) * string) * string) * string) * string)
  : option NativeAtomManifestSubjectDataModel :=
  match nativeDecodeAtomManifestClosedDataModel (fst wires),
        nativeDecodeSubjectRevisionWire (snd wires) with
  | Some previous, Some subject =>
      Some (mkNativeAtomManifestSubjectDataModel previous subject)
  | _, _ => None
  end.

Theorem native_atom_manifest_subject_data_model_roundtrip :
  forall data,
    nativeDecodeAtomManifestSubjectDataModel
      (nativeEncodeAtomManifestSubjectDataModel data) = Some data.
Proof.
  intros [previous [subject]].
  unfold nativeDecodeAtomManifestSubjectDataModel,
    nativeEncodeAtomManifestSubjectDataModel.
  simpl (fst (_, _)). simpl (snd (_, _)).
  rewrite native_atom_manifest_closed_data_model_roundtrip.
  reflexivity.
Qed.

Theorem native_atom_manifest_subject_data_model_injective :
  forall first second,
    nativeEncodeAtomManifestSubjectDataModel first =
      nativeEncodeAtomManifestSubjectDataModel second -> first = second.
Proof.
  intros first second H.
  apply (f_equal nativeDecodeAtomManifestSubjectDataModel) in H.
  rewrite !native_atom_manifest_subject_data_model_roundtrip in H.
  now injection H.
Qed.

Theorem native_atom_manifest_subject_data_model_wrong_role_reject :
  forall previous raw root systems common closed instance realization profile occurrence,
    nativeDecodeAtomManifestSubjectDataModel
      (nativeEncodeAtomManifestClosedDataModel previous,
       nativeRawSystemsDigestWire raw) = None /\
    nativeDecodeAtomManifestSubjectDataModel
      (nativeEncodeAtomManifestClosedDataModel previous,
       nativeLoweringRootWire root) = None /\
    nativeDecodeAtomManifestSubjectDataModel
      (nativeEncodeAtomManifestClosedDataModel previous,
       nativeSystemsRevisionWire systems) = None /\
    nativeDecodeAtomManifestSubjectDataModel
      (nativeEncodeAtomManifestClosedDataModel previous,
       nativeCommonRevisionWire common) = None /\
    nativeDecodeAtomManifestSubjectDataModel
      (nativeEncodeAtomManifestClosedDataModel previous,
       nativeClosedRevisionWire closed) = None /\
    nativeDecodeAtomManifestSubjectDataModel
      (nativeEncodeAtomManifestClosedDataModel previous,
       nativeInstanceRevisionWire instance) = None /\
    nativeDecodeAtomManifestSubjectDataModel
      (nativeEncodeAtomManifestClosedDataModel previous,
       nativeRealizationRevisionWire realization) = None /\
    nativeDecodeAtomManifestSubjectDataModel
      (nativeEncodeAtomManifestClosedDataModel previous,
       nativeVerifierProfileTextWire profile) = None /\
    nativeDecodeAtomManifestSubjectDataModel
      (nativeEncodeAtomManifestClosedDataModel previous,
       nativeOccurrenceKeyWire occurrence) = None.
Proof.
  intros previous [raw] [root] [systems] [common] [closed]
    [instance] [realization] [profile] [occurrence].
  repeat split;
    unfold nativeDecodeAtomManifestSubjectDataModel;
    simpl;
    destruct (nativeDecodeAtomManifestClosedDataModel
      (nativeEncodeAtomManifestClosedDataModel previous)); reflexivity.
Qed.

Theorem native_atom_manifest_subject_data_model_revision_sensitive :
  forall previous first second, first <> second ->
    nativeEncodeAtomManifestSubjectDataModel
      (mkNativeAtomManifestSubjectDataModel previous first) <>
    nativeEncodeAtomManifestSubjectDataModel
      (mkNativeAtomManifestSubjectDataModel previous second).
Proof.
  intros previous first second Hneq Heq.
  apply Hneq.
  apply native_subject_revision_wire_injective.
  exact (f_equal snd Heq).
Qed.

(* #1584: conditional string model for concrete StageClosure I, following
   independently accepted R/L, normalized S, common C, closed F, subject B
   and checked atom-only D/V/Q/M. No Data.Text/Rocq string correspondence. *)
Definition NativeAtomManifestSubjectWireType : Type :=
  ((((((string * string) * list (string * string)) * (string * string)) * string) * string) * string) * string.

Record NativeAtomManifestInstanceDataModel :=
  mkNativeAtomManifestInstanceDataModel {
    nativeAtomManifestInstanceBaseData : NativeAtomManifestSubjectDataModel;
    nativeAtomManifestInstanceRevisionData : NativeInstanceRevisionRole
  }.

Definition nativeEncodeAtomManifestInstanceDataModel
  (data : NativeAtomManifestInstanceDataModel)
  : NativeAtomManifestSubjectWireType * string :=
  (nativeEncodeAtomManifestSubjectDataModel
     (nativeAtomManifestInstanceBaseData data),
   nativeInstanceRevisionWire (nativeAtomManifestInstanceRevisionData data)).

Definition nativeDecodeAtomManifestInstanceDataModel
  (wires : NativeAtomManifestSubjectWireType * string)
  : option NativeAtomManifestInstanceDataModel :=
  match nativeDecodeAtomManifestSubjectDataModel (fst wires),
        nativeDecodeInstanceRevisionWire (snd wires) with
  | Some baseData, Some revision =>
      Some (mkNativeAtomManifestInstanceDataModel baseData revision)
  | _, _ => None
  end.

Theorem native_atom_manifest_instance_data_model_roundtrip :
  forall data,
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel data) = Some data.
Proof.
  intros [previous [revision]].
  unfold nativeDecodeAtomManifestInstanceDataModel,
    nativeEncodeAtomManifestInstanceDataModel.
  simpl (fst (_, _)). simpl (snd (_, _)).
  rewrite native_atom_manifest_subject_data_model_roundtrip.
  reflexivity.
Qed.

Theorem native_atom_manifest_instance_data_model_injective :
  forall first second,
    nativeEncodeAtomManifestInstanceDataModel first =
      nativeEncodeAtomManifestInstanceDataModel second -> first = second.
Proof.
  intros first second H.
  apply (f_equal nativeDecodeAtomManifestInstanceDataModel) in H.
  rewrite !native_atom_manifest_instance_data_model_roundtrip in H.
  now injection H.
Qed.

Theorem native_atom_manifest_instance_data_model_wrong_role_reject :
  forall previous raw root systems common closed subject realization profile occurrence,
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestSubjectDataModel previous,
       nativeRawSystemsDigestWire raw) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestSubjectDataModel previous,
       nativeLoweringRootWire root) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestSubjectDataModel previous,
       nativeSystemsRevisionWire systems) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestSubjectDataModel previous,
       nativeCommonRevisionWire common) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestSubjectDataModel previous,
       nativeClosedRevisionWire closed) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestSubjectDataModel previous,
       nativeSubjectRevisionWire subject) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestSubjectDataModel previous,
       nativeRealizationRevisionWire realization) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestSubjectDataModel previous,
       nativeVerifierProfileTextWire profile) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestSubjectDataModel previous,
       nativeOccurrenceKeyWire occurrence) = None.
Proof.
  intros previous [raw] [root] [systems] [common] [closed]
    [subject] [realization] [profile] [occurrence].
  repeat split;
    unfold nativeDecodeAtomManifestInstanceDataModel;
    simpl;
    destruct (nativeDecodeAtomManifestSubjectDataModel
      (nativeEncodeAtomManifestSubjectDataModel previous)); reflexivity.
Qed.

Theorem native_atom_manifest_instance_data_model_revision_sensitive :
  forall previous first second, first <> second ->
    nativeEncodeAtomManifestInstanceDataModel
      (mkNativeAtomManifestInstanceDataModel previous first) <>
    nativeEncodeAtomManifestInstanceDataModel
      (mkNativeAtomManifestInstanceDataModel previous second).
Proof.
  intros previous first second Hneq Heq.
  apply Hneq.
  apply native_instance_revision_wire_injective.
  exact (f_equal snd Heq).
Qed.

(* #1584: conditional string model for concrete StageClosure I, following
   independently accepted R/L, normalized S, common C, closed F, subject B
   and checked atom-only D/V/Q/M. No Data.Text/Rocq string correspondence. *)
Definition NativeAtomManifestInstanceWireType : Type :=
  NativeAtomManifestInstanceWireType * string.

Record NativeAtomManifestRealizationDataModel :=
  mkNativeAtomManifestRealizationDataModel {
    nativeAtomManifestRealizationBaseData : NativeAtomManifestInstanceDataModel;
    nativeAtomManifestRealizationRevisionData : NativeRealizationRevisionRole
  }.

Definition nativeEncodeAtomManifestInstanceDataModel
  (data : NativeAtomManifestRealizationDataModel)
  : NativeAtomManifestInstanceWireType * string :=
  (nativeEncodeAtomManifestInstanceDataModel
     (nativeAtomManifestRealizationBaseData data),
   nativeRealizationRevisionWire (nativeAtomManifestRealizationRevisionData data)).

Definition nativeDecodeAtomManifestInstanceDataModel
  (wires : NativeAtomManifestInstanceWireType * string)
  : option NativeAtomManifestRealizationDataModel :=
  match nativeDecodeAtomManifestInstanceDataModel (fst wires),
        nativeDecodeRealizationRevisionWire (snd wires) with
  | Some baseData, Some revision =>
      Some (mkNativeAtomManifestRealizationDataModel baseData revision)
  | _, _ => None
  end.

Theorem native_atom_manifest_realization_data_model_roundtrip :
  forall data,
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel data) = Some data.
Proof.
  intros [previous [revision]].
  unfold nativeDecodeAtomManifestInstanceDataModel,
    nativeEncodeAtomManifestInstanceDataModel.
  simpl (fst (_, _)). simpl (snd (_, _)).
  rewrite native_atom_manifest_instance_data_model_roundtrip.
  reflexivity.
Qed.

Theorem native_atom_manifest_realization_data_model_injective :
  forall first second,
    nativeEncodeAtomManifestInstanceDataModel first =
      nativeEncodeAtomManifestInstanceDataModel second -> first = second.
Proof.
  intros first second H.
  apply (f_equal nativeDecodeAtomManifestInstanceDataModel) in H.
  rewrite !native_atom_manifest_realization_data_model_roundtrip in H.
  now injection H.
Qed.

Theorem native_atom_manifest_realization_data_model_wrong_role_reject :
  forall previous raw root systems common closed subject instance profile occurrence,
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel previous,
       nativeRawSystemsDigestWire raw) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel previous,
       nativeLoweringRootWire root) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel previous,
       nativeSystemsRevisionWire systems) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel previous,
       nativeCommonRevisionWire common) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel previous,
       nativeClosedRevisionWire closed) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel previous,
       nativeSubjectRevisionWire subject) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel previous,
       nativeInstanceRevisionWire instance) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel previous,
       nativeVerifierProfileTextWire profile) = None /\
    nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel previous,
       nativeOccurrenceKeyWire occurrence) = None.
Proof.
  intros previous [raw] [root] [systems] [common] [closed]
    [subject] [instance] [profile] [occurrence].
  repeat split;
    unfold nativeDecodeAtomManifestInstanceDataModel;
    simpl;
    destruct (nativeDecodeAtomManifestInstanceDataModel
      (nativeEncodeAtomManifestInstanceDataModel previous)); reflexivity.
Qed.

Theorem native_atom_manifest_realization_data_model_revision_sensitive :
  forall previous first second, first <> second ->
    nativeEncodeAtomManifestInstanceDataModel
      (mkNativeAtomManifestRealizationDataModel previous first) <>
    nativeEncodeAtomManifestInstanceDataModel
      (mkNativeAtomManifestRealizationDataModel previous second).
Proof.
  intros previous first second Hneq Heq.
  apply Hneq.
  apply native_realization_revision_wire_injective.
  exact (f_equal snd Heq).
Qed.
