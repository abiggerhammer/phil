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

End NativeFinalInstanceTypedCorrespondence.

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
