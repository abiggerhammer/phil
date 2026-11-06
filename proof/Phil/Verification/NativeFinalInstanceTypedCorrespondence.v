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
