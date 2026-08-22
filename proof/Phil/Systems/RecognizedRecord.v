From Phil.Systems Require Import ScalarDataflow.

(*
  PHIL-SYS-RECORD-001 — normalized proof model for the recognized-record
  candidate introduced after the certified field-projection slice.

  The concrete implementation materializes an explicit RuntimeRecord value on
  the matching recognition-success path, after commit and before the typed
  field projection.  The projection must consume that exact record, preserve
  schema/type identity, feed the intended exact-receive consumer, and carry the
  exact content-bound materialization/projection decisions.

  This proof reuses PHIL-SYS-SSA-001 only for unique-definition and
  definition-before-use/dominance reasoning.  Concrete Text/ValueId/BlockId
  identity, Data.Map/list enumeration, schema lookup, operation indexing, and
  Haskell-to-normalized-model correspondence remain implementation boundaries.
*)

Definition RecordGrammarId := nat.
Definition RecordFieldId := nat.
Definition RecordTypeId := nat.
Definition RecordBlockId := nat.
Definition RecordDecisionId := nat.

Record RecognizedRecordModel : Type := mkRecognizedRecordModel {
  recordDataflow : ScalarDataflowModel;

  recordWitnessPending : ValueId;
  recordActualPending : ValueId;
  recordWitnessGrammar : RecordGrammarId;
  recordActualPendingGrammar : RecordGrammarId;
  recordActualRecordGrammar : RecordGrammarId;
  recordRecognitionSuccess : RecordBlockId;
  recordWitnessSuccess : RecordBlockId;

  recordValue : ValueId;
  recordCommitPending : ValueId;
  recordCommitSite : SiteId;
  recordMaterializationSite : SiteId;
  recordProjectionSite : SiteId;
  recordLocalOrder : SiteId -> SiteId -> Prop;
  recordMaterializationCount : nat;
  recordProjectionCount : nat;

  recordWitnessField : RecordFieldId;
  recordActualField : RecordFieldId;
  recordWitnessType : RecordTypeId;
  recordActualType : RecordTypeId;
  recordSchemaType : RecordGrammarId -> RecordFieldId -> option RecordTypeId;
  recordProjectionInput : ValueId;
  recordProjectionOutput : ValueId;

  recordExpectedMaterializationDecision : RecordDecisionId;
  recordActualMaterializationDecision : RecordDecisionId;
  recordExpectedProjectionDecision : RecordDecisionId;
  recordActualProjectionDecision : RecordDecisionId;

  recordExactReceiveLength : ValueId;
  recordExactReceiveSite : SiteId
}.

Record RecognizedRecordVerificationSuccess
  (model : RecognizedRecordModel) : Prop := mkRecognizedRecordVerificationSuccess {
  record_success_pending_identity :
    recordActualPending model = recordWitnessPending model;
  record_success_pending_grammar :
    recordActualPendingGrammar model = recordWitnessGrammar model;
  record_success_recognition_path :
    recordRecognitionSuccess model = recordWitnessSuccess model;
  record_success_record_grammar :
    recordActualRecordGrammar model = recordWitnessGrammar model;
  record_success_commit_pending :
    recordCommitPending model = recordWitnessPending model;
  record_success_single_materialization :
    recordMaterializationCount model = 1;
  record_success_single_projection :
    recordProjectionCount model = 1;
  record_success_commit_before_materialization :
    recordLocalOrder model
      (recordCommitSite model)
      (recordMaterializationSite model);
  record_success_materialization_before_projection :
    recordLocalOrder model
      (recordMaterializationSite model)
      (recordProjectionSite model);
  record_success_projection_record_input :
    recordProjectionInput model = recordValue model;
  record_success_field_identity :
    recordActualField model = recordWitnessField model;
  record_success_schema_type :
    recordSchemaType model
      (recordWitnessGrammar model)
      (recordWitnessField model) = Some (recordWitnessType model);
  record_success_actual_type :
    recordActualType model = recordWitnessType model;
  record_success_materialization_decision :
    recordActualMaterializationDecision model =
      recordExpectedMaterializationDecision model;
  record_success_projection_decision :
    recordActualProjectionDecision model =
      recordExpectedProjectionDecision model;
  record_success_exact_receive :
    recordExactReceiveLength model = recordProjectionOutput model;
  record_success_scalar_typed :
    scalarTyped (recordDataflow model) (recordProjectionOutput model);
  record_success_scalar_definition :
    scalarDefinitionAt
      (recordDataflow model)
      (recordProjectionOutput model)
      (recordProjectionSite model);
  record_success_scalar_use :
    scalarUseAt
      (recordDataflow model)
      (recordExactReceiveLength model)
      (recordExactReceiveSite model);
  record_success_dataflow :
    ScalarDataflowVerificationSuccess (recordDataflow model)
}.

Theorem verified_recognized_record_preserves_recognition_provenance :
  forall model,
    RecognizedRecordVerificationSuccess model ->
    recordActualPending model = recordWitnessPending model /\
    recordActualPendingGrammar model = recordWitnessGrammar model /\
    recordRecognitionSuccess model = recordWitnessSuccess model /\
    recordActualRecordGrammar model = recordWitnessGrammar model.
Proof.
  intros model H.
  repeat split.
  - exact (record_success_pending_identity model H).
  - exact (record_success_pending_grammar model H).
  - exact (record_success_recognition_path model H).
  - exact (record_success_record_grammar model H).
Qed.

Theorem verified_recognized_record_materializes_once_after_commit :
  forall model,
    RecognizedRecordVerificationSuccess model ->
    recordCommitPending model = recordWitnessPending model /\
    recordMaterializationCount model = 1 /\
    recordLocalOrder model
      (recordCommitSite model)
      (recordMaterializationSite model).
Proof.
  intros model H.
  repeat split.
  - exact (record_success_commit_pending model H).
  - exact (record_success_single_materialization model H).
  - exact (record_success_commit_before_materialization model H).
Qed.

Theorem verified_recognized_record_projection_consumes_exact_record :
  forall model,
    RecognizedRecordVerificationSuccess model ->
    recordProjectionCount model = 1 /\
    recordProjectionInput model = recordValue model /\
    recordLocalOrder model
      (recordMaterializationSite model)
      (recordProjectionSite model).
Proof.
  intros model H.
  repeat split.
  - exact (record_success_single_projection model H).
  - exact (record_success_projection_record_input model H).
  - exact (record_success_materialization_before_projection model H).
Qed.

Theorem verified_recognized_record_preserves_schema_type_and_exact_receive :
  forall model,
    RecognizedRecordVerificationSuccess model ->
    recordActualField model = recordWitnessField model /\
    recordSchemaType model
      (recordWitnessGrammar model)
      (recordWitnessField model) = Some (recordWitnessType model) /\
    recordActualType model = recordWitnessType model /\
    recordExactReceiveLength model = recordProjectionOutput model.
Proof.
  intros model H.
  repeat split.
  - exact (record_success_field_identity model H).
  - exact (record_success_schema_type model H).
  - exact (record_success_actual_type model H).
  - exact (record_success_exact_receive model H).
Qed.

Theorem verified_recognized_record_decisions_are_exact :
  forall model,
    RecognizedRecordVerificationSuccess model ->
    recordActualMaterializationDecision model =
      recordExpectedMaterializationDecision model /\
    recordActualProjectionDecision model =
      recordExpectedProjectionDecision model.
Proof.
  intros model H.
  split.
  - exact (record_success_materialization_decision model H).
  - exact (record_success_projection_decision model H).
Qed.

Theorem verified_recognized_record_output_has_unique_preceding_definition :
  forall model,
    RecognizedRecordVerificationSuccess model ->
    exists definitionSite,
      scalarDefinitionAt
        (recordDataflow model)
        (recordProjectionOutput model)
        definitionSite /\
      scalarPrecedes
        (recordDataflow model)
        definitionSite
        (recordExactReceiveSite model) /\
      forall otherSite,
        scalarDefinitionAt
          (recordDataflow model)
          (recordProjectionOutput model)
          otherSite ->
        otherSite = definitionSite.
Proof.
  intros model H.
  pose proof (record_success_scalar_use model H) as Huse.
  rewrite (record_success_exact_receive model H) in Huse.
  exact
    (verified_scalar_use_has_unique_preceding_definition
      (recordDataflow model)
      (recordProjectionOutput model)
      (recordExactReceiveSite model)
      (record_success_dataflow model H)
      (record_success_scalar_typed model H)
      Huse).
Qed.

Theorem recognized_record_wrong_record_identity_is_rejected :
  forall model,
    recordProjectionInput model <> recordValue model ->
    ~ RecognizedRecordVerificationSuccess model.
Proof.
  intros model Hwrong H.
  apply Hwrong.
  exact (record_success_projection_record_input model H).
Qed.

Theorem recognized_record_competing_materialization_is_rejected :
  forall model,
    recordMaterializationCount model <> 1 ->
    ~ RecognizedRecordVerificationSuccess model.
Proof.
  intros model Hcount H.
  apply Hcount.
  exact (record_success_single_materialization model H).
Qed.

Theorem recognized_record_bad_ordering_is_rejected :
  forall model,
    (~ recordLocalOrder model
      (recordCommitSite model)
      (recordMaterializationSite model)) \/
    (~ recordLocalOrder model
      (recordMaterializationSite model)
      (recordProjectionSite model)) ->
    ~ RecognizedRecordVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hbad | Hbad].
  - apply Hbad. exact (record_success_commit_before_materialization model H).
  - apply Hbad. exact (record_success_materialization_before_projection model H).
Qed.

Theorem recognized_record_schema_or_type_drift_is_rejected :
  forall model,
    (recordSchemaType model
      (recordWitnessGrammar model)
      (recordWitnessField model) <>
      Some (recordWitnessType model)) \/
    recordActualType model <> recordWitnessType model ->
    ~ RecognizedRecordVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Hdrift | Hdrift].
  - apply Hdrift. exact (record_success_schema_type model H).
  - apply Hdrift. exact (record_success_actual_type model H).
Qed.

Theorem recognized_record_exact_receive_drift_is_rejected :
  forall model,
    recordExactReceiveLength model <> recordProjectionOutput model ->
    ~ RecognizedRecordVerificationSuccess model.
Proof.
  intros model Hwrong H.
  apply Hwrong.
  exact (record_success_exact_receive model H).
Qed.

Theorem recognized_record_decision_drift_is_rejected :
  forall model,
    recordActualMaterializationDecision model <>
      recordExpectedMaterializationDecision model \/
    recordActualProjectionDecision model <>
      recordExpectedProjectionDecision model ->
    ~ RecognizedRecordVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Hdrift | Hdrift].
  - apply Hdrift. exact (record_success_materialization_decision model H).
  - apply Hdrift. exact (record_success_projection_decision model H).
Qed.
