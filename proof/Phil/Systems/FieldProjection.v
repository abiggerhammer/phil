From Phil.Systems Require Import ScalarDataflow.

(*
  PHIL-SYS-FIELD-PROJ-001 — proof-oriented model of
  Phil.Systems.FieldProjection.verifyFieldProjectionWitnesses.

  This proof deliberately reuses PHIL-SYS-SSA-001 for unique-definition and
  definition-before-use / dominance reasoning.  It adds only the
  field-projection-specific authority boundary: the projected scalar must be
  tied to the same recognized pending value, grammar, success path, schema
  field/type, post-commit projection site, lowering decision, and exact-receive
  consumer described by the witness.

  Concrete Text/ValueId/BlockId identities, Data.Map/list enumeration,
  runtime-call name rendering, schema-table lookup, operation indexing, and CFG
  dominance computation remain implementation boundaries.
*)

Definition ProjectionGrammarId := nat.
Definition ProjectionFieldId := nat.
Definition ProjectionTypeId := nat.
Definition ProjectionBlockId := nat.
Definition ProjectionDecisionId := nat.

Record FieldProjectionModel : Type := mkFieldProjectionModel {
  projectionDataflow : ScalarDataflowModel;

  projectionWitnessPending : ValueId;
  projectionActualPending : ValueId;
  projectionWitnessGrammar : ProjectionGrammarId;
  projectionActualGrammar : ProjectionGrammarId;
  projectionRecognitionSuccess : ProjectionBlockId;
  projectionWitnessSuccess : ProjectionBlockId;

  projectionWitnessField : ProjectionFieldId;
  projectionActualField : ProjectionFieldId;
  projectionWitnessType : ProjectionTypeId;
  projectionActualType : ProjectionTypeId;
  projectionSchemaType : ProjectionGrammarId -> ProjectionFieldId -> option ProjectionTypeId;

  projectionCommitPending : ValueId;
  projectionCommitSite : SiteId;
  projectionDefinitionSite : SiteId;
  projectionLocalOrder : SiteId -> SiteId -> Prop;

  projectionOutput : ValueId;
  projectionInputCount : nat;
  projectionExpectedDecision : ProjectionDecisionId;
  projectionActualDecision : ProjectionDecisionId;

  projectionExactReceiveLength : ValueId;
  projectionExactReceiveSite : SiteId
}.

Definition FieldProjectionVerificationSuccess
  (model : FieldProjectionModel) : Prop :=
  projectionActualPending model = projectionWitnessPending model /\
  projectionActualGrammar model = projectionWitnessGrammar model /\
  projectionRecognitionSuccess model = projectionWitnessSuccess model /\\n  projectionActualField model = projectionWitnessField model /\
  projectionSchemaType model
    (projectionWitnessGrammar model)
    (projectionWitnessField model) = Some (projectionWitnessType model) /\
  projectionActualType model = projectionWitnessType model /\
  projectionCommitPending model = projectionWitnessPending model /\
  projectionLocalOrder model
    (projectionCommitSite model)
    (projectionDefinitionSite model) /\
  projectionInputCount model = 0 /\
  projectionActualDecision model = projectionExpectedDecision model /\
  projectionExactReceiveLength model = projectionOutput model /\
  scalarTyped (projectionDataflow model) (projectionOutput model) /\
  scalarDefinitionAt
    (projectionDataflow model)
    (projectionOutput model)
    (projectionDefinitionSite model) /\
  scalarUseAt
    (projectionDataflow model)
    (projectionExactReceiveLength model)
    (projectionExactReceiveSite model) /\
  ScalarDataflowVerificationSuccess (projectionDataflow model).

Theorem verified_field_projection_preserves_recognition_identity :
  forall model,
    FieldProjectionVerificationSuccess model ->
    projectionActualPending model = projectionWitnessPending model /\
    projectionActualGrammar model = projectionWitnessGrammar model /\
    projectionRecognitionSuccess model = projectionWitnessSuccess model.
Proof.
  intros model Hverified.
  destruct Hverified as [Hpending [Hgrammar [Hsuccess _]]].
  repeat split; assumption.
Qed.

Theorem verified_field_projection_preserves_schema_identity_and_type :
  forall model,
    FieldProjectionVerificationSuccess model ->
    projectionActualField model = projectionWitnessField model /\
    projectionSchemaType model
      (projectionWitnessGrammar model)
      (projectionWitnessField model) = Some (projectionWitnessType model) /\
    projectionActualType model = projectionWitnessType model.
Proof.
  intros model Hverified.
  destruct Hverified as [_ [_ [_ [Hfield [Hschema [Htype _]]]]]].
  repeat split; assumption.
Qed.

Theorem verified_field_projection_occurs_after_matching_commit :
  forall model,
    FieldProjectionVerificationSuccess model ->
    projectionCommitPending model = projectionWitnessPending model /\
    projectionLocalOrder model
      (projectionCommitSite model)
      (projectionDefinitionSite model).
Proof.
  intros model Hverified.
  destruct Hverified as
    [_ [_ [_ [_ [_ [_ [Hcommit [Horder _]]]]]]]].
  split; assumption.
Qed.

Theorem verified_field_projection_has_exact_call_shape_and_decision :
  forall model,
    FieldProjectionVerificationSuccess model ->
    projectionInputCount model = 0 /\
    projectionActualDecision model = projectionExpectedDecision model.
Proof.
  intros model Hverified.
  destruct Hverified as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hinputs [Hdecision _]]]]]]]]]].
  split; assumption.
Qed.

Theorem verified_field_projection_feeds_exact_receive :
  forall model,
    FieldProjectionVerificationSuccess model ->
    projectionExactReceiveLength model = projectionOutput model.
Proof.
  intros model Hverified.
  destruct Hverified as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hreceive _]]]]]]]]]]].
  exact Hreceive.
Qed.

Theorem verified_field_projection_output_has_unique_preceding_definition :
  forall model,
    FieldProjectionVerificationSuccess model ->
    exists definitionSite,
      scalarDefinitionAt
        (projectionDataflow model)
        (projectionOutput model)
        definitionSite /\
      scalarPrecedes
        (projectionDataflow model)
        definitionSite
        (projectionExactReceiveSite model) /\
      forall otherSite,
        scalarDefinitionAt
          (projectionDataflow model)
          (projectionOutput model)
          otherSite ->
        otherSite = definitionSite.
Proof.
  intros model Hverified.
  destruct Hverified as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hreceive
      [Htyped [_ [Huse Hdataflow]]]]]]]]]]]]]].
  rewrite Hreceive in Huse.
  exact
    (verified_scalar_use_has_unique_preceding_definition
      (projectionDataflow model)
      (projectionOutput model)
      (projectionExactReceiveSite model)
      Hdataflow Htyped Huse).
Qed.

Theorem field_projection_schema_drift_is_rejected :
  forall model,
    projectionSchemaType model
      (projectionWitnessGrammar model)
      (projectionWitnessField model) <>
      Some (projectionWitnessType model) ->
    ~ FieldProjectionVerificationSuccess model.
Proof.
  intros model Hdrift Hverified.
  apply Hdrift.
  destruct Hverified as [_ [_ [_ [_ [Hschema _]]]]].
  exact Hschema.
Qed.

Theorem field_projection_before_commit_is_rejected :
  forall model,
    ~ projectionLocalOrder model
        (projectionCommitSite model)
        (projectionDefinitionSite model) ->
    ~ FieldProjectionVerificationSuccess model.
Proof.
  intros model HnotAfter Hverified.
  apply HnotAfter.
  destruct Hverified as
    [_ [_ [_ [_ [_ [_ [_ [Horder _]]]]]]]].
  exact Horder.
Qed.

Theorem field_projection_decision_drift_is_rejected :
  forall model,
    projectionActualDecision model <> projectionExpectedDecision model ->
    ~ FieldProjectionVerificationSuccess model.
Proof.
  intros model Hdrift Hverified.
  apply Hdrift.
  destruct Hverified as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hdecision _]]]]]]]]]].
  exact Hdecision.
Qed.

Theorem field_projection_wrong_exact_receive_target_is_rejected :
  forall model,
    projectionExactReceiveLength model <> projectionOutput model ->
    ~ FieldProjectionVerificationSuccess model.
Proof.
  intros model Hwrong Hverified.
  apply Hwrong.
  apply verified_field_projection_feeds_exact_receive.
  exact Hverified.
Qed.

Theorem field_projection_non_dominating_output_is_rejected :
  forall model,
    (forall definitionSite,
      scalarDefinitionAt
        (projectionDataflow model)
        (projectionOutput model)
        definitionSite ->
      ~ scalarPrecedes
          (projectionDataflow model)
          definitionSite
          (projectionExactReceiveSite model)) ->
    ~ FieldProjectionVerificationSuccess model.
Proof.
  intros model HnotDominating Hverified.
  pose proof
    (verified_field_projection_output_has_unique_preceding_definition
      model Hverified) as Hdefinition.
  destruct Hdefinition as [site [Hdefined [Hprecedes _]]].
  exact (HnotDominating site Hdefined Hprecedes).
Qed.
