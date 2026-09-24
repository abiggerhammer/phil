From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Assurance Require Import CheckEventPrerequisiteCoverage.

(*
  Defensive proof-correspondence continuation of the original check-event
  closeout handoff.

  CheckEventPrerequisiteCoverage.v proves that every mandatory prerequisite of
  an admitted check event reaches the final support relation when the complete
  event domain is accounted for.  The audit identified one further,
  independent completeness boundary: a correct support relation is not yet the
  retained residual forest, and a correct retained forest is not yet proof
  that the final scope consumer actually uses it.

  This model keeps those stages explicit.  It does not model or change the
  concrete Haskell accepting entry, residual-map representation, evidence
  authority, export policy, ownership state, native lowering, or the Phase 1
  trusted computing base.  Those remain correspondence premises owned by their
  existing lanes.
*)

Definition ResidualForestRootId := nat.
Definition FinalScopeId := nat.

Record OriginalEventForestModel : Type := mkOriginalEventForestModel {
  originalEventPrerequisiteModel : CheckEventPrerequisiteModel;
  modelEventForestRoot : CheckEventId -> ResidualForestRootId;
  modelForestPrerequisite :
    ResidualForestRootId -> SupportRevisionId -> bool;
  modelEventFinalScope : CheckEventId -> FinalScopeId;
  modelScopeForestPrerequisite :
    FinalScopeId -> ResidualForestRootId -> SupportRevisionId -> bool
}.

(* Every support edge produced for the exact event is retained by that event's
   residual-forest root.  This is the faithful-reflection step that cannot be
   obtained merely from a theorem about certificate leaves. *)
Definition SupportFaithfullyReflectedInForest
  (model : OriginalEventForestModel) : Prop :=
  forall event prerequisite,
    modelEvidenceDependsOn
      (eventSupportModel (originalEventPrerequisiteModel model))
      (modelEventEvidence (originalEventPrerequisiteModel model) event)
      prerequisite = true ->
    modelForestPrerequisite
      model
      (modelEventForestRoot model event)
      prerequisite = true.

(* The final scope consumer uses the retained relation rather than a separately
   reconstructed or incomplete prerequisite inventory. *)
Definition FinalScopeConsumesRetainedForest
  (model : OriginalEventForestModel) : Prop :=
  forall event prerequisite,
    modelForestPrerequisite
      model
      (modelEventForestRoot model event)
      prerequisite = true ->
    modelScopeForestPrerequisite
      model
      (modelEventFinalScope model event)
      (modelEventForestRoot model event)
      prerequisite = true.

Definition OriginalEventFinalScopeComplete
  (model : OriginalEventForestModel) : Prop :=
  forall event prerequisite,
    modelMandatoryPrerequisite
      (originalEventPrerequisiteModel model)
      event
      prerequisite = true ->
    modelScopeForestPrerequisite
      model
      (modelEventFinalScope model event)
      (modelEventForestRoot model event)
      prerequisite = true.

Theorem preserved_event_support_reaches_final_scope :
  forall model,
    EventSupportPreserved (originalEventPrerequisiteModel model) ->
    SupportFaithfullyReflectedInForest model ->
    FinalScopeConsumesRetainedForest model ->
    OriginalEventFinalScopeComplete model.
Proof.
  intros model Hsupport Hreflect Hscope.
  intros event prerequisite Hrequired.
  eapply Hscope.
  eapply Hreflect.
  eapply Hsupport.
  exact Hrequired.
Qed.

(* Compose the previous check-event coverage theorem all the way through the
   retained forest and the final scope consumer. *)
Theorem accounted_original_event_reaches_final_scope :
  forall model,
    CertificateSupportPreserved
      (eventSupportModel (originalEventPrerequisiteModel model)) ->
    OperationSupportPreserved (originalEventPrerequisiteModel model) ->
    EventPrerequisiteAccountedFor (originalEventPrerequisiteModel model) ->
    SupportFaithfullyReflectedInForest model ->
    FinalScopeConsumesRetainedForest model ->
    OriginalEventFinalScopeComplete model.
Proof.
  intros model Hcertificate Hoperation Haccounted Hreflect Hscope.
  eapply preserved_event_support_reaches_final_scope.
  - eapply accounted_event_prerequisites_reach_final_support.
    + exact Hcertificate.
    + exact Hoperation.
    + exact Haccounted.
  - exact Hreflect.
  - exact Hscope.
Qed.

(*
  Negative witness for the remaining handoff gap.  The predecessor's routed
  definition-only event has complete event support: its mandatory prerequisite
  reaches evidence 10.  Here the next adapter silently drops every support edge
  before constructing the retained forest and final scope.  Thus the previous
  theorem remains true while original-event-to-scope completeness fails.
*)
Definition DroppedOriginalEventForestWitness : OriginalEventForestModel :=
  mkOriginalEventForestModel
    RoutedDefinitionPrerequisiteWitness
    (fun _ => 20)
    (fun _ _ => false)
    (fun _ => 30)
    (fun _ _ _ => false).

Theorem dropped_forest_witness_preserves_event_support :
  EventSupportPreserved
    (originalEventPrerequisiteModel DroppedOriginalEventForestWitness).
Proof.
  exact routed_definition_prerequisite_reaches_final_support.
Qed.

Theorem dropped_forest_witness_is_not_faithful_reflection :
  ~ SupportFaithfullyReflectedInForest DroppedOriginalEventForestWitness.
Proof.
  intro Hreflect.
  assert
    (Hsupport :
      modelEvidenceDependsOn
        (eventSupportModel
          (originalEventPrerequisiteModel DroppedOriginalEventForestWitness))
        (modelEventEvidence
          (originalEventPrerequisiteModel DroppedOriginalEventForestWitness)
          7)
        0 = true).
  { reflexivity. }
  specialize (Hreflect 7 0 Hsupport).
  cbn in Hreflect.
  discriminate.
Qed.

Theorem dropped_forest_witness_is_not_final_scope_complete :
  ~ OriginalEventFinalScopeComplete DroppedOriginalEventForestWitness.
Proof.
  intro Hcomplete.
  assert
    (Hrequired :
      modelMandatoryPrerequisite
        (originalEventPrerequisiteModel DroppedOriginalEventForestWitness)
        7
        0 = true).
  { reflexivity. }
  specialize (Hcomplete 7 0 Hrequired).
  cbn in Hcomplete.
  discriminate.
Qed.

Theorem event_support_alone_does_not_close_original_event_scope :
  EventSupportPreserved
      (originalEventPrerequisiteModel DroppedOriginalEventForestWitness) /\
  ~ OriginalEventFinalScopeComplete DroppedOriginalEventForestWitness.
Proof.
  split.
  - exact dropped_forest_witness_preserves_event_support.
  - exact dropped_forest_witness_is_not_final_scope_complete.
Qed.

(*
  Positive bounded witness.  It uses the same routed certificate-free event as
  CheckEventPrerequisiteCoverage.v, but makes the next two transports explicit:
  the event's support relation is retained by its forest and the final scope
  consumes that retained relation.  Root/scope identity authority is a separate
  correspondence obligation; this witness establishes only completeness of the
  retained relation.
*)
Definition ReflectedOriginalEventForestWitness : OriginalEventForestModel :=
  mkOriginalEventForestModel
    RoutedDefinitionPrerequisiteWitness
    (fun _ => 20)
    (fun _ prerequisite =>
      modelEvidenceDependsOn ExplicitOperationSupport 10 prerequisite)
    (fun _ => 30)
    (fun _ _ prerequisite =>
      modelEvidenceDependsOn ExplicitOperationSupport 10 prerequisite).

Theorem reflected_forest_witness_is_faithful :
  SupportFaithfullyReflectedInForest ReflectedOriginalEventForestWitness.
Proof.
  intros event prerequisite Hsupport.
  cbn in Hsupport |- *.
  exact Hsupport.
Qed.

Theorem reflected_forest_witness_is_consumed_by_scope :
  FinalScopeConsumesRetainedForest ReflectedOriginalEventForestWitness.
Proof.
  intros event prerequisite Hretained.
  cbn in Hretained |- *.
  exact Hretained.
Qed.

Theorem reflected_forest_witness_closes_original_event_scope :
  OriginalEventFinalScopeComplete ReflectedOriginalEventForestWitness.
Proof.
  eapply preserved_event_support_reaches_final_scope.
  - exact routed_definition_prerequisite_reaches_final_support.
  - exact reflected_forest_witness_is_faithful.
  - exact reflected_forest_witness_is_consumed_by_scope.
Qed.
