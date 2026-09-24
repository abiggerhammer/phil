From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Surface Require Import BranchEvidenceSupport.
From Phil.Assurance Require Import
  EvidenceConsumerSubjectTransport
  EvidenceConsumerUseClassification
  EvidenceConsumerFinalUseCorrespondence
  EvidenceConsumerSubjectOccurrenceCoverage
  EvidenceConsumerEventOriginCorrespondence
  EvidenceConsumerSemanticEndpointAuthority.

(*
  Defensive proof-correspondence continuation of D-RES-SUPPORT-01 /
  D-RES-TREE-01 after competent semantic endpoint authority.

  EvidenceConsumerSemanticEndpointAuthority.v establishes that every actual
  subject-bearing occurrence has competent source/target endpoint authority
  under the exact approved original event, while the inherited final-use
  correspondence establishes that the evidence use reaches a final consumer
  under that same event.  Those two facts can still be supplied independently:
  they do not by themselves state that the exact occurrence endpoint tuple is
  the one credited by the actual accepting operation.

  This module adds that final occurrence-level authority edge.  Every actual
  subject occurrence must keep its exact event, consumer, occurrence and
  source/target endpoint tuple all the way to the final accepting operation.
  An optional endpoint map or separately reconstructed graph is therefore not
  sufficient final-consumer correspondence.

  The concrete Haskell implementation remains responsible for reflecting the
  authentic returned ValueResult/EvidenceUse occurrence domain and the actual
  accepting operation into this predicate.  This proof does not manufacture
  identities, infer authority from names or types, restore consumed ownership,
  change native lowering, or move LLVM outside the Phase 1 trusted-computing-
  base boundary.
*)

Record EvidenceConsumerOccurrenceFinalAuthorityModel : Type :=
  mkEvidenceConsumerOccurrenceFinalAuthorityModel {
    modelOccurrenceSemanticAuthority :
      EvidenceConsumerSemanticEndpointAuthorityModel;
    modelFinalOccurrenceEndpointAccepted :
      EvidenceUseEventId ->
      EvidenceConsumerId ->
      EvidenceSubjectOccurrenceId ->
      SubjectId -> SubjectId -> bool
  }.

Definition occurrenceFinalOccurrenceModel
  (model : EvidenceConsumerOccurrenceFinalAuthorityModel)
  : EvidenceConsumerSubjectOccurrenceCoverageModel :=
  semanticEndpointOccurrenceModel (modelOccurrenceSemanticAuthority model).

Definition occurrenceFinalUseModel
  (model : EvidenceConsumerOccurrenceFinalAuthorityModel)
  : EvidenceConsumerFinalUseModel :=
  semanticEndpointFinalUseModel (modelOccurrenceSemanticAuthority model).

Definition SameAcceptingConsumerOccurrenceAuthority
  (model : EvidenceConsumerOccurrenceFinalAuthorityModel) : Prop :=
  forall consumer occurrence event source target,
    modelActualEvidenceUse
      (modelFinalUseClassification (occurrenceFinalUseModel model))
      consumer = true ->
    modelActualSubjectOccurrence
      (occurrenceFinalOccurrenceModel model) consumer occurrence = true ->
    modelActualUseEvent
      (occurrenceFinalUseModel model) consumer = Some event ->
    modelFinalUseEvent
      (occurrenceFinalUseModel model) consumer = Some event ->
    modelFinalConsumerUsesEvidence
      (occurrenceFinalUseModel model) consumer = true ->
    modelOccurrenceSourceSubject
      (occurrenceFinalOccurrenceModel model) consumer occurrence = Some source ->
    modelOccurrenceTargetSubject
      (occurrenceFinalOccurrenceModel model) consumer occurrence = Some target ->
    modelFinalOccurrenceEndpointAccepted
      model event consumer occurrence source target = true.

Definition CompleteEvidenceConsumerOccurrenceFinalAuthority
  (model : EvidenceConsumerOccurrenceFinalAuthorityModel) : Prop :=
  CompleteEvidenceConsumerSemanticEndpointAuthority
    (modelOccurrenceSemanticAuthority model) /\
  SameAcceptingConsumerOccurrenceAuthority model.

Theorem semantic_endpoint_and_same_accepting_occurrence_compose :
  forall model,
    CompleteEvidenceConsumerSemanticEndpointAuthority
      (modelOccurrenceSemanticAuthority model) ->
    SameAcceptingConsumerOccurrenceAuthority model ->
    CompleteEvidenceConsumerOccurrenceFinalAuthority model.
Proof.
  intros model Hsemantic Hfinal.
  split; assumption.
Qed.

(*
  Negative witness: the exact multi-subject occurrence endpoints already have
  complete competent semantic authority under event 7 and the evidence use
  reaches the final consumer under event 7, but no occurrence endpoint tuple
  is credited by that accepting operation.
*)
Definition omittedFinalOccurrenceEndpointWitness
  : EvidenceConsumerOccurrenceFinalAuthorityModel :=
  mkEvidenceConsumerOccurrenceFinalAuthorityModel
    qualifiedMultiSubjectSemanticEndpointWitness
    (fun _ _ _ _ _ => false).

Theorem omitted_final_occurrence_endpoint_still_has_complete_semantic_authority :
  CompleteEvidenceConsumerSemanticEndpointAuthority
    (modelOccurrenceSemanticAuthority omittedFinalOccurrenceEndpointWitness).
Proof.
  exact multi_subject_use_has_complete_semantic_endpoint_authority.
Qed.

Theorem omitted_final_occurrence_endpoint_lacks_accepting_authority :
  ~ SameAcceptingConsumerOccurrenceAuthority
      omittedFinalOccurrenceEndpointWitness.
Proof.
  intro Hfinal.
  pose proof
    (Hfinal 7 1 7 1 1
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl)
    as Haccepted.
  cbn in Haccepted.
  discriminate Haccepted.
Qed.

Theorem semantic_endpoint_authority_alone_does_not_establish_final_occurrence_credit :
  CompleteEvidenceConsumerSemanticEndpointAuthority
    (modelOccurrenceSemanticAuthority omittedFinalOccurrenceEndpointWitness) /\
  ~ CompleteEvidenceConsumerOccurrenceFinalAuthority
      omittedFinalOccurrenceEndpointWitness.
Proof.
  split.
  - exact omitted_final_occurrence_endpoint_still_has_complete_semantic_authority.
  - intros [_ Hfinal].
    exact (omitted_final_occurrence_endpoint_lacks_accepting_authority Hfinal).
Qed.

(*
  Positive multi-subject witness: final occurrence credit is exactly the same
  competent endpoint relation already established for the original event.
  The inherited same-event final-use premises ensure that this exact tuple is
  credited only at the actual accepting operation.
*)
Definition qualifiedMultiSubjectOccurrenceFinalAuthorityWitness
  : EvidenceConsumerOccurrenceFinalAuthorityModel :=
  mkEvidenceConsumerOccurrenceFinalAuthorityModel
    qualifiedMultiSubjectSemanticEndpointWitness
    (fun event consumer occurrence source target =>
      modelCompetentOccurrenceEndpoint
        qualifiedMultiSubjectSemanticEndpointWitness
        event consumer occurrence source target).

Theorem qualified_multi_subject_occurrences_reach_same_accepting_consumer :
  SameAcceptingConsumerOccurrenceAuthority
    qualifiedMultiSubjectOccurrenceFinalAuthorityWitness.
Proof.
  intros consumer occurrence event source target
    Hactual Hoccurrence Hevent Hfinal Hused Hsource Htarget.
  exact
    (multi_subject_occurrence_endpoints_have_competent_authority
      consumer occurrence event source target
      Hactual Hoccurrence Hevent Hsource Htarget).
Qed.

Theorem qualified_multi_subject_use_has_complete_occurrence_final_authority :
  CompleteEvidenceConsumerOccurrenceFinalAuthority
    qualifiedMultiSubjectOccurrenceFinalAuthorityWitness.
Proof.
  eapply semantic_endpoint_and_same_accepting_occurrence_compose.
  - exact multi_subject_use_has_complete_semantic_endpoint_authority.
  - exact qualified_multi_subject_occurrences_reach_same_accepting_consumer.
Qed.

(*
  Checked closed uses still carry no fabricated subject occurrence.  Their
  ordinary same-event final-use and approved-event requirements remain in the
  inherited correspondence, while occurrence-level endpoint credit is vacuous.
*)
Definition checkedClosedOccurrenceFinalAuthorityWitness
  : EvidenceConsumerOccurrenceFinalAuthorityModel :=
  mkEvidenceConsumerOccurrenceFinalAuthorityModel
    checkedClosedSemanticEndpointAuthorityWitness
    (fun _ _ _ _ _ => false).

Theorem checked_closed_use_needs_no_final_occurrence_endpoint_authority :
  SameAcceptingConsumerOccurrenceAuthority
    checkedClosedOccurrenceFinalAuthorityWitness.
Proof.
  intros consumer occurrence event source target
    Hactual Hoccurrence Hevent Hfinal Hused Hsource Htarget.
  cbn in Hoccurrence.
  discriminate Hoccurrence.
Qed.

Theorem checked_closed_use_has_complete_occurrence_final_authority :
  CompleteEvidenceConsumerOccurrenceFinalAuthority
    checkedClosedOccurrenceFinalAuthorityWitness.
Proof.
  eapply semantic_endpoint_and_same_accepting_occurrence_compose.
  - exact checked_closed_use_has_complete_semantic_endpoint_authority.
  - exact checked_closed_use_needs_no_final_occurrence_endpoint_authority.
Qed.

Theorem occurrence_final_authority_distinguishes_mapping_from_accepting_credit :
  ~ SameAcceptingConsumerOccurrenceAuthority
      omittedFinalOccurrenceEndpointWitness /\
  CompleteEvidenceConsumerOccurrenceFinalAuthority
    qualifiedMultiSubjectOccurrenceFinalAuthorityWitness /\
  CompleteEvidenceConsumerOccurrenceFinalAuthority
    checkedClosedOccurrenceFinalAuthorityWitness.
Proof.
  split.
  - exact omitted_final_occurrence_endpoint_lacks_accepting_authority.
  - split.
    + exact qualified_multi_subject_use_has_complete_occurrence_final_authority.
    + exact checked_closed_use_has_complete_occurrence_final_authority.
Qed.
