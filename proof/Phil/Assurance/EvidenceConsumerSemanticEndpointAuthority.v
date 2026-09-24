From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Surface Require Import BranchEvidenceSupport.
From Phil.Assurance Require Import
  EvidenceConsumerSubjectTransport
  EvidenceConsumerFinalUseCorrespondence
  EvidenceConsumerSubjectOccurrenceCoverage
  EvidenceConsumerEventOriginCorrespondence.

(*
  Defensive proof-correspondence continuation of D-RES-SUPPORT-01 /
  D-RES-TREE-01 after exact event-origin correspondence.

  EvidenceConsumerSubjectOccurrenceCoverage.v requires every represented
  subject-bearing position to carry source and target SubjectId endpoints, and
  EvidenceConsumerEventOriginCorrespondence.v binds the corresponding actual
  use to an approved original checking event.  Those facts still do not show
  that the endpoint pair was obtained from competent declaration, binding, or
  checked-rebase evidence for that exact event.  A caller could otherwise
  supply numerically matching endpoint metadata and receive proof credit.

  This module makes that authority edge explicit.  Every actual subject
  occurrence must bind its exact source/target pair to competent semantic
  endpoint authority under the same approved original event.  Authority for a
  different event is insufficient.

  The concrete Haskell implementation remains responsible for reflecting the
  native declaration/binding/checked-rebase evidence into this predicate.  A
  local use/occurrence index is not itself a semantic SubjectId or historical
  event identity.  This proof does not manufacture identities, infer authority
  from names or types, restore consumed ownership, change native lowering, or
  move LLVM outside the Phase 1 trusted-computing-base boundary.
*)

Record EvidenceConsumerSemanticEndpointAuthorityModel : Type :=
  mkEvidenceConsumerSemanticEndpointAuthorityModel {
    modelEndpointEventOrigin : EvidenceConsumerEventOriginModel;
    modelCompetentOccurrenceEndpoint :
      EvidenceUseEventId ->
      EvidenceConsumerId ->
      EvidenceSubjectOccurrenceId ->
      SubjectId -> SubjectId -> bool
  }.

Definition semanticEndpointOccurrenceModel
  (model : EvidenceConsumerSemanticEndpointAuthorityModel)
  : EvidenceConsumerSubjectOccurrenceCoverageModel :=
  modelOriginSubjectOccurrences (modelEndpointEventOrigin model).

Definition semanticEndpointFinalUseModel
  (model : EvidenceConsumerSemanticEndpointAuthorityModel)
  : EvidenceConsumerFinalUseModel :=
  modelOccurrenceFinalUse (semanticEndpointOccurrenceModel model).

Definition CompetentActualSubjectOccurrenceEndpointAuthority
  (model : EvidenceConsumerSemanticEndpointAuthorityModel) : Prop :=
  forall consumer occurrence event source target,
    modelActualEvidenceUse
      (modelFinalUseClassification (semanticEndpointFinalUseModel model))
      consumer = true ->
    modelActualSubjectOccurrence
      (semanticEndpointOccurrenceModel model) consumer occurrence = true ->
    modelActualUseEvent
      (semanticEndpointFinalUseModel model) consumer = Some event ->
    modelOccurrenceSourceSubject
      (semanticEndpointOccurrenceModel model) consumer occurrence = Some source ->
    modelOccurrenceTargetSubject
      (semanticEndpointOccurrenceModel model) consumer occurrence = Some target ->
    modelCompetentOccurrenceEndpoint
      model event consumer occurrence source target = true.

Definition CompleteEvidenceConsumerSemanticEndpointAuthority
  (model : EvidenceConsumerSemanticEndpointAuthorityModel) : Prop :=
  CompleteEvidenceConsumerEventOriginCorrespondence
    (modelEndpointEventOrigin model) /\
  CompetentActualSubjectOccurrenceEndpointAuthority model.

Theorem event_origin_and_competent_occurrence_endpoints_compose :
  forall model,
    CompleteEvidenceConsumerEventOriginCorrespondence
      (modelEndpointEventOrigin model) ->
    CompetentActualSubjectOccurrenceEndpointAuthority model ->
    CompleteEvidenceConsumerSemanticEndpointAuthority model.
Proof.
  intros model Horigin Hendpoints.
  split; assumption.
Qed.

(*
  Negative witness: event 7 and both subject occurrences already satisfy the
  complete event-origin chain, but no source/target pair has competent semantic
  authority.  Structural endpoint equality therefore cannot establish the new
  boundary by itself.
*)
Definition unqualifiedSemanticEndpointWitness
  : EvidenceConsumerSemanticEndpointAuthorityModel :=
  mkEvidenceConsumerSemanticEndpointAuthorityModel
    multiSubjectApprovedEventOriginWitness
    (fun _ _ _ _ _ => false).

Theorem unqualified_endpoints_still_have_complete_event_origin_correspondence :
  CompleteEvidenceConsumerEventOriginCorrespondence
    (modelEndpointEventOrigin unqualifiedSemanticEndpointWitness).
Proof.
  exact multi_subject_use_has_complete_event_origin_correspondence.
Qed.

Theorem unqualified_endpoints_lack_competent_authority :
  ~ CompetentActualSubjectOccurrenceEndpointAuthority
      unqualifiedSemanticEndpointWitness.
Proof.
  intro Hauthority.
  pose proof
    (Hauthority 7 1 7 1 1 eq_refl eq_refl eq_refl eq_refl eq_refl)
    as Hqualified.
  cbn in Hqualified.
  discriminate Hqualified.
Qed.

Theorem complete_event_origin_does_not_establish_semantic_endpoint_authority :
  CompleteEvidenceConsumerEventOriginCorrespondence
    (modelEndpointEventOrigin unqualifiedSemanticEndpointWitness) /\
  ~ CompleteEvidenceConsumerSemanticEndpointAuthority
      unqualifiedSemanticEndpointWitness.
Proof.
  split.
  - exact unqualified_endpoints_still_have_complete_event_origin_correspondence.
  - intros [_ Hauthority].
    exact (unqualified_endpoints_lack_competent_authority Hauthority).
Qed.

(*
  Authority attached to a different event cannot authorize the exact endpoint
  pair under event 7, even though event 7 itself has approved producer origin.
*)
Definition wrongEventSemanticEndpointWitness
  : EvidenceConsumerSemanticEndpointAuthorityModel :=
  mkEvidenceConsumerSemanticEndpointAuthorityModel
    multiSubjectApprovedEventOriginWitness
    (fun event _ _ _ _ => Nat.eqb event 8).

Theorem different_event_endpoint_authority_is_insufficient :
  ~ CompetentActualSubjectOccurrenceEndpointAuthority
      wrongEventSemanticEndpointWitness.
Proof.
  intro Hauthority.
  pose proof
    (Hauthority 7 1 7 1 1 eq_refl eq_refl eq_refl eq_refl eq_refl)
    as Hqualified.
  cbn in Hqualified.
  discriminate Hqualified.
Qed.

Definition exactMultiSubjectEndpointAuthority
  (event : EvidenceUseEventId)
  (consumer : EvidenceConsumerId)
  (occurrence : EvidenceSubjectOccurrenceId)
  (source target : SubjectId) : bool :=
  if Nat.eqb event 7 then
    if Nat.eqb consumer 7 then
      if Nat.eqb occurrence 1 then
        if Nat.eqb source 1 then Nat.eqb target 1 else false
      else if Nat.eqb occurrence 2 then
        if Nat.eqb source 2 then Nat.eqb target 2 else false
      else false
    else false
  else false.

Definition qualifiedMultiSubjectSemanticEndpointWitness
  : EvidenceConsumerSemanticEndpointAuthorityModel :=
  mkEvidenceConsumerSemanticEndpointAuthorityModel
    multiSubjectApprovedEventOriginWitness
    exactMultiSubjectEndpointAuthority.

Theorem multi_subject_occurrence_endpoints_have_competent_authority :
  CompetentActualSubjectOccurrenceEndpointAuthority
    qualifiedMultiSubjectSemanticEndpointWitness.
Proof.
  intros consumer occurrence event source target
    Hactual Hoccurrence Hevent Hsource Htarget.
  cbn in Hactual.
  apply Nat.eqb_eq in Hactual.
  subst consumer.
  cbn in Hevent.
  inversion Hevent; subst event.
  unfold twoSubjectOccurrenceEndpoint in Hsource, Htarget.
  cbn in Hsource, Htarget.
  destruct (Nat.eqb occurrence 1) eqn:Hfirst.
  - inversion Hsource; subst source.
    inversion Htarget; subst target.
    unfold exactMultiSubjectEndpointAuthority.
    cbn.
    rewrite Hfirst.
    reflexivity.
  - destruct (Nat.eqb occurrence 2) eqn:Hsecond.
    + inversion Hsource; subst source.
      inversion Htarget; subst target.
      unfold exactMultiSubjectEndpointAuthority.
      cbn.
      rewrite Hfirst, Hsecond.
      reflexivity.
    + discriminate Hsource.
Qed.

Theorem multi_subject_use_has_complete_semantic_endpoint_authority :
  CompleteEvidenceConsumerSemanticEndpointAuthority
    qualifiedMultiSubjectSemanticEndpointWitness.
Proof.
  eapply event_origin_and_competent_occurrence_endpoints_compose.
  - exact multi_subject_use_has_complete_event_origin_correspondence.
  - exact multi_subject_occurrence_endpoints_have_competent_authority.
Qed.

(*
  Checked closed uses still require no fabricated subject identity.  Their
  event-origin correspondence remains mandatory, while endpoint authority is
  vacuous because there is no actual subject occurrence.
*)
Definition checkedClosedSemanticEndpointAuthorityWitness
  : EvidenceConsumerSemanticEndpointAuthorityModel :=
  mkEvidenceConsumerSemanticEndpointAuthorityModel
    checkedClosedApprovedEventOriginWitness
    (fun _ _ _ _ _ => false).

Theorem checked_closed_use_needs_no_semantic_endpoint_authority :
  CompetentActualSubjectOccurrenceEndpointAuthority
    checkedClosedSemanticEndpointAuthorityWitness.
Proof.
  intros consumer occurrence event source target
    Hactual Hoccurrence Hevent Hsource Htarget.
  cbn in Hoccurrence.
  discriminate Hoccurrence.
Qed.

Theorem checked_closed_use_has_complete_semantic_endpoint_authority :
  CompleteEvidenceConsumerSemanticEndpointAuthority
    checkedClosedSemanticEndpointAuthorityWitness.
Proof.
  eapply event_origin_and_competent_occurrence_endpoints_compose.
  - exact checked_closed_use_has_complete_event_origin_correspondence.
  - exact checked_closed_use_needs_no_semantic_endpoint_authority.
Qed.

Theorem semantic_endpoint_authority_distinguishes_metadata_and_competence :
  ~ CompetentActualSubjectOccurrenceEndpointAuthority
      unqualifiedSemanticEndpointWitness /\
  ~ CompetentActualSubjectOccurrenceEndpointAuthority
      wrongEventSemanticEndpointWitness /\
  CompleteEvidenceConsumerSemanticEndpointAuthority
    qualifiedMultiSubjectSemanticEndpointWitness /\
  CompleteEvidenceConsumerSemanticEndpointAuthority
    checkedClosedSemanticEndpointAuthorityWitness.
Proof.
  split.
  - exact unqualified_endpoints_lack_competent_authority.
  - split.
    + exact different_event_endpoint_authority_is_insufficient.
    + split.
      * exact multi_subject_use_has_complete_semantic_endpoint_authority.
      * exact checked_closed_use_has_complete_semantic_endpoint_authority.
Qed.
