From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Assurance Require Import PrerequisiteSupport.

(*
  Defensive proof-correspondence tranche following the 23 September support
  producer review.

  CertificateSupportPreserved proves that every prerequisite named by a
  certificate remains explicit support of that certificate's evidence.  The
  audit found a distinct route in which a check event retains a mandatory
  prerequisite even though the selected root disposition has no decision
  certificate.  In that case certificate support can be perfectly preserved
  while still saying nothing about the event prerequisite.

  This model keeps the two domains separate.  A mandatory check-event
  prerequisite is accounted for when it is represented either by the existing
  certificate-prerequisite relation or by an explicit operation/prerequisite
  relation.  Both routes must feed the same final support relation.

  Concrete Haskell construction of the check-event domain, disposition routing,
  immutable identities, runtime/export policy, and mandatory caller use remain
  implementation-correspondence premises.  This file does not claim that the
  current implementation already establishes them.
*)

Definition CheckEventId := nat.

Record CheckEventPrerequisiteModel : Type := mkCheckEventPrerequisiteModel {
  eventSupportModel : PrerequisiteSupportModel;
  modelMandatoryPrerequisite :
    CheckEventId -> SupportRevisionId -> bool;
  modelEventEvidence :
    CheckEventId -> SupportEvidenceId;
  modelOperationPrerequisite :
    CheckEventId -> SupportRevisionId -> bool
}.

Definition EventPrerequisiteAccountedFor
  (model : CheckEventPrerequisiteModel) : Prop :=
  forall event prerequisite,
    modelMandatoryPrerequisite model event prerequisite = true ->
    orb
      (modelCertificatePrerequisite
        (eventSupportModel model)
        (modelEventEvidence model event)
        prerequisite)
      (modelOperationPrerequisite model event prerequisite) = true.

Definition OperationSupportPreserved
  (model : CheckEventPrerequisiteModel) : Prop :=
  forall event prerequisite,
    modelOperationPrerequisite model event prerequisite = true ->
    modelEvidenceDependsOn
      (eventSupportModel model)
      (modelEventEvidence model event)
      prerequisite = true.

Definition EventSupportPreserved
  (model : CheckEventPrerequisiteModel) : Prop :=
  forall event prerequisite,
    modelMandatoryPrerequisite model event prerequisite = true ->
    modelEvidenceDependsOn
      (eventSupportModel model)
      (modelEventEvidence model event)
      prerequisite = true.

Theorem accounted_event_prerequisites_reach_final_support :
  forall model,
    CertificateSupportPreserved (eventSupportModel model) ->
    OperationSupportPreserved model ->
    EventPrerequisiteAccountedFor model ->
    EventSupportPreserved model.
Proof.
  intros model Hcertificate Hoperation Haccounted.
  intros event prerequisite Hrequired.
  specialize (Haccounted event prerequisite Hrequired).
  destruct
    (modelCertificatePrerequisite
      (eventSupportModel model)
      (modelEventEvidence model event)
      prerequisite)
    eqn:HcertificateUse.
  - eapply Hcertificate.
    exact HcertificateUse.
  - cbn in Haccounted.
    eapply Hoperation.
    exact Haccounted.
Qed.

(*
  Negative witness for the audit observation:

  - event 7 has mandatory prerequisite revision 0;
  - evidence 10 is the event's final support carrier;
  - no decision certificate names revision 0; and
  - no explicit operation/prerequisite route has been supplied.

  CertificateSupportPreserved is therefore vacuously true, while the check
  event's mandatory prerequisite is not preserved.  This demonstrates the
  missing domain premise without refuting PrerequisiteSupport.v.
*)
Definition DefinitionOnlyUnroutedSupport : PrerequisiteSupportModel :=
  mkPrerequisiteSupportModel
    (fun _ _ => false)
    (fun _ _ => false)
    (fun _ => 1)
    (fun _ _ => false)
    (fun _ _ => false).

Definition UnroutedDefinitionPrerequisiteWitness
  : CheckEventPrerequisiteModel :=
  mkCheckEventPrerequisiteModel
    DefinitionOnlyUnroutedSupport
    (fun event prerequisite =>
      andb (Nat.eqb event 7) (Nat.eqb prerequisite 0))
    (fun _ => 10)
    (fun _ _ => false).

Theorem unrouted_witness_preserves_certificate_support :
  CertificateSupportPreserved DefinitionOnlyUnroutedSupport.
Proof.
  intros evidence prerequisite Hused.
  discriminate Hused.
Qed.

Theorem unrouted_witness_has_mandatory_prerequisite :
  modelMandatoryPrerequisite
    UnroutedDefinitionPrerequisiteWitness 7 0 = true.
Proof.
  reflexivity.
Qed.

Theorem unrouted_witness_has_no_certificate_reference :
  modelCertificatePrerequisite
    (eventSupportModel UnroutedDefinitionPrerequisiteWitness)
    (modelEventEvidence UnroutedDefinitionPrerequisiteWitness 7)
    0 = false.
Proof.
  reflexivity.
Qed.

Theorem unrouted_witness_has_no_operation_route :
  modelOperationPrerequisite
    UnroutedDefinitionPrerequisiteWitness 7 0 = false.
Proof.
  reflexivity.
Qed.

Theorem unrouted_witness_is_not_accounted_for :
  ~ EventPrerequisiteAccountedFor UnroutedDefinitionPrerequisiteWitness.
Proof.
  intro Haccounted.
  specialize
    (Haccounted
      7 0
      unrouted_witness_has_mandatory_prerequisite).
  cbn in Haccounted.
  discriminate.
Qed.

Theorem certificate_support_alone_does_not_cover_check_event_domain :
  CertificateSupportPreserved DefinitionOnlyUnroutedSupport /\
  ~ EventSupportPreserved UnroutedDefinitionPrerequisiteWitness.
Proof.
  split.
  - exact unrouted_witness_preserves_certificate_support.
  - intro Hfinal.
    specialize
      (Hfinal
        7 0
        unrouted_witness_has_mandatory_prerequisite).
    cbn in Hfinal.
    discriminate.
Qed.

(*
  Positive no-certificate route.  The same mandatory event prerequisite is
  represented explicitly as an operation prerequisite, and the final support
  relation carries it.  This is the bounded shape needed for definitionally
  discharged roots with surviving runtime prerequisites; it does not prescribe
  the concrete Haskell adapter used to establish the relation.
*)
Definition ExplicitOperationSupport : PrerequisiteSupportModel :=
  mkPrerequisiteSupportModel
    (fun _ _ => false)
    (fun _ _ => false)
    (fun _ => 1)
    (fun _ _ => false)
    (fun evidence prerequisite =>
      andb (Nat.eqb evidence 10) (Nat.eqb prerequisite 0)).

Definition RoutedDefinitionPrerequisiteWitness
  : CheckEventPrerequisiteModel :=
  mkCheckEventPrerequisiteModel
    ExplicitOperationSupport
    (fun event prerequisite =>
      andb (Nat.eqb event 7) (Nat.eqb prerequisite 0))
    (fun _ => 10)
    (fun event prerequisite =>
      andb (Nat.eqb event 7) (Nat.eqb prerequisite 0)).

Theorem routed_witness_preserves_certificate_support :
  CertificateSupportPreserved ExplicitOperationSupport.
Proof.
  intros evidence prerequisite Hused.
  discriminate Hused.
Qed.

Theorem routed_witness_preserves_operation_support :
  OperationSupportPreserved RoutedDefinitionPrerequisiteWitness.
Proof.
  intros event prerequisite Hoperation.
  cbn in Hoperation |- *.
  destruct (Nat.eqb event 7) eqn:Hevent.
  - cbn in Hoperation |- *.
    exact Hoperation.
  - cbn in Hoperation.
    discriminate.
Qed.

Theorem routed_witness_accounts_for_event_prerequisite :
  EventPrerequisiteAccountedFor RoutedDefinitionPrerequisiteWitness.
Proof.
  intros event prerequisite Hrequired.
  cbn in Hrequired |- *.
  destruct (Nat.eqb event 7) eqn:Hevent.
  - rewrite Hevent in Hrequired.
    rewrite Hevent.
    cbn in Hrequired |- *.
    exact Hrequired.
  - rewrite Hevent in Hrequired.
    cbn in Hrequired.
    discriminate.
Qed.

Theorem routed_definition_prerequisite_reaches_final_support :
  EventSupportPreserved RoutedDefinitionPrerequisiteWitness.
Proof.
  eapply accounted_event_prerequisites_reach_final_support.
  - exact routed_witness_preserves_certificate_support.
  - exact routed_witness_preserves_operation_support.
  - exact routed_witness_accounts_for_event_prerequisite.
Qed.
