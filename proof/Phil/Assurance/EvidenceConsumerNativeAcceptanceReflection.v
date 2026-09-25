From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Surface Require Import BranchEvidenceSupport.
From Phil.Assurance Require Import
  EvidenceConsumerSubjectTransport
  EvidenceConsumerUseClassification
  EvidenceConsumerFinalUseCorrespondence
  EvidenceConsumerSubjectOccurrenceCoverage
  EvidenceConsumerEventOriginCorrespondence
  EvidenceConsumerSemanticEndpointAuthority
  EvidenceConsumerOccurrenceFinalAuthority.

(*
  Defensive proof-correspondence continuation of D-RES-SUPPORT-01 /
  D-RES-TREE-01 after occurrence-level final authority.

  EvidenceConsumerOccurrenceFinalAuthority.v states the proof-side condition
  once the actual evidence-use and subject-occurrence domain, competent
  endpoint tuples, event identity, and final accepting operation have already
  been reflected into the model.  The native wrapper now supplies an authentic
  returned-use/occurrence inventory and mandatory endpoint checks before
  immutable closure.  The remaining correspondence edge is to show that a
  successful native return is represented by exactly that proof-side domain
  and tuple data, rather than by another independently supplied Boolean layer
  or reconstructed graph.

  This module keeps that reflection boundary explicit.  It requires exact
  native/proof use and occurrence domains, exact event/source/target tuples,
  and visible final-assurance selection plus architecture/evidence packaging
  premises.  It does not manufacture any native relation.  The concrete
  Haskell implementation remains responsible for reflecting the actual
  successful wrapper return into these fields.

  The proof does not infer global occurrence identity, cross-event equality,
  or rebasing from names, types, or indices; it does not restore consumed
  ownership, change native lowering, or move LLVM outside the Phase 1 trusted
  computing base.
*)

Record EvidenceConsumerNativeAcceptanceReflectionModel : Type :=
  mkEvidenceConsumerNativeAcceptanceReflectionModel {
    modelNativeOccurrenceFinalAuthority :
      EvidenceConsumerOccurrenceFinalAuthorityModel;
    modelNativeAcceptedReturn : bool;
    modelNativeReturnedUse : EvidenceConsumerId -> bool;
    modelNativeReturnedOccurrence :
      EvidenceConsumerId -> EvidenceSubjectOccurrenceId -> bool;
    modelNativeUseEvent : EvidenceConsumerId -> option EvidenceUseEventId;
    modelNativeOccurrenceSourceSubject :
      EvidenceConsumerId -> EvidenceSubjectOccurrenceId -> option SubjectId;
    modelNativeOccurrenceTargetSubject :
      EvidenceConsumerId -> EvidenceSubjectOccurrenceId -> option SubjectId;
    modelNativeFinalAssuranceUseSelected : EvidenceConsumerId -> bool;
    modelNativeArchitectureEvidencePackageAccepted : bool
  }.

Definition nativeAcceptanceOccurrenceModel
  (model : EvidenceConsumerNativeAcceptanceReflectionModel)
  : EvidenceConsumerSubjectOccurrenceCoverageModel :=
  occurrenceFinalOccurrenceModel (modelNativeOccurrenceFinalAuthority model).

Definition nativeAcceptanceFinalUseModel
  (model : EvidenceConsumerNativeAcceptanceReflectionModel)
  : EvidenceConsumerFinalUseModel :=
  occurrenceFinalUseModel (modelNativeOccurrenceFinalAuthority model).

Definition NativeReturnedUseDomainExact
  (model : EvidenceConsumerNativeAcceptanceReflectionModel) : Prop :=
  forall consumer,
    modelNativeReturnedUse model consumer = true <->
    modelActualEvidenceUse
      (modelFinalUseClassification (nativeAcceptanceFinalUseModel model))
      consumer = true.

Definition NativeReturnedOccurrenceDomainExact
  (model : EvidenceConsumerNativeAcceptanceReflectionModel) : Prop :=
  forall consumer occurrence,
    modelNativeReturnedUse model consumer = true ->
    (modelNativeReturnedOccurrence model consumer occurrence = true <->
     modelActualSubjectOccurrence
       (nativeAcceptanceOccurrenceModel model) consumer occurrence = true).

Definition NativeEventAndEndpointTupleExact
  (model : EvidenceConsumerNativeAcceptanceReflectionModel) : Prop :=
  forall consumer,
    modelNativeReturnedUse model consumer = true ->
    modelNativeUseEvent model consumer =
      modelActualUseEvent (nativeAcceptanceFinalUseModel model) consumer /\
    modelNativeUseEvent model consumer =
      modelFinalUseEvent (nativeAcceptanceFinalUseModel model) consumer /\
    forall occurrence,
      modelNativeReturnedOccurrence model consumer occurrence = true ->
      modelNativeOccurrenceSourceSubject model consumer occurrence =
        modelOccurrenceSourceSubject
          (nativeAcceptanceOccurrenceModel model) consumer occurrence /\
      modelNativeOccurrenceTargetSubject model consumer occurrence =
        modelOccurrenceTargetSubject
          (nativeAcceptanceOccurrenceModel model) consumer occurrence.

Definition NativeAcceptanceInputsVisible
  (model : EvidenceConsumerNativeAcceptanceReflectionModel) : Prop :=
  modelNativeAcceptedReturn model = true ->
  modelNativeArchitectureEvidencePackageAccepted model = true /\
  forall consumer,
    modelNativeReturnedUse model consumer = true ->
    modelNativeFinalAssuranceUseSelected model consumer = true.

Definition CompleteEvidenceConsumerNativeAcceptanceReflection
  (model : EvidenceConsumerNativeAcceptanceReflectionModel) : Prop :=
  CompleteEvidenceConsumerOccurrenceFinalAuthority
    (modelNativeOccurrenceFinalAuthority model) /\
  NativeReturnedUseDomainExact model /\
  NativeReturnedOccurrenceDomainExact model /\
  NativeEventAndEndpointTupleExact model /\
  NativeAcceptanceInputsVisible model.

Theorem occurrence_final_authority_and_exact_native_reflection_compose :
  forall model,
    CompleteEvidenceConsumerOccurrenceFinalAuthority
      (modelNativeOccurrenceFinalAuthority model) ->
    NativeReturnedUseDomainExact model ->
    NativeReturnedOccurrenceDomainExact model ->
    NativeEventAndEndpointTupleExact model ->
    NativeAcceptanceInputsVisible model ->
    CompleteEvidenceConsumerNativeAcceptanceReflection model.
Proof.
  intros model Hfinal Huses Hoccurrences Htuples Hinputs.
  split.
  - exact Hfinal.
  - split.
    + exact Huses.
    + split.
      * exact Hoccurrences.
      * split.
        -- exact Htuples.
        -- exact Hinputs.
Qed.

(*
  Negative domain witness: the proof-side correspondence is complete for the
  real consumer 7, while a separately supplied native layer claims an extra
  consumer 8.  Completeness of the smaller proof domain cannot certify the
  larger returned domain.
*)
Definition extraNativeUseWitness
  : EvidenceConsumerNativeAcceptanceReflectionModel :=
  mkEvidenceConsumerNativeAcceptanceReflectionModel
    qualifiedMultiSubjectOccurrenceFinalAuthorityWitness
    true
    (fun consumer => orb (Nat.eqb consumer 7) (Nat.eqb consumer 8))
    twoSubjectOccurrenceSelected
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else Some 8)
    twoSubjectOccurrenceEndpoint
    twoSubjectOccurrenceEndpoint
    (fun consumer => orb (Nat.eqb consumer 7) (Nat.eqb consumer 8))
    true.

Theorem extra_native_use_still_has_complete_occurrence_final_authority :
  CompleteEvidenceConsumerOccurrenceFinalAuthority
    (modelNativeOccurrenceFinalAuthority extraNativeUseWitness).
Proof.
  exact qualified_multi_subject_use_has_complete_occurrence_final_authority.
Qed.

Theorem extra_native_use_breaks_exact_use_domain :
  ~ NativeReturnedUseDomainExact extraNativeUseWitness.
Proof.
  intro Hexact.
  destruct (Hexact 8) as [Hforward _].
  pose proof (Hforward eq_refl) as Hactual.
  cbn in Hactual.
  discriminate Hactual.
Qed.

(*
  Negative tuple witness: the domains are the intended ones, but the native
  layer reports event 8 while the proof-side original/final event is 7.
*)
Definition wrongNativeEventWitness
  : EvidenceConsumerNativeAcceptanceReflectionModel :=
  mkEvidenceConsumerNativeAcceptanceReflectionModel
    qualifiedMultiSubjectOccurrenceFinalAuthorityWitness
    true
    (fun consumer => Nat.eqb consumer 7)
    twoSubjectOccurrenceSelected
    (fun consumer => if Nat.eqb consumer 7 then Some 8 else None)
    twoSubjectOccurrenceEndpoint
    twoSubjectOccurrenceEndpoint
    (fun consumer => Nat.eqb consumer 7)
    true.

Theorem wrong_native_event_breaks_exact_tuple_reflection :
  ~ NativeEventAndEndpointTupleExact wrongNativeEventWitness.
Proof.
  intro Htuples.
  destruct (Htuples 7 eq_refl) as [Hevent _].
  cbn in Hevent.
  discriminate Hevent.
Qed.

(*
  Visibility witnesses: a successful return must not hide final-assurance use
  selection or fixture-owned architecture/evidence packaging behind the
  occurrence predicate.
*)
Definition missingNativeSelectionWitness
  : EvidenceConsumerNativeAcceptanceReflectionModel :=
  mkEvidenceConsumerNativeAcceptanceReflectionModel
    qualifiedMultiSubjectOccurrenceFinalAuthorityWitness
    true
    (fun consumer => Nat.eqb consumer 7)
    twoSubjectOccurrenceSelected
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    twoSubjectOccurrenceEndpoint
    twoSubjectOccurrenceEndpoint
    (fun _ => false)
    true.

Theorem missing_native_selection_is_not_visible_acceptance_input :
  ~ NativeAcceptanceInputsVisible missingNativeSelectionWitness.
Proof.
  intro Hinputs.
  destruct (Hinputs eq_refl) as [_ Hselected].
  pose proof (Hselected 7 eq_refl) as Hselection.
  cbn in Hselection.
  discriminate Hselection.
Qed.

Definition missingNativePackageWitness
  : EvidenceConsumerNativeAcceptanceReflectionModel :=
  mkEvidenceConsumerNativeAcceptanceReflectionModel
    qualifiedMultiSubjectOccurrenceFinalAuthorityWitness
    true
    (fun consumer => Nat.eqb consumer 7)
    twoSubjectOccurrenceSelected
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    twoSubjectOccurrenceEndpoint
    twoSubjectOccurrenceEndpoint
    (fun consumer => Nat.eqb consumer 7)
    false.

Theorem missing_native_package_is_not_visible_acceptance_input :
  ~ NativeAcceptanceInputsVisible missingNativePackageWitness.
Proof.
  intro Hinputs.
  destruct (Hinputs eq_refl) as [Hpackage _].
  cbn in Hpackage.
  discriminate Hpackage.
Qed.

(*
  Positive multi-subject witness: the native domain is exactly consumer 7 and
  its two subject occurrences, the native event and endpoint tuples are the
  same tuples already authorized by the proof model, and the final assurance
  selection/package premises remain explicit.
*)
Definition exactNativeAcceptanceWitness
  : EvidenceConsumerNativeAcceptanceReflectionModel :=
  mkEvidenceConsumerNativeAcceptanceReflectionModel
    qualifiedMultiSubjectOccurrenceFinalAuthorityWitness
    true
    (fun consumer => Nat.eqb consumer 7)
    twoSubjectOccurrenceSelected
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    twoSubjectOccurrenceEndpoint
    twoSubjectOccurrenceEndpoint
    (fun consumer => Nat.eqb consumer 7)
    true.

Theorem exact_native_use_domain_is_reflected :
  NativeReturnedUseDomainExact exactNativeAcceptanceWitness.
Proof.
  intro consumer.
  cbn.
  split; intro H; exact H.
Qed.

Theorem exact_native_occurrence_domain_is_reflected :
  NativeReturnedOccurrenceDomainExact exactNativeAcceptanceWitness.
Proof.
  intros consumer occurrence Huse.
  cbn.
  split; intro H; exact H.
Qed.

Theorem exact_native_event_and_endpoint_tuples_are_reflected :
  NativeEventAndEndpointTupleExact exactNativeAcceptanceWitness.
Proof.
  intros consumer Huse.
  cbn in Huse.
  apply Nat.eqb_eq in Huse.
  subst consumer.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + intros occurrence Hoccurrence.
      split; reflexivity.
Qed.

Theorem exact_native_acceptance_inputs_remain_visible :
  NativeAcceptanceInputsVisible exactNativeAcceptanceWitness.
Proof.
  intro Haccepted.
  split.
  - reflexivity.
  - intros consumer Huse.
    cbn in Huse |- *.
    exact Huse.
Qed.

Theorem exact_native_acceptance_has_complete_reflection :
  CompleteEvidenceConsumerNativeAcceptanceReflection
    exactNativeAcceptanceWitness.
Proof.
  eapply occurrence_final_authority_and_exact_native_reflection_compose.
  - exact qualified_multi_subject_use_has_complete_occurrence_final_authority.
  - exact exact_native_use_domain_is_reflected.
  - exact exact_native_occurrence_domain_is_reflected.
  - exact exact_native_event_and_endpoint_tuples_are_reflected.
  - exact exact_native_acceptance_inputs_remain_visible.
Qed.

(*
  Checked closed uses remain closed structurally: they keep their exact event,
  final selection and packaging premises but acquire no fabricated subject
  occurrence or endpoint.
*)
Definition checkedClosedNativeAcceptanceWitness
  : EvidenceConsumerNativeAcceptanceReflectionModel :=
  mkEvidenceConsumerNativeAcceptanceReflectionModel
    checkedClosedOccurrenceFinalAuthorityWitness
    true
    (fun consumer => Nat.eqb consumer 7)
    (fun _ _ => false)
    (fun consumer => if Nat.eqb consumer 7 then Some 7 else None)
    (fun _ _ => None)
    (fun _ _ => None)
    (fun consumer => Nat.eqb consumer 7)
    true.

Theorem checked_closed_native_use_domain_is_reflected :
  NativeReturnedUseDomainExact checkedClosedNativeAcceptanceWitness.
Proof.
  intro consumer.
  cbn.
  split; intro H; exact H.
Qed.

Theorem checked_closed_native_occurrence_domain_is_reflected :
  NativeReturnedOccurrenceDomainExact checkedClosedNativeAcceptanceWitness.
Proof.
  intros consumer occurrence Huse.
  cbn.
  split; intro H; exact H.
Qed.

Theorem checked_closed_native_event_and_endpoint_tuples_are_reflected :
  NativeEventAndEndpointTupleExact checkedClosedNativeAcceptanceWitness.
Proof.
  intros consumer Huse.
  cbn in Huse.
  apply Nat.eqb_eq in Huse.
  subst consumer.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + intros occurrence Hoccurrence.
      cbn in Hoccurrence.
      discriminate Hoccurrence.
Qed.

Theorem checked_closed_native_acceptance_inputs_remain_visible :
  NativeAcceptanceInputsVisible checkedClosedNativeAcceptanceWitness.
Proof.
  intro Haccepted.
  split.
  - reflexivity.
  - intros consumer Huse.
    cbn in Huse |- *.
    exact Huse.
Qed.

Theorem checked_closed_native_acceptance_has_complete_reflection :
  CompleteEvidenceConsumerNativeAcceptanceReflection
    checkedClosedNativeAcceptanceWitness.
Proof.
  eapply occurrence_final_authority_and_exact_native_reflection_compose.
  - exact checked_closed_use_has_complete_occurrence_final_authority.
  - exact checked_closed_native_use_domain_is_reflected.
  - exact checked_closed_native_occurrence_domain_is_reflected.
  - exact checked_closed_native_event_and_endpoint_tuples_are_reflected.
  - exact checked_closed_native_acceptance_inputs_remain_visible.
Qed.
