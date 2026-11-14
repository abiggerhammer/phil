From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Assurance Require Import
  SystemsErasureConsumerDomainBoundary
  SystemsAssumptionAuthorityBoundary
  EvidenceConsumerFinalUseCorrespondence.

(*
  P9-A, issue #1771.  These are explicit adversarial MODEL fixtures,
  never evidence that native SYS-012/SYS-013 or the final Haskell event path
  has an authoritative producer.  The existing model projections are used
  unchanged.  In particular, no model bool becomes an accepting certificate.

  The distinction is: checking locally supplied entries, checking event
  metadata, and checking local assumption graph consistency do not imply
  domain completeness, a final consuming event, or immutable assumption
  authority respectively.
*)

Theorem p9_one_of_two_consumers_escapes_local_traversal :
  LocalSuppliedConsumerTraversalAccepted omittedConsumerWitness /\
  ~ AuthoritativeConsumerDomainPreserved omittedConsumerWitness.
Proof.
  split.
  - exact omitted_consumer_still_passes_local_supplied_traversal.
  - exact local_traversal_does_not_establish_authoritative_consumer_domain.
Qed.

Theorem p9_wrong_event_and_missing_final_use_both_fail :
  ~ CompleteEvidenceConsumerFinalUseCorrespondence wrongEventFinalUseWitness /\
  ~ SameEventFinalEvidenceUsePreserved omittedFinalUseWitness.
Proof.
  split.
  - intros [_ Hfinal].
    exact (wrong_event_final_use_lacks_same_event_preservation Hfinal).
  - exact omitted_final_use_lacks_same_event_preservation.
Qed.

(*
  A parameterized assumption mutation preserves required stage key 1,
  the locally coherent dependency registry and its scope 300.  Only the
  immutable authority's digest/subject/boundary/selection/permission/current
  facts change.  Every mutation still passes local SYS-013 correspondence.
*)
Definition p9AssumptionVariant
  (digestOK subjectOK boundaryOK selectedOK permittedOK currentOK : bool)
  : SystemsAssumptionAuthorityModel :=
  mkSystemsAssumptionAuthorityModel
    (modelRequiredAssumption exactAuthorityWitness)
    (modelStageScope exactAuthorityWitness)
    (modelLocalGraphCoherent exactAuthorityWitness)
    (modelAuthorityMap exactAuthorityWitness)
    (modelExpectedDigest exactAuthorityWitness)
    (modelExpectedSubject exactAuthorityWitness)
    (modelExpectedBoundary exactAuthorityWitness)
    (fun authority =>
      if Nat.eqb authority 10
      then Some (if digestOK then 100 else 101) else None)
    (fun authority =>
      if Nat.eqb authority 10
      then Some (if subjectOK then 200 else 201) else None)
    (modelAuthorityScope exactAuthorityWitness)
    (fun authority =>
      if Nat.eqb authority 10
      then Some (if boundaryOK then 400 else 401) else None)
    (fun authority => Nat.eqb authority 10 && selectedOK)
    (fun authority => Nat.eqb authority 10 && permittedOK)
    (fun authority => Nat.eqb authority 10 && currentOK).

Theorem p9_local_stage_accepts_every_single_field_mutation :
  forall digestOK subjectOK boundaryOK selectedOK permittedOK currentOK,
    LocalStageBindingCoherent
      (p9AssumptionVariant
        digestOK subjectOK boundaryOK selectedOK permittedOK currentOK).
Proof.
  intros digestOK subjectOK boundaryOK selectedOK permittedOK currentOK
    key Hrequired.
  cbn in Hrequired.
  apply Nat.eqb_eq in Hrequired.
  subst key.
  exists 10, 300.
  repeat split; try reflexivity.
  discriminate.
Qed.

(*
  Unpack an actual required key at the imported authority boundary.
  This proves each immutable-record obligation is necessary, rather than
  hoping generic congruence discovers the stage key / authority key links.
*)
Theorem p9_import_requires_every_authority_field :
  forall digestOK subjectOK boundaryOK selectedOK permittedOK currentOK,
    ImportedAssumptionAuthorityPreserved
      (p9AssumptionVariant
        digestOK subjectOK boundaryOK selectedOK permittedOK currentOK) ->
    digestOK = true /\
    subjectOK = true /\
    boundaryOK = true /\
    selectedOK = true /\
    permittedOK = true /\
    currentOK = true.
Proof.
  intros digestOK subjectOK boundaryOK selectedOK permittedOK currentOK
    Hauthority.
  pose proof (Hauthority 1 eq_refl) as Hrequired.
  destruct Hrequired as
    [authority [scope
      [Hmap [Hscope [Hpresent [Hlocal [Hdigest [Hsubject
      [HauthorityScope [Hboundary
      [Hselected [Hpermitted Hcurrent]]]]]]]]]]]].
  cbn in Hmap, Hscope.
  inversion Hmap; subst authority.
  inversion Hscope; subst scope.
  cbn in Hdigest, Hsubject, Hboundary, Hselected, Hpermitted, Hcurrent.
  repeat split.
  - destruct digestOK; [reflexivity | discriminate Hdigest].
  - destruct subjectOK; [reflexivity | discriminate Hsubject].
  - destruct boundaryOK; [reflexivity | discriminate Hboundary].
  - destruct selectedOK; [reflexivity | discriminate Hselected].
  - destruct permittedOK; [reflexivity | discriminate Hpermitted].
  - destruct currentOK; [reflexivity | discriminate Hcurrent].
Qed.

Theorem p9_bad_digest_cannot_be_imported :
  ~ ImportedAssumptionAuthorityPreserved
      (p9AssumptionVariant false true true true true true).
Proof.
  intro H.
  pose proof (p9_import_requires_every_authority_field
    false true true true true true H) as [Hd _].
  discriminate Hd.
Qed.

Theorem p9_bad_subject_cannot_be_imported :
  ~ ImportedAssumptionAuthorityPreserved
      (p9AssumptionVariant true false true true true true).
Proof.
  intro H.
  pose proof (p9_import_requires_every_authority_field
    true false true true true true H) as [_ [Hs _]].
  discriminate Hs.
Qed.

Theorem p9_bad_boundary_cannot_be_imported :
  ~ ImportedAssumptionAuthorityPreserved
      (p9AssumptionVariant true true false true true true).
Proof.
  intro H.
  pose proof (p9_import_requires_every_authority_field
    true true false true true true H) as [_ [_ [Hb _]]].
  discriminate Hb.
Qed.

Theorem p9_unselected_authority_cannot_be_imported :
  ~ ImportedAssumptionAuthorityPreserved
      (p9AssumptionVariant true true true false true true).
Proof.
  intro H.
  pose proof (p9_import_requires_every_authority_field
    true true true false true true H) as [_ [_ [_ [Hs _]]]].
  discriminate Hs.
Qed.

Theorem p9_unpermitted_authority_cannot_be_imported :
  ~ ImportedAssumptionAuthorityPreserved
      (p9AssumptionVariant true true true true false true).
Proof.
  intro H.
  pose proof (p9_import_requires_every_authority_field
    true true true true false true H) as [_ [_ [_ [_ [Hp _]]]]].
  discriminate Hp.
Qed.

Theorem p9_expired_authority_cannot_be_imported :
  ~ ImportedAssumptionAuthorityPreserved
      (p9AssumptionVariant true true true true true false).
Proof.
  intro H.
  pose proof (p9_import_requires_every_authority_field
    true true true true true false H) as [_ [_ [_ [_ [_ Hc]]]]].
  discriminate Hc.
Qed.

(* A local-consumer registry may refer to a key that has no selected
   immutable authority record.  Naming it in the required set is not
   authorization: the import must fail for key 2. *)
Definition p9UnmappedRequiredKey : SystemsAssumptionAuthorityModel :=
  mkSystemsAssumptionAuthorityModel
    (fun key => Nat.eqb key 1 || Nat.eqb key 2)
    (modelStageScope exactAuthorityWitness)
    (modelLocalGraphCoherent exactAuthorityWitness)
    (modelAuthorityMap exactAuthorityWitness)
    (modelExpectedDigest exactAuthorityWitness)
    (modelExpectedSubject exactAuthorityWitness)
    (modelExpectedBoundary exactAuthorityWitness)
    (modelAuthorityDigest exactAuthorityWitness)
    (modelAuthoritySubject exactAuthorityWitness)
    (modelAuthorityScope exactAuthorityWitness)
    (modelAuthorityBoundary exactAuthorityWitness)
    (modelAuthoritySelected exactAuthorityWitness)
    (modelAuthorityPermitted exactAuthorityWitness)
    (modelAuthorityCurrent exactAuthorityWitness).

Theorem p9_unmapped_required_key_cannot_be_imported :
  ~ ImportedAssumptionAuthorityPreserved p9UnmappedRequiredKey.
Proof.
  intro Hauthority.
  destruct (Hauthority 2 eq_refl)
    as [authority [scope [Hmap _]]].
  cbn in Hmap.
  discriminate.
Qed.

Theorem p9_existing_positive_models_stay_positive :
  AuthoritativeConsumerDomainPreserved exactConsumerDomainWitness /\
  CompleteEvidenceConsumerFinalUseCorrespondence
    checkedClosedSameEventFinalUseWitness /\
  CompleteEvidenceConsumerFinalUseCorrespondence
    stableSameEventFinalUseWitness /\
  ImportedAssumptionAuthorityPreserved exactAuthorityWitness.
Proof.
  split.
  - exact exact_consumer_domain_witness_is_authoritative.
  - split.
    + exact checked_closed_same_event_has_complete_final_correspondence.
    + split.
      * exact stable_same_event_has_complete_final_correspondence.
      * exact exact_authority_witness_preserves_required_stage_assumption.
Qed.

(* Kernel-checked exported witness statuses.  This prints dependency
   assumptions in hosted Rocq 9.2 CI, not native provenance claims. *)
Print Assumptions p9_one_of_two_consumers_escapes_local_traversal.
Print Assumptions p9_wrong_event_and_missing_final_use_both_fail.
Print Assumptions p9_local_stage_accepts_every_single_field_mutation.
Print Assumptions p9_bad_digest_cannot_be_imported.
Print Assumptions p9_bad_subject_cannot_be_imported.
Print Assumptions p9_bad_boundary_cannot_be_imported.
Print Assumptions p9_unselected_authority_cannot_be_imported.
Print Assumptions p9_unpermitted_authority_cannot_be_imported.
Print Assumptions p9_expired_authority_cannot_be_imported.
Print Assumptions p9_unmapped_required_key_cannot_be_imported.
Print Assumptions p9_existing_positive_models_stay_positive.
