From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  D-ERASURE-PREDECESSOR-BIND-01 — the native SYS-012 erasure record checks
  local source/discharge subject correspondence and later-consumer closure, but
  local coherence does not by itself reconstruct the accepted Assurance witness
  required by PHIL-ASSURE-USE-001.

  This bounded model keeps that imported authority explicit.  Each required
  erasure justification has a stage revision, an exact semantic subject, and a
  mapping to immutable evidence.  Imported authority additionally requires the
  mapped evidence to carry the same revision and subject and to be selected,
  certification-scoped, accepted, and usable.

  The model is deliberately per-erasure and proof-correspondence-only.  It does
  not replace the native consumer-domain checks, grant truth to caller-supplied
  evidence, or alter any Phase 1 trusted-computing-base boundary.
*)

Definition ErasureJustificationKey := nat.
Definition ImmutableEvidenceId := nat.
Definition RevisionIdentity := nat.
Definition SubjectIdentity := nat.

Record SystemsErasureAuthorityModel : Type :=
  mkSystemsErasureAuthorityModel {
    modelRequiredErasure : ErasureJustificationKey -> bool;
    modelLocalErasureCoherent : ErasureJustificationKey -> bool;
    modelStageRevision : ErasureJustificationKey -> option RevisionIdentity;
    modelExpectedSubject : ErasureJustificationKey -> SubjectIdentity;
    modelSourceSubject : ErasureJustificationKey -> option SubjectIdentity;
    modelDischargeSubject : ErasureJustificationKey -> option SubjectIdentity;
    modelAuthorityMap : ErasureJustificationKey -> option ImmutableEvidenceId;
    modelAuthorityRevision : ImmutableEvidenceId -> option RevisionIdentity;
    modelAuthoritySubject : ImmutableEvidenceId -> option SubjectIdentity;
    modelAuthoritySelected : ImmutableEvidenceId -> bool;
    modelAuthorityCertificationScoped : ImmutableEvidenceId -> bool;
    modelAuthorityRevisionAccepted : ImmutableEvidenceId -> bool;
    modelAuthorityUsable : ImmutableEvidenceId -> bool
  }.

Definition LocalErasureBindingCoherent
  (model : SystemsErasureAuthorityModel) : Prop :=
  forall key,
    modelRequiredErasure model key = true ->
    exists revision subject authority,
      modelStageRevision model key = Some revision /\
      revision <> 0 /\
      modelExpectedSubject model key = subject /\
      modelSourceSubject model key = Some subject /\
      modelDischargeSubject model key = Some subject /\
      modelAuthorityMap model key = Some authority /\
      modelLocalErasureCoherent model key = true.

Definition ImportedErasureAuthorityPreserved
  (model : SystemsErasureAuthorityModel) : Prop :=
  forall key,
    modelRequiredErasure model key = true ->
    exists revision subject authority,
      modelStageRevision model key = Some revision /\
      revision <> 0 /\
      modelExpectedSubject model key = subject /\
      modelSourceSubject model key = Some subject /\
      modelDischargeSubject model key = Some subject /\
      modelAuthorityMap model key = Some authority /\
      modelLocalErasureCoherent model key = true /\
      modelAuthorityRevision model authority = Some revision /\
      modelAuthoritySubject model authority = Some subject /\
      modelAuthoritySelected model authority = true /\
      modelAuthorityCertificationScoped model authority = true /\
      modelAuthorityRevisionAccepted model authority = true /\
      modelAuthorityUsable model authority = true.

Theorem imported_erasure_authority_implies_local_binding :
  forall model,
    ImportedErasureAuthorityPreserved model ->
    LocalErasureBindingCoherent model.
Proof.
  intros model Hauthority key Hrequired.
  pose proof (Hauthority key Hrequired) as Hbound.
  destruct Hbound as
    [revision [subject [authority
      [Hrevision
      [Hpresent
      [Hexpected
      [Hsource
      [Hdischarge
      [Hmap
      [Hlocal
      [HauthorityRevision
      [HauthoritySubject
      [Hselected
      [Hscope
      [Haccepted Husable]]]]]]]]]]]]]]].
  exists revision, subject, authority.
  repeat split; assumption.
Qed.

Definition mismatchedRevisionWitness : SystemsErasureAuthorityModel :=
  mkSystemsErasureAuthorityModel
    (fun key => Nat.eqb key 1)
    (fun key => Nat.eqb key 1)
    (fun key => if Nat.eqb key 1 then Some 300 else None)
    (fun key => if Nat.eqb key 1 then 200 else 0)
    (fun key => if Nat.eqb key 1 then Some 200 else None)
    (fun key => if Nat.eqb key 1 then Some 200 else None)
    (fun key => if Nat.eqb key 1 then Some 10 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 301 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 200 else None)
    (fun evidence => Nat.eqb evidence 10)
    (fun evidence => Nat.eqb evidence 10)
    (fun evidence => Nat.eqb evidence 10)
    (fun evidence => Nat.eqb evidence 10).

Theorem mismatched_revision_still_has_local_erasure_binding :
  LocalErasureBindingCoherent mismatchedRevisionWitness.
Proof.
  intros key Hrequired.
  cbn in Hrequired.
  apply Nat.eqb_eq in Hrequired.
  subst key.
  exists 300, 200, 10.
  repeat split; try reflexivity.
  discriminate.
Qed.

Theorem local_erasure_binding_does_not_establish_imported_authority :
  ~ ImportedErasureAuthorityPreserved mismatchedRevisionWitness.
Proof.
  intro Hauthority.
  pose proof (Hauthority 1 eq_refl) as Hbound.
  destruct Hbound as
    [revision [subject [authority
      [Hrevision
      [Hpresent
      [Hexpected
      [Hsource
      [Hdischarge
      [Hmap
      [Hlocal
      [HauthorityRevision
      [HauthoritySubject
      [Hselected
      [Hscope
      [Haccepted Husable]]]]]]]]]]]]]]].
  cbn in Hrevision, Hmap, HauthorityRevision.
  inversion Hrevision; subst revision.
  inversion Hmap; subst authority.
  cbn in HauthorityRevision.
  discriminate.
Qed.

Definition exactAuthorityWitness : SystemsErasureAuthorityModel :=
  mkSystemsErasureAuthorityModel
    (fun key => Nat.eqb key 1)
    (fun key => Nat.eqb key 1)
    (fun key => if Nat.eqb key 1 then Some 300 else None)
    (fun key => if Nat.eqb key 1 then 200 else 0)
    (fun key => if Nat.eqb key 1 then Some 200 else None)
    (fun key => if Nat.eqb key 1 then Some 200 else None)
    (fun key => if Nat.eqb key 1 then Some 10 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 300 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 200 else None)
    (fun evidence => Nat.eqb evidence 10)
    (fun evidence => Nat.eqb evidence 10)
    (fun evidence => Nat.eqb evidence 10)
    (fun evidence => Nat.eqb evidence 10).

Theorem exact_authority_witness_preserves_required_erasure :
  ImportedErasureAuthorityPreserved exactAuthorityWitness.
Proof.
  intros key Hrequired.
  cbn in Hrequired.
  apply Nat.eqb_eq in Hrequired.
  subst key.
  exists 300, 200, 10.
  repeat split; try reflexivity.
  discriminate.
Qed.

Theorem exact_authority_witness_retains_local_erasure_binding :
  LocalErasureBindingCoherent exactAuthorityWitness.
Proof.
  apply imported_erasure_authority_implies_local_binding.
  exact exact_authority_witness_preserves_required_erasure.
Qed.
