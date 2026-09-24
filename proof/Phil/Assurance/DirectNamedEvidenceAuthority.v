From Stdlib Require Import Bool.Bool Arith.PeanoNat.
From Phil.Assurance Require Import EvidenceFactAuthority.

(*
  Defensive proof-correspondence continuation of D-CERT-SUPPORT-01.

  EvidenceFactAuthorityPreserved covers EvidenceFact references actually used by
  checked decision certificates.  A StaticByEvidence disposition is different:
  it selects a named proof directly and can therefore have no certificate-used
  EvidenceFact at all.  Certificate-fact authority may consequently hold
  vacuously while the direct named proof is mapped to an immutable record with
  the wrong proposition, semantic subject, or scope.

  This bounded model gives direct named evidence its own authority relation.
  Every selected direct name must resolve to one immutable evidence record that
  preserves the authoritative proposition, subjects, and scope, and that exact
  immutable record must be the one used by the final consumer.

  Concrete Haskell Name lookup, construction of the authoritative direct-proof
  registry, immutable EvidenceEntryId/RevisionId identities, source admission,
  and mandatory final-consumer use remain implementation-correspondence
  premises.  This proof does not grant truth to arbitrary supplied evidence,
  reject valid in-scope named proofs, restore consumed resources, or change any
  Phase 1 trusted-computing-base boundary.
*)

Definition DirectEvidenceName := nat.

Record DirectNamedEvidenceAuthorityModel : Type :=
  mkDirectNamedEvidenceAuthorityModel {
    directCertificateAuthority : EvidenceFactAuthorityModel;
    modelDirectSelected : DirectEvidenceName -> bool;
    modelDirectAuthoritativeProposition :
      DirectEvidenceName -> option PropositionIdentity;
    modelDirectAuthoritativeSubjects :
      DirectEvidenceName -> option SubjectIdentity;
    modelDirectAuthoritativeScope :
      DirectEvidenceName -> option ScopeIdentity;
    modelDirectMappedEvidence :
      DirectEvidenceName -> option ImmutableEvidenceId;
    modelDirectEvidenceProposition :
      ImmutableEvidenceId -> option PropositionIdentity;
    modelDirectEvidenceSubjects :
      ImmutableEvidenceId -> option SubjectIdentity;
    modelDirectEvidenceScope :
      ImmutableEvidenceId -> option ScopeIdentity;
    modelDirectFinalConsumerUses :
      ImmutableEvidenceId -> bool
  }.

Definition DirectNamedEvidenceAuthorityPreserved
  (model : DirectNamedEvidenceAuthorityModel) : Prop :=
  forall evidenceName,
    modelDirectSelected model evidenceName = true ->
    exists evidence proposition subjects scope,
      modelDirectAuthoritativeProposition model evidenceName = Some proposition /\
      modelDirectAuthoritativeSubjects model evidenceName = Some subjects /\
      modelDirectAuthoritativeScope model evidenceName = Some scope /\
      modelDirectMappedEvidence model evidenceName = Some evidence /\
      modelDirectEvidenceProposition model evidence = Some proposition /\
      modelDirectEvidenceSubjects model evidence = Some subjects /\
      modelDirectEvidenceScope model evidence = Some scope /\
      modelDirectFinalConsumerUses model evidence = true.

Definition DirectMappedConsumerOnly
  (model : DirectNamedEvidenceAuthorityModel) : Prop :=
  forall evidenceName,
    modelDirectSelected model evidenceName = true ->
    exists evidence,
      modelDirectMappedEvidence model evidenceName = Some evidence /\
      modelDirectFinalConsumerUses model evidence = true.

Theorem selected_direct_evidence_requires_authoritative_immutable_support :
  forall model evidenceName,
    DirectNamedEvidenceAuthorityPreserved model ->
    modelDirectSelected model evidenceName = true ->
    exists evidence proposition subjects scope,
      modelDirectAuthoritativeProposition model evidenceName = Some proposition /\
      modelDirectAuthoritativeSubjects model evidenceName = Some subjects /\
      modelDirectAuthoritativeScope model evidenceName = Some scope /\
      modelDirectMappedEvidence model evidenceName = Some evidence /\
      modelDirectEvidenceProposition model evidence = Some proposition /\
      modelDirectEvidenceSubjects model evidence = Some subjects /\
      modelDirectEvidenceScope model evidence = Some scope /\
      modelDirectFinalConsumerUses model evidence = true.
Proof.
  intros model evidenceName Hpreserved Hselected.
  eapply Hpreserved.
  exact Hselected.
Qed.

Definition vacuousCertificateAuthority : EvidenceFactAuthorityModel :=
  mkEvidenceFactAuthorityModel
    (fun _ => None)
    (fun _ => None)
    (fun _ => None)
    (fun _ => None)
    (fun _ => None)
    (fun _ => None)
    (fun _ => None)
    (fun _ => false)
    (fun _ => false).

Theorem vacuous_certificate_fact_authority_is_preserved :
  EvidenceFactAuthorityPreserved vacuousCertificateAuthority.
Proof.
  intros fact Hused.
  cbn in Hused.
  discriminate Hused.
Qed.

Definition mismatchedDirectNamedWitness : DirectNamedEvidenceAuthorityModel :=
  mkDirectNamedEvidenceAuthorityModel
    vacuousCertificateAuthority
    (fun evidenceName => Nat.eqb evidenceName 1)
    (fun evidenceName => if Nat.eqb evidenceName 1 then Some 100 else None)
    (fun evidenceName => if Nat.eqb evidenceName 1 then Some 200 else None)
    (fun evidenceName => if Nat.eqb evidenceName 1 then Some 300 else None)
    (fun evidenceName => if Nat.eqb evidenceName 1 then Some 10 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 100 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 200 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 301 else None)
    (fun evidence => Nat.eqb evidence 10).

Theorem mismatched_direct_named_evidence_reaches_a_consumer :
  DirectMappedConsumerOnly mismatchedDirectNamedWitness.
Proof.
  intros evidenceName Hselected.
  cbn in Hselected.
  apply Nat.eqb_eq in Hselected.
  subst evidenceName.
  exists 10.
  split; reflexivity.
Qed.

Theorem mismatched_direct_named_evidence_lacks_authority :
  ~ DirectNamedEvidenceAuthorityPreserved mismatchedDirectNamedWitness.
Proof.
  intro Hpreserved.
  pose proof (Hpreserved 1 eq_refl) as Hselected.
  destruct Hselected as
    [evidence [proposition [subjects [scope
      [Hproposition
      [Hsubjects
      [Hscope
      [Hmapped
      [HevidenceProposition
      [HevidenceSubjects
      [HevidenceScope Hconsumer]]]]]]]]]]].
  cbn in Hscope, Hmapped.
  inversion Hscope; subst scope.
  inversion Hmapped; subst evidence.
  cbn in HevidenceScope.
  discriminate.
Qed.

Theorem certificate_fact_authority_does_not_cover_direct_named_evidence :
  EvidenceFactAuthorityPreserved
    (directCertificateAuthority mismatchedDirectNamedWitness) /\
  ~ DirectNamedEvidenceAuthorityPreserved mismatchedDirectNamedWitness.
Proof.
  split.
  - exact vacuous_certificate_fact_authority_is_preserved.
  - exact mismatched_direct_named_evidence_lacks_authority.
Qed.

Definition exactDirectNamedWitness : DirectNamedEvidenceAuthorityModel :=
  mkDirectNamedEvidenceAuthorityModel
    vacuousCertificateAuthority
    (fun evidenceName => Nat.eqb evidenceName 1)
    (fun evidenceName => if Nat.eqb evidenceName 1 then Some 100 else None)
    (fun evidenceName => if Nat.eqb evidenceName 1 then Some 200 else None)
    (fun evidenceName => if Nat.eqb evidenceName 1 then Some 300 else None)
    (fun evidenceName => if Nat.eqb evidenceName 1 then Some 10 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 100 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 200 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 300 else None)
    (fun evidence => Nat.eqb evidence 10).

Theorem exact_direct_named_evidence_preserves_authority :
  DirectNamedEvidenceAuthorityPreserved exactDirectNamedWitness.
Proof.
  intros evidenceName Hselected.
  cbn in Hselected.
  apply Nat.eqb_eq in Hselected.
  subst evidenceName.
  exists 10, 100, 200, 300.
  repeat split; reflexivity.
Qed.

Theorem exact_direct_named_evidence_reaches_the_final_consumer :
  DirectMappedConsumerOnly exactDirectNamedWitness.
Proof.
  intros evidenceName Hselected.
  pose proof
    (selected_direct_evidence_requires_authoritative_immutable_support
      exactDirectNamedWitness evidenceName
      exact_direct_named_evidence_preserves_authority
      Hselected)
    as Hauthority.
  destruct Hauthority as
    [evidence [proposition [subjects [scope
      [Hproposition
      [Hsubjects
      [Hscope
      [Hmapped
      [HevidenceProposition
      [HevidenceSubjects
      [HevidenceScope Hconsumer]]]]]]]]]]].
  exists evidence.
  split.
  - exact Hmapped.
  - exact Hconsumer.
Qed.
