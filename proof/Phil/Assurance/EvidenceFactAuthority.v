From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  D-CERT-SUPPORT-01 — an EvidenceFact -> EvidenceEntryId map is not itself
  evidence authority.

  Native correspondence:

  - Phil.Core.Discharge.collectEvidenceAssumptions derives EvidenceFact
    references from the canonicalized unrestricted Core evidence registry.
  - Phil.Assurance.Handoff.handoffResolvedObligationWithEvidence translates a
    retained EvidenceFact (binding name, normalized fact index) through an
    assurance-owned EvidenceEntryId map and emits DependsOnEvidence.
  - Phil.Verification.ManifestClosure later requires the selected immutable
    evidence records and their dependencies at INT-002 closure.

  The remaining producer-authority boundary is stronger than successful map
  lookup: for every EvidenceFact actually used by a certificate, the mapped
  immutable evidence revision must preserve the authoritative fact's meaning.
  In this bounded model that meaning consists of proposition, semantic-subject
  identity, and scope identity.  Emitting the mapped dependency without those
  equalities is insufficient.

  Concrete Name/Int registry enumeration, proposition rendering, RevisionId /
  EvidenceEntryId lookup, and mandatory Haskell consumer use remain explicit
  implementation-correspondence boundaries.  This proof does not grant truth
  to arbitrary supplied evidence, restore consumed resources for lookup, or
  change any Phase 1 trusted-computing-base boundary.
*)

Definition FactRef := nat.
Definition PropositionIdentity := nat.
Definition SubjectIdentity := nat.
Definition ScopeIdentity := nat.
Definition ImmutableEvidenceId := nat.

Record EvidenceFactAuthorityModel : Type := mkEvidenceFactAuthorityModel {
  modelAuthoritativeProposition : FactRef -> option PropositionIdentity;
  modelAuthoritativeSubjects : FactRef -> option SubjectIdentity;
  modelAuthoritativeScope : FactRef -> option ScopeIdentity;
  modelMappedEvidence : FactRef -> option ImmutableEvidenceId;
  modelEvidenceProposition : ImmutableEvidenceId -> option PropositionIdentity;
  modelEvidenceSubjects : ImmutableEvidenceId -> option SubjectIdentity;
  modelEvidenceScope : ImmutableEvidenceId -> option ScopeIdentity;
  modelCertificateUsesFact : FactRef -> bool;
  modelEmittedEvidenceDependency : ImmutableEvidenceId -> bool
}.

Definition EvidenceFactAuthorityPreserved
  (model : EvidenceFactAuthorityModel) : Prop :=
  forall fact,
    modelCertificateUsesFact model fact = true ->
    exists evidence proposition subjects scope,
      modelAuthoritativeProposition model fact = Some proposition /\
      modelAuthoritativeSubjects model fact = Some subjects /\
      modelAuthoritativeScope model fact = Some scope /\
      modelMappedEvidence model fact = Some evidence /\
      modelEvidenceProposition model evidence = Some proposition /\
      modelEvidenceSubjects model evidence = Some subjects /\
      modelEvidenceScope model evidence = Some scope /\
      modelEmittedEvidenceDependency model evidence = true.

Definition MappedDependencyOnly
  (model : EvidenceFactAuthorityModel) : Prop :=
  forall fact,
    modelCertificateUsesFact model fact = true ->
    exists evidence,
      modelMappedEvidence model fact = Some evidence /\
      modelEmittedEvidenceDependency model evidence = true.

Theorem used_fact_requires_authoritative_immutable_support :
  forall model fact,
    EvidenceFactAuthorityPreserved model ->
    modelCertificateUsesFact model fact = true ->
    exists evidence proposition subjects scope,
      modelAuthoritativeProposition model fact = Some proposition /\
      modelAuthoritativeSubjects model fact = Some subjects /\
      modelAuthoritativeScope model fact = Some scope /\
      modelMappedEvidence model fact = Some evidence /\
      modelEvidenceProposition model evidence = Some proposition /\
      modelEvidenceSubjects model evidence = Some subjects /\
      modelEvidenceScope model evidence = Some scope /\
      modelEmittedEvidenceDependency model evidence = true.
Proof.
  intros model fact Hpreserved Hused.
  eapply Hpreserved.
  exact Hused.
Qed.

Definition mismatchedScopeWitness : EvidenceFactAuthorityModel :=
  mkEvidenceFactAuthorityModel
    (fun fact => if Nat.eqb fact 1 then Some 100 else None)
    (fun fact => if Nat.eqb fact 1 then Some 200 else None)
    (fun fact => if Nat.eqb fact 1 then Some 300 else None)
    (fun fact => if Nat.eqb fact 1 then Some 10 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 100 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 200 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 301 else None)
    (fun fact => Nat.eqb fact 1)
    (fun evidence => Nat.eqb evidence 10).

Theorem mismatched_scope_still_has_a_mapped_dependency :
  MappedDependencyOnly mismatchedScopeWitness.
Proof.
  intros fact Hused.
  cbn in Hused.
  apply Nat.eqb_eq in Hused.
  subst fact.
  exists 10.
  split; reflexivity.
Qed.

Theorem mapped_dependency_alone_does_not_establish_authority :
  ~ EvidenceFactAuthorityPreserved mismatchedScopeWitness.
Proof.
  intro Hpreserved.
  pose proof (Hpreserved 1 eq_refl) as Hused.
  destruct Hused as
    [evidence [proposition [subjects [scope
      [Hproposition
      [Hsubjects
      [Hscope
      [Hmapped
      [HevidenceProposition
      [HevidenceSubjects
      [HevidenceScope Hdependency]]]]]]]]]]].
  cbn in Hscope, Hmapped.
  inversion Hscope; subst scope.
  inversion Hmapped; subst evidence.
  cbn in HevidenceScope.
  discriminate.
Qed.

Definition exactAuthorityWitness : EvidenceFactAuthorityModel :=
  mkEvidenceFactAuthorityModel
    (fun fact => if Nat.eqb fact 1 then Some 100 else None)
    (fun fact => if Nat.eqb fact 1 then Some 200 else None)
    (fun fact => if Nat.eqb fact 1 then Some 300 else None)
    (fun fact => if Nat.eqb fact 1 then Some 10 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 100 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 200 else None)
    (fun evidence => if Nat.eqb evidence 10 then Some 300 else None)
    (fun fact => Nat.eqb fact 1)
    (fun evidence => Nat.eqb evidence 10).

Theorem exact_authority_witness_preserves_used_fact_support :
  EvidenceFactAuthorityPreserved exactAuthorityWitness.
Proof.
  intros fact Hused.
  cbn in Hused.
  apply Nat.eqb_eq in Hused.
  subst fact.
  exists 10, 100, 200, 300.
  repeat split; reflexivity.
Qed.

Theorem exact_authority_implies_a_mapped_dependency :
  MappedDependencyOnly exactAuthorityWitness.
Proof.
  intros fact Hused.
  pose proof
    (used_fact_requires_authoritative_immutable_support
      exactAuthorityWitness fact
      exact_authority_witness_preserves_used_fact_support
      Hused)
    as Hauthority.
  destruct Hauthority as
    [evidence [proposition [subjects [scope
      [Hproposition
      [Hsubjects
      [Hscope
      [Hmapped
      [HevidenceProposition
      [HevidenceSubjects
      [HevidenceScope Hdependency]]]]]]]]]]].
  exists evidence.
  split.
  - exact Hmapped.
  - exact Hdependency.
Qed.
