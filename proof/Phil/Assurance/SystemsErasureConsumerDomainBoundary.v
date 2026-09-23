From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  D-ERASURE-CONSUMER-DOMAIN-01 — SYS-012 validates every later consumer that
  appears in its supplied map, but traversal of that map does not establish
  that the map enumerates every relevant actual semantic consumer.

  This bounded proof-correspondence model makes the missing producer contract
  explicit.  A competent inventory producer must supply exactly the relevant
  later-consumer domain and preserve each consumer's source fact, semantic
  subject, erased representation, ordering coordinate and successor relation.
  The existing local closure decision is then applied to that authoritative
  domain.

  The model does not synthesize arbitrary optimized-IR consumers, add a Phase 2
  requirement, or change LLVM or any other Phase 1 trusted-computing-base
  boundary.
*)

Definition SemanticUseKey := nat.
Definition SourceFactIdentity := nat.
Definition SubjectIdentity := nat.
Definition RepresentationIdentity := nat.
Definition OrderingIdentity := nat.
Definition SuccessorIdentity := nat.

Record SystemsErasureConsumerDomainModel : Type :=
  mkSystemsErasureConsumerDomainModel {
    modelActualRelevantConsumer : SemanticUseKey -> bool;
    modelSuppliedConsumer : SemanticUseKey -> bool;
    modelActualSourceFact : SemanticUseKey -> option SourceFactIdentity;
    modelSuppliedSourceFact : SemanticUseKey -> option SourceFactIdentity;
    modelActualSubject : SemanticUseKey -> option SubjectIdentity;
    modelSuppliedSubject : SemanticUseKey -> option SubjectIdentity;
    modelActualRepresentation : SemanticUseKey -> option RepresentationIdentity;
    modelSuppliedRepresentation : SemanticUseKey -> option RepresentationIdentity;
    modelActualOrdering : SemanticUseKey -> option OrderingIdentity;
    modelSuppliedOrdering : SemanticUseKey -> option OrderingIdentity;
    modelActualSuccessor : SemanticUseKey -> option SuccessorIdentity;
    modelSuppliedSuccessor : SemanticUseKey -> option SuccessorIdentity;
    modelSuppliedClosureAccepted : SemanticUseKey -> bool
  }.

Definition ConsumerIdentityPreserved
  (model : SystemsErasureConsumerDomainModel)
  (key : SemanticUseKey) : Prop :=
  exists fact subject representation ordering,
    modelActualSourceFact model key = Some fact /\
    modelSuppliedSourceFact model key = Some fact /\
    modelActualSubject model key = Some subject /\
    modelSuppliedSubject model key = Some subject /\
    modelActualRepresentation model key = Some representation /\
    modelSuppliedRepresentation model key = Some representation /\
    modelActualOrdering model key = Some ordering /\
    ordering <> 0 /\
    modelSuppliedOrdering model key = Some ordering /\
    modelActualSuccessor model key = modelSuppliedSuccessor model key.

Definition LocalSuppliedConsumerTraversalAccepted
  (model : SystemsErasureConsumerDomainModel) : Prop :=
  forall key,
    modelSuppliedConsumer model key = true ->
    modelSuppliedClosureAccepted model key = true.

Definition AuthoritativeConsumerDomainPreserved
  (model : SystemsErasureConsumerDomainModel) : Prop :=
  (forall key,
    modelActualRelevantConsumer model key = true <->
    modelSuppliedConsumer model key = true) /\
  (forall key,
    modelActualRelevantConsumer model key = true ->
    ConsumerIdentityPreserved model key) /\
  (forall key,
    modelActualRelevantConsumer model key = true ->
    modelSuppliedClosureAccepted model key = true).

Theorem authoritative_consumer_domain_implies_local_traversal :
  forall model,
    AuthoritativeConsumerDomainPreserved model ->
    LocalSuppliedConsumerTraversalAccepted model.
Proof.
  intros model Hauthority key Hsupplied.
  destruct Hauthority as [Hdomain [_ Hclosure]].
  apply Hclosure.
  apply (proj2 (Hdomain key)).
  exact Hsupplied.
Qed.

Definition twoConsumerDomain (key : SemanticUseKey) : bool :=
  orb (Nat.eqb key 1) (Nat.eqb key 2).

Definition omittedConsumerWitness : SystemsErasureConsumerDomainModel :=
  mkSystemsErasureConsumerDomainModel
    twoConsumerDomain
    (fun key => Nat.eqb key 1)
    (fun key => if Nat.eqb key 1 then Some 101
                else if Nat.eqb key 2 then Some 102 else None)
    (fun key => if Nat.eqb key 1 then Some 101 else None)
    (fun key => if Nat.eqb key 1 then Some 201
                else if Nat.eqb key 2 then Some 202 else None)
    (fun key => if Nat.eqb key 1 then Some 201 else None)
    (fun key => if Nat.eqb key 1 then Some 301
                else if Nat.eqb key 2 then Some 302 else None)
    (fun key => if Nat.eqb key 1 then Some 301 else None)
    (fun key => if Nat.eqb key 1 then Some 401
                else if Nat.eqb key 2 then Some 402 else None)
    (fun key => if Nat.eqb key 1 then Some 401 else None)
    (fun key => if Nat.eqb key 1 then Some 501
                else if Nat.eqb key 2 then Some 502 else None)
    (fun key => if Nat.eqb key 1 then Some 501 else None)
    (fun key => Nat.eqb key 1).

Theorem omitted_consumer_still_passes_local_supplied_traversal :
  LocalSuppliedConsumerTraversalAccepted omittedConsumerWitness.
Proof.
  intros key Hsupplied.
  cbn in Hsupplied.
  apply Nat.eqb_eq in Hsupplied.
  subst key.
  reflexivity.
Qed.

Theorem local_traversal_does_not_establish_authoritative_consumer_domain :
  ~ AuthoritativeConsumerDomainPreserved omittedConsumerWitness.
Proof.
  intro Hauthority.
  destruct Hauthority as [Hdomain _].
  assert (Hactual :
    modelActualRelevantConsumer omittedConsumerWitness 2 = true) by reflexivity.
  pose proof (proj1 (Hdomain 2) Hactual) as Hsupplied.
  cbn in Hsupplied.
  discriminate.
Qed.

Definition exactConsumerDomainWitness : SystemsErasureConsumerDomainModel :=
  mkSystemsErasureConsumerDomainModel
    twoConsumerDomain
    twoConsumerDomain
    (fun key => if Nat.eqb key 1 then Some 101
                else if Nat.eqb key 2 then Some 102 else None)
    (fun key => if Nat.eqb key 1 then Some 101
                else if Nat.eqb key 2 then Some 102 else None)
    (fun key => if Nat.eqb key 1 then Some 201
                else if Nat.eqb key 2 then Some 202 else None)
    (fun key => if Nat.eqb key 1 then Some 201
                else if Nat.eqb key 2 then Some 202 else None)
    (fun key => if Nat.eqb key 1 then Some 301
                else if Nat.eqb key 2 then Some 302 else None)
    (fun key => if Nat.eqb key 1 then Some 301
                else if Nat.eqb key 2 then Some 302 else None)
    (fun key => if Nat.eqb key 1 then Some 401
                else if Nat.eqb key 2 then Some 402 else None)
    (fun key => if Nat.eqb key 1 then Some 401
                else if Nat.eqb key 2 then Some 402 else None)
    (fun key => if Nat.eqb key 1 then Some 501
                else if Nat.eqb key 2 then Some 502 else None)
    (fun key => if Nat.eqb key 1 then Some 501
                else if Nat.eqb key 2 then Some 502 else None)
    twoConsumerDomain.

Theorem exact_consumer_domain_witness_is_authoritative :
  AuthoritativeConsumerDomainPreserved exactConsumerDomainWitness.
Proof.
  split; [| split].
  - intro key.
    split; intro H; exact H.
  - intros key Hactual.
    unfold twoConsumerDomain in Hactual.
    destruct (Nat.eqb key 1) eqn:Hone.
    + apply Nat.eqb_eq in Hone.
      subst key.
      exists 101, 201, 301, 401.
      repeat split; try reflexivity.
      discriminate.
    + destruct (Nat.eqb key 2) eqn:Htwo.
      * apply Nat.eqb_eq in Htwo.
        subst key.
        exists 102, 202, 302, 402.
        repeat split; try reflexivity.
        discriminate.
      * cbn in Hactual.
        discriminate.
  - intros key Hactual.
    exact Hactual.
Qed.

Theorem exact_consumer_domain_witness_retains_local_traversal :
  LocalSuppliedConsumerTraversalAccepted exactConsumerDomainWitness.
Proof.
  apply authoritative_consumer_domain_implies_local_traversal.
  exact exact_consumer_domain_witness_is_authoritative.
Qed.
