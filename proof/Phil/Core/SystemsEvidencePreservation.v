From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Assurance Require Import Manifest EvidenceUse.
From Phil.Core Require Import DataSubject BoundarySubject.

(*
  PHIL-SYS-EVID-001 — aggregate evidence, erasure, and assumption preservation
  for the bounded SYS-011--013 Systems chain.

  The proof deliberately composes already-Certified authority rather than
  restating it:

  - PHIL-BND-SUBJECT-001 supplies exact subject-transfer authority over the
    Certified PHIL-DATA-SUBJECT-001 transport semantics;
  - PHIL-ASSURE-USE-001 supplies exact nonempty usable erasure authority; and
  - PHIL-ASSURE-ASSUME-001 supplies exact selected/permitted/in-scope
    assumption authority.

  Concrete Haskell Text/Map/Set/list representation, consumer enumeration,
  source-fact/subject correspondence construction, stage-revision hashing,
  exact diagnostics, and Haskell implementation equivalence remain explicit
  correspondence boundaries.
*)

(* -------------------------------------------------------------------------- *)
(* SYS-012 — evidence erasure after exact discharge and consumer closure.      *)
(* -------------------------------------------------------------------------- *)

Definition SystemsEvidenceConsumer := nat.

Inductive LaterConsumerBasis : Type :=
| LaterNeedsErasedRepresentation
| LaterUsesSuccessorInvariant : nat -> LaterConsumerBasis.

Record EvidenceErasureFacts : Type := mkEvidenceErasureFacts {
  erasureSourceFactBindsExactSubject : bool;
  erasureDischargeEvidenceBindsExactSubject : bool;
  erasureRepresentationRevision : nat;
  erasureLastSemanticUse : nat;
  erasureNoLaterConsumerBasisRevision : nat;
  erasureSuccessorInvariantRevision : option nat;
  erasureRuntimeResidueChangeRevision : option nat;
  erasureCostChangeRevision : option nat
}.

Definition OptionalRevisionWellFormed (revision : option nat) : Prop :=
  match revision with
  | None => True
  | Some value => value <> 0
  end.

Definition LaterConsumerSafe
  (facts : EvidenceErasureFacts)
  (basis : LaterConsumerBasis) : Prop :=
  match basis with
  | LaterNeedsErasedRepresentation => False
  | LaterUsesSuccessorInvariant actual =>
      match erasureSuccessorInvariantRevision facts with
      | None => False
      | Some expected => expected <> 0 /\ actual = expected
      end
  end.

Record EvidenceErasurePreserved
  (context : AssuranceUseContext)
  (revision : RevisionId)
  (selected : EvidenceSet)
  (facts : EvidenceErasureFacts)
  (laterConsumers : SystemsEvidenceConsumer -> option LaterConsumerBasis) : Prop :=
  mkEvidenceErasurePreserved {
    systemsErasureUseVerified :
      ErasureUseVerified context revision selected;
    systemsErasureSourceSubjectExact :
      erasureSourceFactBindsExactSubject facts = true;
    systemsErasureDischargeSubjectExact :
      erasureDischargeEvidenceBindsExactSubject facts = true;
    systemsErasureRepresentationPresent :
      erasureRepresentationRevision facts <> 0;
    systemsErasureLastUsePresent :
      erasureLastSemanticUse facts <> 0;
    systemsErasureConsumerClosureBasisPresent :
      erasureNoLaterConsumerBasisRevision facts <> 0;
    systemsErasureSuccessorRevisionWellFormed :
      OptionalRevisionWellFormed (erasureSuccessorInvariantRevision facts);
    systemsErasureRuntimeResidueRevisionWellFormed :
      OptionalRevisionWellFormed (erasureRuntimeResidueChangeRevision facts);
    systemsErasureCostRevisionWellFormed :
      OptionalRevisionWellFormed (erasureCostChangeRevision facts);
    systemsErasureLaterConsumersClosed :
      forall consumer basis,
        laterConsumers consumer = Some basis ->
        consumer <> erasureLastSemanticUse facts /\
        LaterConsumerSafe facts basis
  }.

Theorem evidence_erasure_requires_exact_usable_discharge :
  forall context revision selected facts laterConsumers,
    EvidenceErasurePreserved
      context revision selected facts laterConsumers ->
    erasureSourceFactBindsExactSubject facts = true /\
    erasureDischargeEvidenceBindsExactSubject facts = true /\
    exists evidence,
      selected evidence = true /\
      EvidenceExactUsableFor context revision evidence.
Proof.
  intros context revision selected facts laterConsumers Hpreserved.
  destruct Hpreserved as
    [Huse Hsource Hsubject Hrepresentation Hlast Hclosure
     Hsuccessor Hruntime Hcost Hconsumers].
  pose proof
    (verified_erasure_use_is_nonempty_and_exact
      context revision selected Huse)
    as Hexact.
  destruct Hexact as [Hscope [Haccepted [evidence [Hselected Husable]]]].
  split.
  - exact Hsource.
  - split.
    + exact Hsubject.
    + exists evidence.
      split; assumption.
Qed.

Theorem live_erased_representation_consumer_rejects :
  forall context revision selected facts laterConsumers consumer,
    laterConsumers consumer = Some LaterNeedsErasedRepresentation ->
    ~ EvidenceErasurePreserved
        context revision selected facts laterConsumers.
Proof.
  intros context revision selected facts laterConsumers consumer Hconsumer Hpreserved.
  destruct Hpreserved as
    [Huse Hsource Hsubject Hrepresentation Hlast Hclosure
     Hsuccessor Hruntime Hcost Hconsumers].
  specialize (Hconsumers consumer LaterNeedsErasedRepresentation Hconsumer).
  destruct Hconsumers as [HnotLast Hsafe].
  exact Hsafe.
Qed.

Theorem successor_invariant_consumer_is_exact :
  forall context revision selected facts laterConsumers consumer actual,
    EvidenceErasurePreserved
      context revision selected facts laterConsumers ->
    laterConsumers consumer = Some (LaterUsesSuccessorInvariant actual) ->
    exists expected,
      erasureSuccessorInvariantRevision facts = Some expected /\
      expected <> 0 /\
      actual = expected.
Proof.
  intros context revision selected facts laterConsumers consumer actual
    Hpreserved Hconsumer.
  destruct Hpreserved as
    [Huse Hsource Hsubject Hrepresentation Hlast Hclosure
     Hsuccessor Hruntime Hcost Hconsumers].
  specialize (Hconsumers consumer (LaterUsesSuccessorInvariant actual) Hconsumer).
  destruct Hconsumers as [HnotLast Hsafe].
  unfold LaterConsumerSafe in Hsafe.
  destruct (erasureSuccessorInvariantRevision facts) as [expected|] eqn:Hexpected.
  - destruct Hsafe as [Hpresent Hexact].
    exists expected.
    repeat split; assumption.
  - contradiction.
Qed.

Theorem last_semantic_use_cannot_reappear_as_later_consumer :
  forall context revision selected facts laterConsumers basis,
    laterConsumers (erasureLastSemanticUse facts) = Some basis ->
    ~ EvidenceErasurePreserved
        context revision selected facts laterConsumers.
Proof.
  intros context revision selected facts laterConsumers basis Hconsumer Hpreserved.
  destruct Hpreserved as
    [Huse Hsource Hsubject Hrepresentation Hlast Hclosure
     Hsuccessor Hruntime Hcost Hconsumers].
  specialize
    (Hconsumers (erasureLastSemanticUse facts) basis Hconsumer).
  destruct Hconsumers as [HnotLast Hsafe].
  apply HnotLast.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* SYS-013 — exact bidirectional assumption dependency and validity scope.     *)
(* -------------------------------------------------------------------------- *)

Definition SystemsAssumptionKey := nat.
Definition SystemsAssumptionScopeRevision := nat.

Inductive SystemsAssumptionConsumer : Type :=
| AssumptionFactConsumer : nat -> SystemsAssumptionConsumer
| AssumptionMechanismConsumer : nat -> SystemsAssumptionConsumer
| AssumptionErasureConsumer : nat -> SystemsAssumptionConsumer.

Record SystemsAssumptionBinding : Type := mkSystemsAssumptionBinding {
  systemsAssumptionAuthority : AssumptionAuthority;
  systemsAssumptionValidityScopeRevision : SystemsAssumptionScopeRevision
}.

Definition SystemsAssumptionRegistry :=
  SystemsAssumptionKey -> option SystemsAssumptionBinding.

Definition RequiredAssumptionDependency :=
  SystemsAssumptionConsumer -> SystemsAssumptionKey -> Prop.

Definition SystemsAssumptionForward :=
  SystemsAssumptionConsumer ->
  SystemsAssumptionKey ->
  option SystemsAssumptionScopeRevision.

Definition SystemsAssumptionReverse :=
  SystemsAssumptionKey -> SystemsAssumptionConsumer -> bool.

Record SystemsAssumptionDependenciesPreserved
  (required : RequiredAssumptionDependency)
  (registry : SystemsAssumptionRegistry)
  (forward : SystemsAssumptionForward)
  (reverse : SystemsAssumptionReverse) : Prop :=
  mkSystemsAssumptionDependenciesPreserved {
    systemsAssumptionRegistryExact :
      forall assumption,
        (exists consumer, required consumer assumption) <->
        (exists binding, registry assumption = Some binding);
    systemsAssumptionAuthorityAccepted :
      forall assumption binding,
        registry assumption = Some binding ->
        verifyAssumptionAuthority (systemsAssumptionAuthority binding) =
          GateAccepted;
    systemsAssumptionScopePresent :
      forall assumption binding,
        registry assumption = Some binding ->
        systemsAssumptionValidityScopeRevision binding <> 0;
    systemsAssumptionForwardExact :
      forall consumer assumption,
        required consumer assumption <->
        (exists scope, forward consumer assumption = Some scope);
    systemsAssumptionForwardScopeExact :
      forall consumer assumption scope,
        forward consumer assumption = Some scope ->
        exists binding,
          registry assumption = Some binding /\
          scope = systemsAssumptionValidityScopeRevision binding;
    systemsAssumptionReverseExact :
      forall consumer assumption,
        reverse assumption consumer = true <-> required consumer assumption
  }.

Theorem required_assumption_dependency_is_bidirectionally_preserved :
  forall required registry forward reverse consumer assumption,
    SystemsAssumptionDependenciesPreserved
      required registry forward reverse ->
    required consumer assumption ->
    exists binding scope,
      registry assumption = Some binding /\
      forward consumer assumption = Some scope /\
      scope = systemsAssumptionValidityScopeRevision binding /\
      scope <> 0 /\
      reverse assumption consumer = true.
Proof.
  intros required registry forward reverse consumer assumption Hpreserved Hrequired.
  destruct Hpreserved as
    [Hregistry Hauthority Hscope Hforward HforwardScope Hreverse].
  apply (proj1 (Hforward consumer assumption)) in Hrequired.
  destruct Hrequired as [scope HforwardLookup].
  pose proof
    (HforwardScope consumer assumption scope HforwardLookup)
    as Hbinding.
  destruct Hbinding as [binding [HregistryLookup HscopeExact]].
  pose proof (Hscope assumption binding HregistryLookup) as HscopePresent.
  exists binding, scope.
  split.
  - exact HregistryLookup.
  - split.
    + exact HforwardLookup.
    + split.
      * exact HscopeExact.
      * split.
        -- rewrite HscopeExact.
           exact HscopePresent.
        -- apply (proj2 (Hreverse consumer assumption)).
           apply (proj2 (Hforward consumer assumption)).
           exists scope.
           exact HforwardLookup.
Qed.

Theorem required_assumption_retains_certified_authority :
  forall required registry forward reverse consumer assumption,
    SystemsAssumptionDependenciesPreserved
      required registry forward reverse ->
    required consumer assumption ->
    exists binding,
      registry assumption = Some binding /\
      assumptionIdentityMatches (systemsAssumptionAuthority binding) = true /\
      assumptionDigestMatches (systemsAssumptionAuthority binding) = true /\
      assumptionSelectedByManifest (systemsAssumptionAuthority binding) = true /\
      assumptionPermittedByContext (systemsAssumptionAuthority binding) = true /\
      assumptionValidityMatches (systemsAssumptionAuthority binding) = true.
Proof.
  intros required registry forward reverse consumer assumption Hpreserved Hrequired.
  destruct Hpreserved as
    [Hregistry Hauthority Hscope Hforward HforwardScope Hreverse].
  assert (Hexists : exists candidate, required candidate assumption).
  {
    exists consumer.
    exact Hrequired.
  }
  apply (proj1 (Hregistry assumption)) in Hexists.
  destruct Hexists as [binding Hlookup].
  pose proof (Hauthority assumption binding Hlookup) as Haccepted.
  pose proof
    (successful_assumption_authority_is_exact
      (systemsAssumptionAuthority binding) Haccepted)
    as Hexact.
  destruct Hexact as [Hidentity [Hdigest [Hselected [Hpermitted Hvalidity]]]].
  exists binding.
  split.
  - exact Hlookup.
  - repeat split; assumption.
Qed.

Corollary fact_assumption_dependency_cannot_be_laundered :
  forall required registry forward reverse fact assumption,
    SystemsAssumptionDependenciesPreserved
      required registry forward reverse ->
    required (AssumptionFactConsumer fact) assumption ->
    exists binding scope,
      registry assumption = Some binding /\
      forward (AssumptionFactConsumer fact) assumption = Some scope /\
      scope = systemsAssumptionValidityScopeRevision binding /\
      scope <> 0 /\
      reverse assumption (AssumptionFactConsumer fact) = true.
Proof.
  intros required registry forward reverse fact assumption Hpreserved Hrequired.
  eapply required_assumption_dependency_is_bidirectionally_preserved;
    eassumption.
Qed.

Corollary mechanism_assumption_dependency_cannot_be_laundered :
  forall required registry forward reverse mechanism assumption,
    SystemsAssumptionDependenciesPreserved
      required registry forward reverse ->
    required (AssumptionMechanismConsumer mechanism) assumption ->
    exists binding scope,
      registry assumption = Some binding /\
      forward (AssumptionMechanismConsumer mechanism) assumption = Some scope /\
      scope = systemsAssumptionValidityScopeRevision binding /\
      scope <> 0 /\
      reverse assumption (AssumptionMechanismConsumer mechanism) = true.
Proof.
  intros required registry forward reverse mechanism assumption Hpreserved Hrequired.
  eapply required_assumption_dependency_is_bidirectionally_preserved;
    eassumption.
Qed.

Corollary erasure_assumption_dependency_cannot_be_laundered :
  forall required registry forward reverse erasure assumption,
    SystemsAssumptionDependenciesPreserved
      required registry forward reverse ->
    required (AssumptionErasureConsumer erasure) assumption ->
    exists binding scope,
      registry assumption = Some binding /\
      forward (AssumptionErasureConsumer erasure) assumption = Some scope /\
      scope = systemsAssumptionValidityScopeRevision binding /\
      scope <> 0 /\
      reverse assumption (AssumptionErasureConsumer erasure) = true.
Proof.
  intros required registry forward reverse erasure assumption Hpreserved Hrequired.
  eapply required_assumption_dependency_is_bidirectionally_preserved;
    eassumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* PHIL-SYS-EVID-001 — cumulative SYS-011--013 preservation.                  *)
(* -------------------------------------------------------------------------- *)

Record SystemsEvidencePreserved
  (update : DataSubjectUpdate)
  (evidence : SubjectBoundEvidence)
  (transfer : BoundarySubjectTransfer)
  (resultEvidence : option SubjectBoundEvidence)
  (context : AssuranceUseContext)
  (erasureRevision : RevisionId)
  (selectedErasureEvidence : EvidenceSet)
  (erasureFacts : EvidenceErasureFacts)
  (laterConsumers : SystemsEvidenceConsumer -> option LaterConsumerBasis)
  (required : RequiredAssumptionDependency)
  (registry : SystemsAssumptionRegistry)
  (forward : SystemsAssumptionForward)
  (reverse : SystemsAssumptionReverse) : Prop :=
  mkSystemsEvidencePreserved {
    systemsEvidenceSubjectUpdateChecked :
      CheckedDataSubjectUpdate
        update evidence (Some (boundaryDataTransport transfer)) resultEvidence;
    systemsEvidenceSubjectTransferAccepted :
      BoundarySubjectTransferAccepted evidence transfer;
    systemsEvidenceErasureAccepted :
      EvidenceErasurePreserved
        context erasureRevision selectedErasureEvidence
        erasureFacts laterConsumers;
    systemsEvidenceAssumptionDependenciesAccepted :
      SystemsAssumptionDependenciesPreserved
        required registry forward reverse
  }.

Theorem systems_evidence_preservation_is_cumulative :
  forall update evidence transfer resultEvidence
         context erasureRevision selectedErasureEvidence
         erasureFacts laterConsumers required registry forward reverse,
    SystemsEvidencePreserved
      update evidence transfer resultEvidence
      context erasureRevision selectedErasureEvidence
      erasureFacts laterConsumers required registry forward reverse ->
    TransportValid update evidence (boundaryDataTransport transfer) /\
    dataSubjectTransportKind (boundaryDataTransport transfer) =
      SubjectCopyTransport /\
    EvidenceErasurePreserved
      context erasureRevision selectedErasureEvidence
      erasureFacts laterConsumers /\
    SystemsAssumptionDependenciesPreserved
      required registry forward reverse.
Proof.
  intros update evidence transfer resultEvidence
    context erasureRevision selectedErasureEvidence
    erasureFacts laterConsumers required registry forward reverse Hpreserved.
  destruct Hpreserved as [Hupdate Htransfer Herasure Hassumptions].
  pose proof
    (checked_boundary_transfer_preserves_all_boundary_gates
      update evidence transfer resultEvidence Hupdate Htransfer)
    as Hboundary.
  destruct Hboundary as
    [Hvalid [Hkind [Hcopy [Hbytes [Hlaw [Hevidence Hscope]]]]]].
  split.
  - exact Hvalid.
  - split.
    + exact Hkind.
    + split; assumption.
Qed.

Corollary systems_evidence_runtime_coincidence_is_not_correspondence :
  forall evidence token,
    ~ BoundaryTransferCandidateAccepted
        evidence (RuntimeSubjectCoincidenceCandidate token).
Proof.
  exact runtime_subject_coincidence_never_authorizes_transfer.
Qed.
