From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import ProviderQualificationImplementationBridge.

(*
  PHIL-PROV-QUAL-IMPL-001 — extracted nested provider qualification traversal.

  The kernel owns finite operation-domain correspondence, implementation-entry
  lookup, implementation-outcome-domain correspondence, mapped public-outcome
  lookup, and exact residue comparison. Per-operation callable/precondition
  acceptance is supplied as one bounded predicate so production can compose this
  traversal with the already Implementation Refined CALL-012 decision.
*)

Definition ContractOperationProjection
  (ContractOperation OutcomeKey Residue : Type) : Type :=
  (ContractOperation * list (OutcomeKey * Residue))%type.

Definition ImplementationOperationProjection
  (ImplementationOperation OutcomeKey Residue : Type) : Type :=
  (ImplementationOperation * list (OutcomeKey * Residue))%type.

Definition CorrespondenceProjection
  (EntryKey OutcomeKey : Type) : Type :=
  (EntryKey * list (OutcomeKey * OutcomeKey))%type.

Definition decideOutcomeMapping
  {OutcomeKey Residue : Type}
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (residueEqual : Residue -> Residue -> bool)
  (contractOutcomes : list (OutcomeKey * Residue))
  (implementationOutcomes : list (OutcomeKey * Residue))
  (mapping : OutcomeKey * OutcomeKey) : bool :=
  let implementationOutcome := fst mapping in
  let contractOutcome := snd mapping in
  match lookupAssoc eqOutcome implementationOutcome implementationOutcomes,
        lookupAssoc eqOutcome contractOutcome contractOutcomes with
  | Some implementationResidue, Some contractResidue =>
      residueEqual implementationResidue contractResidue
  | _, _ => false
  end.

Definition decideOutcomeTraversal
  {OutcomeKey Residue : Type}
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (residueEqual : Residue -> Residue -> bool)
  (contractOutcomes : list (OutcomeKey * Residue))
  (implementationOutcomes : list (OutcomeKey * Residue))
  (outcomeMappings : list (OutcomeKey * OutcomeKey)) : bool :=
  sameKeyDomainb eqOutcome implementationOutcomes outcomeMappings &&
  allFiniteb
    (decideOutcomeMapping
      eqOutcome residueEqual contractOutcomes implementationOutcomes)
    outcomeMappings.

Definition OutcomeTraversalAccepts
  {OutcomeKey Residue : Type}
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (residueEqual : Residue -> Residue -> bool)
  (contractOutcomes : list (OutcomeKey * Residue))
  (implementationOutcomes : list (OutcomeKey * Residue))
  (outcomeMappings : list (OutcomeKey * OutcomeKey)) : Prop :=
  sameKeyDomainb eqOutcome implementationOutcomes outcomeMappings = true /\
  Forall
    (fun mapping =>
      decideOutcomeMapping
        eqOutcome residueEqual contractOutcomes implementationOutcomes mapping = true)
    outcomeMappings.

Theorem decide_outcome_traversal_true_iff :
  forall (OutcomeKey Residue : Type)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (residueEqual : Residue -> Residue -> bool)
      (contractOutcomes : list (OutcomeKey * Residue))
      (implementationOutcomes : list (OutcomeKey * Residue))
      (outcomeMappings : list (OutcomeKey * OutcomeKey)),
    decideOutcomeTraversal
      eqOutcome residueEqual contractOutcomes implementationOutcomes outcomeMappings = true <->
    OutcomeTraversalAccepts
      eqOutcome residueEqual contractOutcomes implementationOutcomes outcomeMappings.
Proof.
  intros OutcomeKey Residue eqOutcome residueEqual
    contractOutcomes implementationOutcomes outcomeMappings.
  unfold decideOutcomeTraversal, OutcomeTraversalAccepts.
  rewrite andb_true_iff, all_finiteb_true_iff.
  reflexivity.
Qed.

Definition decideOperationTraversal
  {EntryKey OutcomeKey ContractOperation ImplementationOperation Residue : Type}
  (eqEntry : EntryKey -> EntryKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (residueEqual : Residue -> Residue -> bool)
  (operationAccepts : ContractOperation -> ImplementationOperation -> bool)
  (implementationEntries
    : list (EntryKey * ImplementationOperationProjection
      ImplementationOperation OutcomeKey Residue))
  (contractProjection
    : ContractOperationProjection ContractOperation OutcomeKey Residue)
  (correspondence : CorrespondenceProjection EntryKey OutcomeKey) : bool :=
  match lookupAssoc eqEntry (fst correspondence) implementationEntries with
  | None => false
  | Some implementationProjection =>
      operationAccepts (fst contractProjection) (fst implementationProjection) &&
      decideOutcomeTraversal
        eqOutcome
        residueEqual
        (snd contractProjection)
        (snd implementationProjection)
        (snd correspondence)
  end.

Definition OperationTraversalAccepts
  {EntryKey OutcomeKey ContractOperation ImplementationOperation Residue : Type}
  (eqEntry : EntryKey -> EntryKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (residueEqual : Residue -> Residue -> bool)
  (operationAccepts : ContractOperation -> ImplementationOperation -> bool)
  (implementationEntries
    : list (EntryKey * ImplementationOperationProjection
      ImplementationOperation OutcomeKey Residue))
  (contractProjection
    : ContractOperationProjection ContractOperation OutcomeKey Residue)
  (correspondence : CorrespondenceProjection EntryKey OutcomeKey) : Prop :=
  match lookupAssoc eqEntry (fst correspondence) implementationEntries with
  | None => False
  | Some implementationProjection =>
      operationAccepts (fst contractProjection) (fst implementationProjection) = true /\
      OutcomeTraversalAccepts
        eqOutcome
        residueEqual
        (snd contractProjection)
        (snd implementationProjection)
        (snd correspondence)
  end.

Theorem decide_operation_traversal_true_iff :
  forall (EntryKey OutcomeKey ContractOperation ImplementationOperation Residue : Type)
      (eqEntry : EntryKey -> EntryKey -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (residueEqual : Residue -> Residue -> bool)
      (operationAccepts : ContractOperation -> ImplementationOperation -> bool)
      (implementationEntries
        : list (EntryKey * ImplementationOperationProjection
          ImplementationOperation OutcomeKey Residue))
      (contractProjection
        : ContractOperationProjection ContractOperation OutcomeKey Residue)
      (correspondence : CorrespondenceProjection EntryKey OutcomeKey),
    decideOperationTraversal
      eqEntry eqOutcome residueEqual operationAccepts
      implementationEntries contractProjection correspondence = true <->
    OperationTraversalAccepts
      eqEntry eqOutcome residueEqual operationAccepts
      implementationEntries contractProjection correspondence.
Proof.
  intros EntryKey OutcomeKey ContractOperation ImplementationOperation Residue
    eqEntry eqOutcome residueEqual operationAccepts
    implementationEntries contractProjection correspondence.
  unfold decideOperationTraversal, OperationTraversalAccepts.
  destruct (lookupAssoc eqEntry (fst correspondence) implementationEntries)
    as [implementationProjection|] eqn:Hlookup.
  - rewrite andb_true_iff, decide_outcome_traversal_true_iff.
    reflexivity.
  - cbn. tauto.
Qed.

Definition decideOperationAt
  {OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqEntry : EntryKey -> EntryKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (residueEqual : Residue -> Residue -> bool)
  (operationAccepts : ContractOperation -> ImplementationOperation -> bool)
  (correspondences
    : list (OperationKey * CorrespondenceProjection EntryKey OutcomeKey))
  (implementationEntries
    : list (EntryKey * ImplementationOperationProjection
      ImplementationOperation OutcomeKey Residue))
  (operation
    : OperationKey * ContractOperationProjection ContractOperation OutcomeKey Residue)
  : bool :=
  match lookupAssoc eqOperation (fst operation) correspondences with
  | None => false
  | Some correspondence =>
      decideOperationTraversal
        eqEntry eqOutcome residueEqual operationAccepts
        implementationEntries (snd operation) correspondence
  end.

Definition OperationAtAccepts
  {OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqEntry : EntryKey -> EntryKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (residueEqual : Residue -> Residue -> bool)
  (operationAccepts : ContractOperation -> ImplementationOperation -> bool)
  (correspondences
    : list (OperationKey * CorrespondenceProjection EntryKey OutcomeKey))
  (implementationEntries
    : list (EntryKey * ImplementationOperationProjection
      ImplementationOperation OutcomeKey Residue))
  (operation
    : OperationKey * ContractOperationProjection ContractOperation OutcomeKey Residue)
  : Prop :=
  match lookupAssoc eqOperation (fst operation) correspondences with
  | None => False
  | Some correspondence =>
      OperationTraversalAccepts
        eqEntry eqOutcome residueEqual operationAccepts
        implementationEntries (snd operation) correspondence
  end.

Theorem decide_operation_at_true_iff :
  forall (OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue : Type)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqEntry : EntryKey -> EntryKey -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (residueEqual : Residue -> Residue -> bool)
      (operationAccepts : ContractOperation -> ImplementationOperation -> bool)
      (correspondences
        : list (OperationKey * CorrespondenceProjection EntryKey OutcomeKey))
      (implementationEntries
        : list (EntryKey * ImplementationOperationProjection
          ImplementationOperation OutcomeKey Residue))
      (operation
        : OperationKey * ContractOperationProjection ContractOperation OutcomeKey Residue),
    decideOperationAt
      eqOperation eqEntry eqOutcome residueEqual operationAccepts
      correspondences implementationEntries operation = true <->
    OperationAtAccepts
      eqOperation eqEntry eqOutcome residueEqual operationAccepts
      correspondences implementationEntries operation.
Proof.
  intros OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue
    eqOperation eqEntry eqOutcome residueEqual operationAccepts
    correspondences implementationEntries operation.
  unfold decideOperationAt, OperationAtAccepts.
  destruct (lookupAssoc eqOperation (fst operation) correspondences)
    as [correspondence|] eqn:Hlookup.
  - apply decide_operation_traversal_true_iff.
  - cbn. tauto.
Qed.

Lemma all_operation_at_true_iff :
  forall (OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue : Type)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqEntry : EntryKey -> EntryKey -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (residueEqual : Residue -> Residue -> bool)
      (operationAccepts : ContractOperation -> ImplementationOperation -> bool)
      (correspondences
        : list (OperationKey * CorrespondenceProjection EntryKey OutcomeKey))
      (implementationEntries
        : list (EntryKey * ImplementationOperationProjection
          ImplementationOperation OutcomeKey Residue))
      (contractOperations
        : list (OperationKey * ContractOperationProjection
          ContractOperation OutcomeKey Residue)),
    allFiniteb
      (decideOperationAt
        eqOperation eqEntry eqOutcome residueEqual operationAccepts
        correspondences implementationEntries)
      contractOperations = true <->
    Forall
      (OperationAtAccepts
        eqOperation eqEntry eqOutcome residueEqual operationAccepts
        correspondences implementationEntries)
      contractOperations.
Proof.
  intros OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue
    eqOperation eqEntry eqOutcome residueEqual operationAccepts
    correspondences implementationEntries contractOperations.
  rewrite all_finiteb_true_iff.
  induction contractOperations as [| operation rest IH].
  - split; intro H; constructor.
  - split; intro H.
    + inversion H as [| operation' rest' Hoperation Hrest]; subst.
      constructor.
      * apply (proj1
          (decide_operation_at_true_iff
            OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue
            eqOperation eqEntry eqOutcome residueEqual operationAccepts
            correspondences implementationEntries operation)).
        exact Hoperation.
      * apply (proj1 IH). exact Hrest.
    + inversion H as [| operation' rest' Hoperation Hrest]; subst.
      constructor.
      * apply (proj2
          (decide_operation_at_true_iff
            OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue
            eqOperation eqEntry eqOutcome residueEqual operationAccepts
            correspondences implementationEntries operation)).
        exact Hoperation.
      * apply (proj2 IH). exact Hrest.
Qed.

Definition decideProviderQualification
  {OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqEntry : EntryKey -> EntryKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (residueEqual : Residue -> Residue -> bool)
  (operationAccepts : ContractOperation -> ImplementationOperation -> bool)
  (contractRevisionMatches : bool)
  (implementationRevisionMatches : bool)
  (contractOperations
    : list (OperationKey * ContractOperationProjection ContractOperation OutcomeKey Residue))
  (correspondences
    : list (OperationKey * CorrespondenceProjection EntryKey OutcomeKey))
  (implementationEntries
    : list (EntryKey * ImplementationOperationProjection
      ImplementationOperation OutcomeKey Residue)) : bool :=
  contractRevisionMatches &&
  (implementationRevisionMatches &&
    (sameKeyDomainb eqOperation contractOperations correspondences &&
      allFiniteb
        (decideOperationAt
          eqOperation eqEntry eqOutcome residueEqual operationAccepts
          correspondences implementationEntries)
        contractOperations)).

Definition ProviderTraversalAccepts
  {OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqEntry : EntryKey -> EntryKey -> bool)
  (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
  (residueEqual : Residue -> Residue -> bool)
  (operationAccepts : ContractOperation -> ImplementationOperation -> bool)
  (contractRevisionMatches : bool)
  (implementationRevisionMatches : bool)
  (contractOperations
    : list (OperationKey * ContractOperationProjection ContractOperation OutcomeKey Residue))
  (correspondences
    : list (OperationKey * CorrespondenceProjection EntryKey OutcomeKey))
  (implementationEntries
    : list (EntryKey * ImplementationOperationProjection
      ImplementationOperation OutcomeKey Residue)) : Prop :=
  contractRevisionMatches = true /\
  implementationRevisionMatches = true /\
  sameKeyDomainb eqOperation contractOperations correspondences = true /\
  Forall
    (OperationAtAccepts
      eqOperation eqEntry eqOutcome residueEqual operationAccepts
      correspondences implementationEntries)
    contractOperations.

Theorem decide_provider_qualification_true_iff :
  forall (OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue : Type)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqEntry : EntryKey -> EntryKey -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (residueEqual : Residue -> Residue -> bool)
      (operationAccepts : ContractOperation -> ImplementationOperation -> bool)
      (contractRevisionMatches implementationRevisionMatches : bool)
      (contractOperations
        : list (OperationKey * ContractOperationProjection
          ContractOperation OutcomeKey Residue))
      (correspondences
        : list (OperationKey * CorrespondenceProjection EntryKey OutcomeKey))
      (implementationEntries
        : list (EntryKey * ImplementationOperationProjection
          ImplementationOperation OutcomeKey Residue)),
    decideProviderQualification
      eqOperation eqEntry eqOutcome residueEqual operationAccepts
      contractRevisionMatches implementationRevisionMatches
      contractOperations correspondences implementationEntries = true <->
    ProviderTraversalAccepts
      eqOperation eqEntry eqOutcome residueEqual operationAccepts
      contractRevisionMatches implementationRevisionMatches
      contractOperations correspondences implementationEntries.
Proof.
  intros OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue
    eqOperation eqEntry eqOutcome residueEqual operationAccepts
    contractRevisionMatches implementationRevisionMatches
    contractOperations correspondences implementationEntries.
  unfold decideProviderQualification, ProviderTraversalAccepts.
  repeat rewrite andb_true_iff.
  rewrite all_operation_at_true_iff.
  tauto.
Qed.

Theorem accepted_provider_traversal_has_exact_operation_keys :
  forall (OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue : Type)
      (eqOperation : OperationKey -> OperationKey -> bool)
      (eqEntry : EntryKey -> EntryKey -> bool)
      (eqOutcome : OutcomeKey -> OutcomeKey -> bool)
      (residueEqual : Residue -> Residue -> bool)
      (operationAccepts : ContractOperation -> ImplementationOperation -> bool),
    (forall first second : OperationKey,
      eqOperation first second = true <-> first = second) ->
    forall (contractRevisionMatches implementationRevisionMatches : bool)
      (contractOperations
        : list (OperationKey * ContractOperationProjection
          ContractOperation OutcomeKey Residue))
      (correspondences
        : list (OperationKey * CorrespondenceProjection EntryKey OutcomeKey))
      (implementationEntries
        : list (EntryKey * ImplementationOperationProjection
          ImplementationOperation OutcomeKey Residue)),
      decideProviderQualification
        eqOperation eqEntry eqOutcome residueEqual operationAccepts
        contractRevisionMatches implementationRevisionMatches
        contractOperations correspondences implementationEntries = true ->
      keysOf contractOperations = keysOf correspondences.
Proof.
  intros OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue
    eqOperation eqEntry eqOutcome residueEqual operationAccepts Heq
    contractRevisionMatches implementationRevisionMatches
    contractOperations correspondences implementationEntries Hdecision.
  apply (proj1
    (decide_provider_qualification_true_iff
      OperationKey EntryKey OutcomeKey ContractOperation ImplementationOperation Residue
      eqOperation eqEntry eqOutcome residueEqual operationAccepts
      contractRevisionMatches implementationRevisionMatches
      contractOperations correspondences implementationEntries)) in Hdecision.
  destruct Hdecision as [_ [_ [Hdomain _]]].
  apply (proj1
    (same_key_domainb_true_iff_keys_equal
      OperationKey
      (ContractOperationProjection ContractOperation OutcomeKey Residue)
      (CorrespondenceProjection EntryKey OutcomeKey)
      eqOperation Heq contractOperations correspondences)).
  exact Hdomain.
Qed.
