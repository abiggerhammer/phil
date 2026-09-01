From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

From Phil.Core Require Import
  StorageRealization
  SystemsStageClosure
  ConcurrencyTerminal.

(*
  PHIL-MEM-CLOSURE-001 — semantic storage terminal closure is part of Phil
  safety; physical reclamation is a separate realization/profile obligation.

  This proof deliberately keeps those boundaries distinct:

  - explicit semantic storage resources must be released or have an exact
    permitted semantic terminal disposition before a process/root terminal fact
    may be certified;
  - the process/resource/loan/endpoint/obligation closure theorem remains the
    authority for ordinary terminal closure;
  - physical storage objects are realization facts only.  Reclamation or exact
    profile-authorized retention may be required for target certification, but a
    later physical leak cannot retroactively rewrite an already-established Phil
    semantic terminal fact.

  Concrete Text/Map/Set representation, the exact Haskell storage-owner table,
  and provider/profile truth remain correspondence boundaries.
*)

Definition StorageTerminalDispositionKey := nat.
Definition StorageProfileRevision := nat.

Inductive SemanticStorageOwnerState : Type :=
| SemanticStorageOwnerLive : SemanticStorageOwnerState
| SemanticStorageOwnerReleased : SemanticStorageOwnerState
| SemanticStorageOwnerTerminalDisposition :
    StorageTerminalDispositionKey -> SemanticStorageOwnerState.

Record SemanticStorageOwner : Type := mkSemanticStorageOwner {
  semanticStorageOwnerKey : SemanticStorageResourceKey;
  semanticStorageOwnerState : SemanticStorageOwnerState
}.

Definition PermittedStorageDisposition :=
  SemanticStorageResourceKey -> StorageTerminalDispositionKey -> Prop.

Definition SemanticStorageOwnerClosed
  (permitted : PermittedStorageDisposition)
  (owner : SemanticStorageOwner) : Prop :=
  match semanticStorageOwnerState owner with
  | SemanticStorageOwnerLive => False
  | SemanticStorageOwnerReleased => True
  | SemanticStorageOwnerTerminalDisposition disposition =>
      permitted (semanticStorageOwnerKey owner) disposition
  end.

Definition semanticStorageOwnerKeys
  (owners : list SemanticStorageOwner) : list SemanticStorageResourceKey :=
  map semanticStorageOwnerKey owners.

Definition SemanticStorageClosure
  (permitted : PermittedStorageDisposition)
  (owners : list SemanticStorageOwner) : Prop :=
  NoDup (semanticStorageOwnerKeys owners) /\
  Forall (SemanticStorageOwnerClosed permitted) owners.

Theorem live_semantic_storage_owner_blocks_closure :
  forall permitted owners owner,
    SemanticStorageClosure permitted owners ->
    In owner owners ->
    semanticStorageOwnerState owner = SemanticStorageOwnerLive ->
    False.
Proof.
  intros permitted owners owner Hclosure Hin Hlive.
  destruct Hclosure as [_ Hall].
  rewrite Forall_forall in Hall.
  pose proof (Hall owner Hin) as Hclosed.
  unfold SemanticStorageOwnerClosed in Hclosed.
  rewrite Hlive in Hclosed.
  exact Hclosed.
Qed.

Theorem released_semantic_storage_owner_permits_closure :
  forall permitted key,
    SemanticStorageClosure permitted
      [mkSemanticStorageOwner key SemanticStorageOwnerReleased].
Proof.
  intros permitted key.
  split.
  - unfold semanticStorageOwnerKeys.
    simpl.
    constructor.
    + simpl. intros Hcontra. exact Hcontra.
    + constructor.
  - constructor.
    + simpl. exact I.
    + constructor.
Qed.

Theorem exact_permitted_terminal_disposition_permits_closure :
  forall permitted key disposition,
    permitted key disposition ->
    SemanticStorageClosure permitted
      [mkSemanticStorageOwner key
        (SemanticStorageOwnerTerminalDisposition disposition)].
Proof.
  intros permitted key disposition Hpermitted.
  split.
  - unfold semanticStorageOwnerKeys.
    simpl.
    constructor.
    + simpl. intros Hcontra. exact Hcontra.
    + constructor.
  - constructor.
    + simpl. exact Hpermitted.
    + constructor.
Qed.

Theorem unpermitted_terminal_disposition_blocks_closure :
  forall permitted owners owner disposition,
    In owner owners ->
    semanticStorageOwnerState owner =
      SemanticStorageOwnerTerminalDisposition disposition ->
    ~ permitted (semanticStorageOwnerKey owner) disposition ->
    ~ SemanticStorageClosure permitted owners.
Proof.
  intros permitted owners owner disposition Hin Hstate Hnot Hclosure.
  destruct Hclosure as [_ Hall].
  rewrite Forall_forall in Hall.
  pose proof (Hall owner Hin) as Hclosed.
  unfold SemanticStorageOwnerClosed in Hclosed.
  rewrite Hstate in Hclosed.
  exact (Hnot Hclosed).
Qed.

Inductive PhysicalStorageState : Type :=
| PhysicalStorageReclaimed : PhysicalStorageState
| PhysicalStorageRetainedByProfile : StorageProfileRevision -> PhysicalStorageState
| PhysicalStorageLeaked : PhysicalStorageState.

Record PhysicalStorageObjectState : Type := mkPhysicalStorageObjectState {
  physicalStorageStateObject : PhysicalStorageObjectKey;
  physicalStorageState : PhysicalStorageState
}.

Inductive StorageReclamationPolicy : Type :=
| RequirePhysicalReclamation : StorageReclamationPolicy
| PermitPhysicalRetention : StorageProfileRevision -> StorageReclamationPolicy.

Definition PhysicalStorageStateAccepted
  (policy : StorageReclamationPolicy)
  (objectState : PhysicalStorageObjectState) : Prop :=
  match physicalStorageState objectState with
  | PhysicalStorageReclaimed => True
  | PhysicalStorageLeaked => False
  | PhysicalStorageRetainedByProfile actualProfile =>
      match policy with
      | RequirePhysicalReclamation => False
      | PermitPhysicalRetention expectedProfile => expectedProfile = actualProfile
      end
  end.

Definition physicalStorageObjectKeys
  (objects : list PhysicalStorageObjectState) : list PhysicalStorageObjectKey :=
  map physicalStorageStateObject objects.

Definition PhysicalStorageReclamationAccepted
  (policy : StorageReclamationPolicy)
  (objects : list PhysicalStorageObjectState) : Prop :=
  NoDup (physicalStorageObjectKeys objects) /\
  Forall (PhysicalStorageStateAccepted policy) objects.

Theorem reclaimed_physical_storage_is_accepted :
  forall object,
    PhysicalStorageReclamationAccepted RequirePhysicalReclamation
      [mkPhysicalStorageObjectState object PhysicalStorageReclaimed].
Proof.
  intros object.
  split.
  - unfold physicalStorageObjectKeys.
    simpl.
    constructor.
    + simpl. intros Hcontra. exact Hcontra.
    + constructor.
  - constructor.
    + simpl. exact I.
    + constructor.
Qed.

Theorem exact_profile_retention_is_accepted :
  forall object profile,
    PhysicalStorageReclamationAccepted (PermitPhysicalRetention profile)
      [mkPhysicalStorageObjectState object
        (PhysicalStorageRetainedByProfile profile)].
Proof.
  intros object profile.
  split.
  - unfold physicalStorageObjectKeys.
    simpl.
    constructor.
    + simpl. intros Hcontra. exact Hcontra.
    + constructor.
  - constructor.
    + simpl. reflexivity.
    + constructor.
Qed.

Theorem wrong_profile_retention_rejects :
  forall object expected actual,
    expected <> actual ->
    ~ PhysicalStorageReclamationAccepted (PermitPhysicalRetention expected)
        [mkPhysicalStorageObjectState object
          (PhysicalStorageRetainedByProfile actual)].
Proof.
  intros object expected actual Hdifferent Haccepted.
  destruct Haccepted as [_ Hall].
  inversion Hall as [| state rest Hstate Hrest]; subst.
  simpl in Hstate.
  exact (Hdifferent Hstate).
Qed.

Theorem physical_leak_rejects_required_reclamation :
  forall object,
    ~ PhysicalStorageReclamationAccepted RequirePhysicalReclamation
        [mkPhysicalStorageObjectState object PhysicalStorageLeaked].
Proof.
  intros object Haccepted.
  destruct Haccepted as [_ Hall].
  inversion Hall as [| state rest Hstate Hrest]; subst.
  simpl in Hstate.
  exact Hstate.
Qed.

Record CertifiedMemoryProcessClosure
  (identity : StageClosureIdentityFacts)
  (realization : StorageRealizationFacts)
  (terminal : CertifiedProcessTerminalFact)
  (permitted : PermittedStorageDisposition)
  (owners : list SemanticStorageOwner) : Prop := mkCertifiedMemoryProcessClosure {
  certifiedMemoryStageIdentity : StageClosureIdentityValid identity;
  certifiedMemoryRealization : StorageRealizationValid realization;
  certifiedMemorySemanticOwners : SemanticStorageClosure permitted owners
}.

Theorem certified_memory_process_closure_inherits_ordinary_terminal_closure :
  forall identity realization terminal permitted owners,
    CertifiedMemoryProcessClosure
      identity realization terminal permitted owners ->
    ResourceComplete
      (localTerminalContext (certifiedLocalTerminal terminal)).
Proof.
  intros identity realization terminal permitted owners Hcertified.
  apply certified_process_terminal_requires_resource_closure.
Qed.

Theorem live_semantic_storage_owner_blocks_certified_process_closure :
  forall identity realization terminal permitted owners owner,
    CertifiedMemoryProcessClosure
      identity realization terminal permitted owners ->
    In owner owners ->
    semanticStorageOwnerState owner = SemanticStorageOwnerLive ->
    False.
Proof.
  intros identity realization terminal permitted owners owner Hcertified Hin Hlive.
  eapply live_semantic_storage_owner_blocks_closure.
  - exact (certifiedMemorySemanticOwners
      identity realization terminal permitted owners Hcertified).
  - exact Hin.
  - exact Hlive.
Qed.

Definition ProcessStorageOwners := ProcessKey -> list SemanticStorageOwner.
Definition ProcessStoragePermissions := ProcessKey -> PermittedStorageDisposition.

Definition AllStaticProcessStorageClosed
  (population : ProcessPopulation)
  (permissions : ProcessStoragePermissions)
  (owners : ProcessStorageOwners) : Prop :=
  forall occurrence,
    In occurrence population ->
    SemanticStorageClosure
      (permissions (staticProcessKey occurrence))
      (owners (staticProcessKey occurrence)).

Record CertifiedMemoryRootClosure
  (population : ProcessPopulation)
  (facts : CertifiedTerminalMap)
  (statuses : ProcessStatusMap)
  (root : RootSemanticClosure)
  (permissions : ProcessStoragePermissions)
  (owners : ProcessStorageOwners) : Prop := mkCertifiedMemoryRootClosure {
  certifiedMemoryRootTerminal :
    CertifiedRootTerminal population facts statuses root;
  certifiedMemoryAllProcessStorageClosed :
    AllStaticProcessStorageClosed population permissions owners
}.

Theorem live_static_process_storage_owner_blocks_root_closure :
  forall population facts statuses root permissions owners occurrence owner,
    CertifiedMemoryRootClosure
      population facts statuses root permissions owners ->
    In occurrence population ->
    In owner (owners (staticProcessKey occurrence)) ->
    semanticStorageOwnerState owner = SemanticStorageOwnerLive ->
    False.
Proof.
  intros population facts statuses root permissions owners occurrence owner
    Hroot HinPopulation HinOwner Hlive.
  pose proof
    (certifiedMemoryAllProcessStorageClosed
      population facts statuses root permissions owners Hroot
      occurrence HinPopulation) as Hstorage.
  eapply live_semantic_storage_owner_blocks_closure.
  - exact Hstorage.
  - exact HinOwner.
  - exact Hlive.
Qed.

(* Physical reclamation is deliberately absent from CertifiedMemoryRootClosure.
   It may fail at the realization/profile layer without changing the previously
   established Phil terminal fact. *)
Theorem physical_reclamation_failure_does_not_rewrite_semantic_root_terminal :
  forall population facts statuses root permissions owners policy objects,
    CertifiedMemoryRootClosure
      population facts statuses root permissions owners ->
    ~ PhysicalStorageReclamationAccepted policy objects ->
    CertifiedRootTerminal population facts statuses root.
Proof.
  intros population facts statuses root permissions owners policy objects
    Hmemory _.
  exact (certifiedMemoryRootTerminal
    population facts statuses root permissions owners Hmemory).
Qed.

Theorem physical_leak_can_fail_realization_after_semantic_closure :
  forall population facts statuses root permissions owners object,
    CertifiedMemoryRootClosure
      population facts statuses root permissions owners ->
    CertifiedRootTerminal population facts statuses root /\
    ~ PhysicalStorageReclamationAccepted RequirePhysicalReclamation
        [mkPhysicalStorageObjectState object PhysicalStorageLeaked].
Proof.
  intros population facts statuses root permissions owners object Hmemory.
  split.
  - exact (certifiedMemoryRootTerminal
      population facts statuses root permissions owners Hmemory).
  - apply physical_leak_rejects_required_reclamation.
Qed.
