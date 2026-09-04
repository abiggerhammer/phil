From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import
  StorageRealization
  SystemsStageClosure
  ConcurrencyTerminal
  StorageTerminalClosure.

(*
  Machine-facing decision surface for PHIL-MEM-CLOSURE-001.

  Semantic storage closure and physical reclamation remain separate classifiers.
  The process/root composition gates include semantic storage closure only;
  physical reclamation is deliberately absent from those semantic terminal gates.
*)

Definition decideSemanticStorageLiveByFacts : bool := false.

Definition decideSemanticStorageReleasedByFacts : bool := true.

Definition decideSemanticStorageTerminalDispositionByFacts
  (permittedExact : bool) : bool :=
  permittedExact.

Definition decideSemanticStorageClosureByFacts
  (ownerKeysUnique allOwnersClosed : bool) : bool :=
  andb ownerKeysUnique allOwnersClosed.

Definition decidePhysicalStorageReclaimedByFacts : bool := true.

Definition decidePhysicalStorageLeakedByFacts : bool := false.

Definition decidePhysicalStorageRetainedByProfileByFacts
  (policyPermitsRetention profileExact : bool) : bool :=
  andb policyPermitsRetention profileExact.

Definition decidePhysicalStorageReclamationByFacts
  (objectKeysUnique allStatesAccepted : bool) : bool :=
  andb objectKeysUnique allStatesAccepted.

Definition decideCertifiedMemoryProcessClosureByFacts
  (stageIdentityValid realizationValid semanticStorageClosed : bool) : bool :=
  andb stageIdentityValid (andb realizationValid semanticStorageClosed).

Definition decideCertifiedMemoryRootClosureByFacts
  (rootTerminalValid allStaticStorageClosed : bool) : bool :=
  andb rootTerminalValid allStaticStorageClosed.

Theorem decideSemanticStorageLiveByFacts_classifies :
  forall permitted key,
    decideSemanticStorageLiveByFacts = true <->
    SemanticStorageOwnerClosed permitted
      (mkSemanticStorageOwner key SemanticStorageOwnerLive).
Proof.
  intros permitted key.
  unfold decideSemanticStorageLiveByFacts, SemanticStorageOwnerClosed.
  simpl.
  split.
  - intros Hfalse. discriminate Hfalse.
  - intros Hfalse. contradiction.
Qed.

Theorem decideSemanticStorageReleasedByFacts_classifies :
  forall permitted key,
    decideSemanticStorageReleasedByFacts = true <->
    SemanticStorageOwnerClosed permitted
      (mkSemanticStorageOwner key SemanticStorageOwnerReleased).
Proof.
  intros permitted key.
  unfold decideSemanticStorageReleasedByFacts, SemanticStorageOwnerClosed.
  simpl.
  split; intros _.
  - exact I.
  - reflexivity.
Qed.

Theorem decideSemanticStorageTerminalDispositionByFacts_classifies :
  forall permitted key disposition permittedExact,
    (permittedExact = true <-> permitted key disposition) ->
    decideSemanticStorageTerminalDispositionByFacts permittedExact = true <->
    SemanticStorageOwnerClosed permitted
      (mkSemanticStorageOwner key
        (SemanticStorageOwnerTerminalDisposition disposition)).
Proof.
  intros permitted key disposition permittedExact Hpermitted.
  unfold decideSemanticStorageTerminalDispositionByFacts,
    SemanticStorageOwnerClosed.
  simpl.
  exact Hpermitted.
Qed.

Theorem decideSemanticStorageClosureByFacts_classifies :
  forall permitted owners ownerKeysUnique allOwnersClosed,
    (ownerKeysUnique = true <->
      NoDup (semanticStorageOwnerKeys owners)) ->
    (allOwnersClosed = true <->
      Forall (SemanticStorageOwnerClosed permitted) owners) ->
    decideSemanticStorageClosureByFacts
      ownerKeysUnique allOwnersClosed = true <->
    SemanticStorageClosure permitted owners.
Proof.
  intros permitted owners ownerKeysUnique allOwnersClosed Hunique Hall.
  unfold decideSemanticStorageClosureByFacts, SemanticStorageClosure.
  rewrite andb_true_iff.
  split.
  - intros [HuniqueBool HallBool].
    split.
    + apply (proj1 Hunique). exact HuniqueBool.
    + apply (proj1 Hall). exact HallBool.
  - intros [HuniqueProp HallProp].
    split.
    + apply (proj2 Hunique). exact HuniqueProp.
    + apply (proj2 Hall). exact HallProp.
Qed.

Theorem decidePhysicalStorageReclaimedByFacts_classifies :
  forall policy object,
    decidePhysicalStorageReclaimedByFacts = true <->
    PhysicalStorageStateAccepted policy
      (mkPhysicalStorageObjectState object PhysicalStorageReclaimed).
Proof.
  intros policy object.
  unfold decidePhysicalStorageReclaimedByFacts, PhysicalStorageStateAccepted.
  simpl.
  split; intros _.
  - exact I.
  - reflexivity.
Qed.

Theorem decidePhysicalStorageLeakedByFacts_classifies :
  forall policy object,
    decidePhysicalStorageLeakedByFacts = true <->
    PhysicalStorageStateAccepted policy
      (mkPhysicalStorageObjectState object PhysicalStorageLeaked).
Proof.
  intros policy object.
  unfold decidePhysicalStorageLeakedByFacts, PhysicalStorageStateAccepted.
  simpl.
  split.
  - intros Hfalse. discriminate Hfalse.
  - intros Hfalse. contradiction.
Qed.

Theorem decidePhysicalStorageRetainedByProfileByFacts_classifies :
  forall policy object actualProfile policyPermitsRetention profileExact,
    (policyPermitsRetention = true <->
      match policy with
      | RequirePhysicalReclamation => False
      | PermitPhysicalRetention _ => True
      end) ->
    (profileExact = true <->
      match policy with
      | RequirePhysicalReclamation => False
      | PermitPhysicalRetention expectedProfile =>
          expectedProfile = actualProfile
      end) ->
    decidePhysicalStorageRetainedByProfileByFacts
      policyPermitsRetention profileExact = true <->
    PhysicalStorageStateAccepted policy
      (mkPhysicalStorageObjectState object
        (PhysicalStorageRetainedByProfile actualProfile)).
Proof.
  intros policy object actualProfile policyPermitsRetention profileExact
    Hpermits Hexact.
  destruct policy as [| expectedProfile].
  - simpl in Hpermits, Hexact |- *.
    unfold decidePhysicalStorageRetainedByProfileByFacts.
    rewrite andb_true_iff.
    split.
    + intros [HpermitBool _].
      apply (proj1 Hpermits) in HpermitBool.
      contradiction.
    + intros Hfalse. contradiction.
  - simpl in Hpermits, Hexact |- *.
    unfold decidePhysicalStorageRetainedByProfileByFacts.
    rewrite andb_true_iff.
    split.
    + intros [_ HexactBool].
      apply (proj1 Hexact).
      exact HexactBool.
    + intros Hprofiles.
      split.
      * apply (proj2 Hpermits). exact I.
      * apply (proj2 Hexact). exact Hprofiles.
Qed.

Theorem decidePhysicalStorageReclamationByFacts_classifies :
  forall policy objects objectKeysUnique allStatesAccepted,
    (objectKeysUnique = true <->
      NoDup (physicalStorageObjectKeys objects)) ->
    (allStatesAccepted = true <->
      Forall (PhysicalStorageStateAccepted policy) objects) ->
    decidePhysicalStorageReclamationByFacts
      objectKeysUnique allStatesAccepted = true <->
    PhysicalStorageReclamationAccepted policy objects.
Proof.
  intros policy objects objectKeysUnique allStatesAccepted Hunique Hall.
  unfold decidePhysicalStorageReclamationByFacts,
    PhysicalStorageReclamationAccepted.
  rewrite andb_true_iff.
  split.
  - intros [HuniqueBool HallBool].
    split.
    + apply (proj1 Hunique). exact HuniqueBool.
    + apply (proj1 Hall). exact HallBool.
  - intros [HuniqueProp HallProp].
    split.
    + apply (proj2 Hunique). exact HuniqueProp.
    + apply (proj2 Hall). exact HallProp.
Qed.

Theorem decideCertifiedMemoryProcessClosureByFacts_classifies :
  forall identity realization terminal permitted owners
    stageIdentityValid realizationValid semanticStorageClosed,
    (stageIdentityValid = true <-> StageClosureIdentityValid identity) ->
    (realizationValid = true <-> StorageRealizationValid realization) ->
    (semanticStorageClosed = true <-> SemanticStorageClosure permitted owners) ->
    decideCertifiedMemoryProcessClosureByFacts
      stageIdentityValid realizationValid semanticStorageClosed = true <->
    CertifiedMemoryProcessClosure
      identity realization terminal permitted owners.
Proof.
  intros identity realization terminal permitted owners
    stageIdentityValid realizationValid semanticStorageClosed
    Hstage Hrealization Hstorage.
  unfold decideCertifiedMemoryProcessClosureByFacts.
  rewrite andb_true_iff, andb_true_iff.
  split.
  - intros [HstageBool [HrealizationBool HstorageBool]].
    constructor.
    + apply (proj1 Hstage). exact HstageBool.
    + apply (proj1 Hrealization). exact HrealizationBool.
    + apply (proj1 Hstorage). exact HstorageBool.
  - intros Hcertified.
    destruct Hcertified as [HstageProp HrealizationProp HstorageProp].
    split.
    + apply (proj2 Hstage). exact HstageProp.
    + split.
      * apply (proj2 Hrealization). exact HrealizationProp.
      * apply (proj2 Hstorage). exact HstorageProp.
Qed.

Theorem decideCertifiedMemoryRootClosureByFacts_classifies :
  forall population facts statuses root permissions owners
    rootTerminalValid allStaticStorageClosed,
    (rootTerminalValid = true <->
      CertifiedRootTerminal population facts statuses root) ->
    (allStaticStorageClosed = true <->
      AllStaticProcessStorageClosed population permissions owners) ->
    decideCertifiedMemoryRootClosureByFacts
      rootTerminalValid allStaticStorageClosed = true <->
    CertifiedMemoryRootClosure
      population facts statuses root permissions owners.
Proof.
  intros population facts statuses root permissions owners
    rootTerminalValid allStaticStorageClosed Hterminal Hstorage.
  unfold decideCertifiedMemoryRootClosureByFacts.
  rewrite andb_true_iff.
  split.
  - intros [HterminalBool HstorageBool].
    constructor.
    + apply (proj1 Hterminal). exact HterminalBool.
    + apply (proj1 Hstorage). exact HstorageBool.
  - intros Hcertified.
    destruct Hcertified as [HterminalProp HstorageProp].
    split.
    + apply (proj2 Hterminal). exact HterminalProp.
    + apply (proj2 Hstorage). exact HstorageProp.
Qed.
