From Stdlib Require Import Strings.String Lists.List Bool.Bool.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ChoiceAmbiguousClose
  FSEM02ChoiceMissingContextGate.
Import ListNotations.

(* Non-normative supplied observation, NOT a Haskell Map-to-Rocq proof.
   contextLocal and nominalGranted are external independent premises.
   Rejection constructors carry no successor and cannot grant authority. *)
Definition fsem02ContextLocalEnd
  (processPresent active contextPresent contextLocal nominalGranted : bool)
  (owners : FSEM02OwnerLedger)
  (process : string) (endpoint : Name) (keys : list string)
  : FSEM02GatedEndResult :=
  fsem02GatedEnd processPresent active contextPresent
    (andb contextLocal nominalGranted) owners process endpoint keys.

Theorem fsem02CrosswiredUniqueOwnerRefusesDespiteNominalInput :
  forall owners process endpoint keys key nominal,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02ContextLocalEnd true true true false nominal
      owners process endpoint keys = FSEM02NominalRefusedGate.
Proof.
  intros owners process endpoint keys key nominal Hone.
  unfold fsem02ContextLocalEnd, fsem02GatedEnd. simpl.
  now rewrite Hone.
Qed.

Theorem fsem02CrosswiredUniqueOwnerHasNoRetiredSuccessor :
  forall owners process endpoint keys key nominal after,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02ContextLocalEnd true true true false nominal
      owners process endpoint keys <> FSEM02ClosedGate after.
Proof.
  intros owners process endpoint keys key nominal after Hone Hclosed.
  unfold fsem02ContextLocalEnd, fsem02GatedEnd in Hclosed.
  simpl in Hclosed. rewrite Hone in Hclosed. discriminate.
Qed.

Theorem fsem02CrosswiredZeroOwnerPrecedesProtocolContextIdentity :
  forall owners process endpoint keys nominal,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [] ->
    fsem02ContextLocalEnd true true true false nominal
      owners process endpoint keys = FSEM02UnknownOwnerGate.
Proof.
  intros owners process endpoint keys nominal Hzero.
  unfold fsem02ContextLocalEnd, fsem02GatedEnd. simpl.
  now rewrite Hzero.
Qed.

Theorem fsem02CrosswiredDuplicateOwnersPrecedeProtocolContextIdentity :
  forall owners process endpoint keys nominal first second rest,
    filter (fsem02IsMatchingOwner owners process endpoint) keys =
      first :: second :: rest ->
    fsem02ContextLocalEnd true true true false nominal
      owners process endpoint keys =
      FSEM02AmbiguousOwnerGate (first :: second :: rest).
Proof.
  intros owners process endpoint keys nominal first second rest Hmultiple.
  unfold fsem02ContextLocalEnd, fsem02GatedEnd. simpl.
  now rewrite Hmultiple.
Qed.

Theorem fsem02RestoredLocalContextStillNeedsNominalGrant :
  forall owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02ContextLocalEnd true true true true false
      owners process endpoint keys = FSEM02NominalRefusedGate.
Proof.
  intros owners process endpoint keys key Hone.
  unfold fsem02ContextLocalEnd, fsem02GatedEnd. simpl.
  now rewrite Hone.
Qed.

Theorem fsem02RestoredLocalContextUniqueAuthorizedOwnerRetires :
  forall owners process endpoint keys key after,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02RetireSelectedClientOwner owners key process endpoint = Some after ->
    fsem02ContextLocalEnd true true true true true
      owners process endpoint keys = FSEM02ClosedGate after.
Proof.
  intros owners process endpoint keys key after Hone Hretire.
  unfold fsem02ContextLocalEnd, fsem02GatedEnd. simpl.
  now rewrite Hone, Hretire.
Qed.
