From Stdlib Require Import Strings.String Lists.List Bool.Bool.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ChoiceAmbiguousClose
  FSEM02ChoiceMissingContextGate FSEM02ChoiceCrosswiredContextGate.
Import ListNotations.

(* A non-normative finite observation of the Core End resource agreement
   gate. Process activation/context presence, native Map enumeration, nominal
   grant and actual metadata/resource correspondence are external premises.
   No refusal constructor contains a successor ledger. *)
Inductive FSEM02EndResourceObservation :=
| FSEM02ResourceAgrees
| FSEM02ResourceMissing
| FSEM02ResourceWrongType
| FSEM02ResourceWrongSession.

Inductive FSEM02EndResourceResult :=
| FSEM02EarlierEndGate (result : FSEM02GatedEndResult)
| FSEM02ResourceDisagreement (reason : FSEM02EndResourceObservation).

Definition fsem02EndWithResourceObservation
  (nominalGranted : bool) (resource : FSEM02EndResourceObservation)
  (owners : FSEM02OwnerLedger)
  (process : string) (endpoint : Name) (keys : list string)
  : FSEM02EndResourceResult :=
  match filter (fsem02IsMatchingOwner owners process endpoint) keys with
  | [] => FSEM02EarlierEndGate FSEM02UnknownOwnerGate
  | [key] =>
      if negb nominalGranted
      then FSEM02EarlierEndGate FSEM02NominalRefusedGate
      else match resource with
           | FSEM02ResourceAgrees =>
               FSEM02EarlierEndGate
                 (fsem02GatedEnd true true true true
                   owners process endpoint keys)
           | other => FSEM02ResourceDisagreement other
           end
  | first :: second :: rest =>
      FSEM02EarlierEndGate
        (FSEM02AmbiguousOwnerGate (first :: second :: rest))
  end.

Theorem fsem02ResourceMissingUniqueOwnerRefusesExactly :
  forall owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02EndWithResourceObservation true FSEM02ResourceMissing
      owners process endpoint keys =
      FSEM02ResourceDisagreement FSEM02ResourceMissing.
Proof.
  intros owners process endpoint keys key Hone.
  unfold fsem02EndWithResourceObservation. now rewrite Hone.
Qed.

Theorem fsem02ResourceWrongTypeUniqueOwnerRefusesExactly :
  forall owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02EndWithResourceObservation true FSEM02ResourceWrongType
      owners process endpoint keys =
      FSEM02ResourceDisagreement FSEM02ResourceWrongType.
Proof.
  intros owners process endpoint keys key Hone.
  unfold fsem02EndWithResourceObservation. now rewrite Hone.
Qed.

Theorem fsem02ResourceWrongSessionUniqueOwnerRefusesExactly :
  forall owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02EndWithResourceObservation true FSEM02ResourceWrongSession
      owners process endpoint keys =
      FSEM02ResourceDisagreement FSEM02ResourceWrongSession.
Proof.
  intros owners process endpoint keys key Hone.
  unfold fsem02EndWithResourceObservation. now rewrite Hone.
Qed.

Theorem fsem02ResourceDisagreementNeverRetires :
  forall owners process endpoint keys key resource after,
    resource <> FSEM02ResourceAgrees ->
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02EndWithResourceObservation true resource
      owners process endpoint keys <>
      FSEM02EarlierEndGate (FSEM02ClosedGate after).
Proof.
  intros owners process endpoint keys key resource after Hwrong Hone.
  unfold fsem02EndWithResourceObservation. rewrite Hone.
  destruct resource; try contradiction; discriminate.
Qed.

Theorem fsem02ZeroOwnersPrecedesResourceAgreement :
  forall nominal resource owners process endpoint keys,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [] ->
    fsem02EndWithResourceObservation nominal resource
      owners process endpoint keys =
      FSEM02EarlierEndGate FSEM02UnknownOwnerGate.
Proof.
  intros nominal resource owners process endpoint keys Hzero.
  unfold fsem02EndWithResourceObservation. now rewrite Hzero.
Qed.

Theorem fsem02AmbiguousOwnersPrecedeResourceAgreement :
  forall nominal resource owners process endpoint keys first second rest,
    filter (fsem02IsMatchingOwner owners process endpoint) keys =
      first :: second :: rest ->
    fsem02EndWithResourceObservation nominal resource
      owners process endpoint keys =
      FSEM02EarlierEndGate
        (FSEM02AmbiguousOwnerGate (first :: second :: rest)).
Proof.
  intros nominal resource owners process endpoint keys first second rest Hmany.
  unfold fsem02EndWithResourceObservation. now rewrite Hmany.
Qed.

Theorem fsem02NominalMismatchPrecedesResourceAgreement :
  forall resource owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02EndWithResourceObservation false resource
      owners process endpoint keys =
      FSEM02EarlierEndGate FSEM02NominalRefusedGate.
Proof.
  intros resource owners process endpoint keys key Hone.
  unfold fsem02EndWithResourceObservation. now rewrite Hone.
Qed.

Theorem fsem02ExactResourceAndGrantedRetirement :
  forall owners process endpoint keys key after,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02RetireSelectedClientOwner owners key process endpoint = Some after ->
    fsem02EndWithResourceObservation true FSEM02ResourceAgrees
      owners process endpoint keys =
      FSEM02EarlierEndGate (FSEM02ClosedGate after).
Proof.
  intros owners process endpoint keys key after Hone Hretire.
  unfold fsem02EndWithResourceObservation. rewrite Hone.
  simpl. unfold fsem02GatedEnd. simpl.
  now rewrite Hone, Hretire.
Qed.
