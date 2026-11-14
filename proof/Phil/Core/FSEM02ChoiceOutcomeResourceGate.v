From Stdlib Require Import Strings.String Lists.List Bool.Bool.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ChoiceAmbiguousClose
  FSEM02ChoiceMissingContextGate FSEM02ChoiceResourceAgreementGate.
Import ListNotations.

(* FSEM-02: terminal outcome is an independent supplied observation.
   A correct owner, nominal grant, and matching resource do not certify it.
   The finite owner enumeration and actual Haskell diagnostics are premises. *)
Inductive FSEM02OutcomeResourceResult : Type :=
| FSEM02OutcomePriorGate (gate : FSEM02GatedEndResult)
| FSEM02OutcomeResourceRefusal (reason : FSEM02EndResourceObservation)
| FSEM02WrongOutcomeRefusal.

Definition fsem02OutcomeResourceGate
  (nominalGranted outcomeMatches : bool)
  (resource : FSEM02EndResourceObservation)
  (owners : FSEM02OwnerLedger)
  (process : string) (endpoint : Name) (keys : list string)
  : FSEM02OutcomeResourceResult :=
  match filter (fsem02IsMatchingOwner owners process endpoint) keys with
  | [] => FSEM02OutcomePriorGate FSEM02UnknownOwnerGate
  | [key] =>
      if negb nominalGranted
      then FSEM02OutcomePriorGate FSEM02NominalRefusedGate
      else match resource with
           | FSEM02ResourceAgrees =>
               if outcomeMatches
               then FSEM02OutcomePriorGate
                      (fsem02GatedEnd true true true true
                        owners process endpoint keys)
               else FSEM02WrongOutcomeRefusal
           | other => FSEM02OutcomeResourceRefusal other
           end
  | first :: second :: rest =>
      FSEM02OutcomePriorGate
        (FSEM02AmbiguousOwnerGate (first :: second :: rest))
  end.

Theorem fsem02WrongOutcomeAfterResourceAgreement :
  forall owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02OutcomeResourceGate true false FSEM02ResourceAgrees
      owners process endpoint keys = FSEM02WrongOutcomeRefusal.
Proof.
  intros owners process endpoint keys key Hone.
  unfold fsem02OutcomeResourceGate. now rewrite Hone.
Qed.

Theorem fsem02MissingResourcePrecedesWrongOutcome :
  forall outcome owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02OutcomeResourceGate true outcome FSEM02ResourceMissing
      owners process endpoint keys =
      FSEM02OutcomeResourceRefusal FSEM02ResourceMissing.
Proof.
  intros outcome owners process endpoint keys key Hone.
  unfold fsem02OutcomeResourceGate. now rewrite Hone.
Qed.

Theorem fsem02WrongTypePrecedesWrongOutcome :
  forall outcome owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02OutcomeResourceGate true outcome FSEM02ResourceWrongType
      owners process endpoint keys =
      FSEM02OutcomeResourceRefusal FSEM02ResourceWrongType.
Proof.
  intros outcome owners process endpoint keys key Hone.
  unfold fsem02OutcomeResourceGate. now rewrite Hone.
Qed.

Theorem fsem02WrongSessionPrecedesWrongOutcome :
  forall outcome owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02OutcomeResourceGate true outcome FSEM02ResourceWrongSession
      owners process endpoint keys =
      FSEM02OutcomeResourceRefusal FSEM02ResourceWrongSession.
Proof.
  intros outcome owners process endpoint keys key Hone.
  unfold fsem02OutcomeResourceGate. now rewrite Hone.
Qed.

Theorem fsem02WrongOutcomeHasNoRetiredSuccessor :
  forall owners process endpoint keys key after,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02OutcomeResourceGate true false FSEM02ResourceAgrees
      owners process endpoint keys <>
      FSEM02OutcomePriorGate (FSEM02ClosedGate after).
Proof.
  intros owners process endpoint keys key after Hone.
  rewrite (fsem02WrongOutcomeAfterResourceAgreement _ _ _ _ _ Hone).
  discriminate.
Qed.

Theorem fsem02UnmatchedOwnerPrecedesOutcomeAndResources :
  forall nominal outcome resource owners process endpoint keys,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [] ->
    fsem02OutcomeResourceGate nominal outcome resource
      owners process endpoint keys =
      FSEM02OutcomePriorGate FSEM02UnknownOwnerGate.
Proof.
  intros nominal outcome resource owners process endpoint keys Hnone.
  unfold fsem02OutcomeResourceGate. now rewrite Hnone.
Qed.

Theorem fsem02AmbiguousOwnersPrecedeOutcomeAndResources :
  forall nominal outcome resource owners process endpoint keys x y rest,
    filter (fsem02IsMatchingOwner owners process endpoint) keys =
      x :: y :: rest ->
    fsem02OutcomeResourceGate nominal outcome resource
      owners process endpoint keys =
      FSEM02OutcomePriorGate (FSEM02AmbiguousOwnerGate (x :: y :: rest)).
Proof.
  intros nominal outcome resource owners process endpoint keys x y rest Hmany.
  unfold fsem02OutcomeResourceGate. now rewrite Hmany.
Qed.

Theorem fsem02OutcomeCannotOverrideNominalRefusal :
  forall outcome resource owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02OutcomeResourceGate false outcome resource
      owners process endpoint keys =
      FSEM02OutcomePriorGate FSEM02NominalRefusedGate.
Proof.
  intros outcome resource owners process endpoint keys key Hone.
  unfold fsem02OutcomeResourceGate. now rewrite Hone.
Qed.

Theorem fsem02MatchingOutcomeAndResourceNeedRetirementPremise :
  forall owners process endpoint keys key after,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02RetireSelectedClientOwner owners key process endpoint = Some after ->
    fsem02OutcomeResourceGate true true FSEM02ResourceAgrees
      owners process endpoint keys =
      FSEM02OutcomePriorGate (FSEM02ClosedGate after).
Proof.
  intros owners process endpoint keys key after Hone Hretire.
  unfold fsem02OutcomeResourceGate. rewrite Hone. simpl.
  unfold fsem02GatedEnd. simpl.
  now rewrite Hone, Hretire.
Qed.
