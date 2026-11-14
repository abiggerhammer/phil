From Stdlib Require Import Strings.String Lists.List Bool.Bool.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ChoiceAmbiguousClose
  FSEM02ChoiceMissingContextGate FSEM02ChoiceResourceAgreementGate
  FSEM02ChoiceOutcomeResourceGate.
Import ListNotations.

(* Non-normative FSEM-02: each flag is supplied by an independent native
   observation. An absent process-local protocol context precedes the owner,
   nominal, resource, and external-outcome observations. The modeled finite
   owner enumeration is NOT certified equivalent to Haskell Map.toList. *)
Inductive FSEM02TripleGateResult : Type :=
| FSEM02TripleMissingContext
| FSEM02TripleContextChecked (result : FSEM02OutcomeResourceResult).

Definition fsem02TripleFaultGate
  (contextPresent nominalGranted outcomeMatches : bool)
  (resource : FSEM02EndResourceObservation)
  (owners : FSEM02OwnerLedger)
  (process : string) (endpoint : Name) (keys : list string)
  : FSEM02TripleGateResult :=
  if contextPresent
  then FSEM02TripleContextChecked
    (fsem02OutcomeResourceGate nominalGranted outcomeMatches
      resource owners process endpoint keys)
  else FSEM02TripleMissingContext.

Theorem fsem02TripleMissingContextPrecedesAllLaterGates :
  forall nominal outcome resource owners process endpoint keys,
    fsem02TripleFaultGate false nominal outcome resource
      owners process endpoint keys = FSEM02TripleMissingContext.
Proof. reflexivity. Qed.

Theorem fsem02TripleMissingContextHasNoRetiredSuccessor :
  forall nominal outcome resource owners process endpoint keys after,
    fsem02TripleFaultGate false nominal outcome resource
      owners process endpoint keys <>
      FSEM02TripleContextChecked
        (FSEM02OutcomePriorGate (FSEM02ClosedGate after)).
Proof. intros; discriminate. Qed.

Theorem fsem02TripleRestoredMissingResourcePrecedesWrongOutcome :
  forall owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02TripleFaultGate true true false FSEM02ResourceMissing
      owners process endpoint keys =
      FSEM02TripleContextChecked
        (FSEM02OutcomeResourceRefusal FSEM02ResourceMissing).
Proof.
  intros owners process endpoint keys key Hone.
  unfold fsem02TripleFaultGate; simpl.
  now rewrite (fsem02MissingResourcePrecedesWrongOutcome
    false owners process endpoint keys key Hone).
Qed.

Theorem fsem02TripleRestoredWrongTypePrecedesWrongOutcome :
  forall owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02TripleFaultGate true true false FSEM02ResourceWrongType
      owners process endpoint keys =
      FSEM02TripleContextChecked
        (FSEM02OutcomeResourceRefusal FSEM02ResourceWrongType).
Proof.
  intros owners process endpoint keys key Hone.
  unfold fsem02TripleFaultGate; simpl.
  now rewrite (fsem02WrongTypePrecedesWrongOutcome
    false owners process endpoint keys key Hone).
Qed.

Theorem fsem02TripleRestoredWrongSessionPrecedesWrongOutcome :
  forall owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02TripleFaultGate true true false FSEM02ResourceWrongSession
      owners process endpoint keys =
      FSEM02TripleContextChecked
        (FSEM02OutcomeResourceRefusal FSEM02ResourceWrongSession).
Proof.
  intros owners process endpoint keys key Hone.
  unfold fsem02TripleFaultGate; simpl.
  now rewrite (fsem02WrongSessionPrecedesWrongOutcome
    false owners process endpoint keys key Hone).
Qed.

Theorem fsem02TripleRestoredResourceStillRequiresCorrectOutcome :
  forall owners process endpoint keys key,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02TripleFaultGate true true false FSEM02ResourceAgrees
      owners process endpoint keys =
      FSEM02TripleContextChecked FSEM02WrongOutcomeRefusal.
Proof.
  intros owners process endpoint keys key Hone.
  unfold fsem02TripleFaultGate; simpl.
  now rewrite (fsem02WrongOutcomeAfterResourceAgreement
    owners process endpoint keys key Hone).
Qed.

Theorem fsem02TripleCorrectOutcomeRequiresSeparateRetirement :
  forall owners process endpoint keys key after,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02RetireSelectedClientOwner owners key process endpoint = Some after ->
    fsem02TripleFaultGate true true true FSEM02ResourceAgrees
      owners process endpoint keys =
      FSEM02TripleContextChecked
        (FSEM02OutcomePriorGate (FSEM02ClosedGate after)).
Proof.
  intros owners process endpoint keys key after Hone Hretire.
  unfold fsem02TripleFaultGate; simpl.
  now rewrite (fsem02MatchingOutcomeAndResourceNeedRetirementPremise
    owners process endpoint keys key after Hone Hretire).
Qed.

Theorem fsem02TripleWrongOutcomeCannotRetire :
  forall owners process endpoint keys key after,
    filter (fsem02IsMatchingOwner owners process endpoint) keys = [key] ->
    fsem02TripleFaultGate true true false FSEM02ResourceAgrees
      owners process endpoint keys <>
      FSEM02TripleContextChecked
        (FSEM02OutcomePriorGate (FSEM02ClosedGate after)).
Proof.
  intros owners process endpoint keys key after Hone.
  rewrite (fsem02TripleRestoredResourceStillRequiresCorrectOutcome
    owners process endpoint keys key Hone).
  discriminate.
Qed.
