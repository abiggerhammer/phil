From Stdlib Require Import Strings.String Lists.List Bool.Bool.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose.
Import ListNotations.

(* FSEM-02, non-normative finite-key projection of the native End owner
   ambiguity gate. The enumeration of ALL live owner keys is an EXTERNAL
   premise: we do not prove native Map.toList completeness or a general
   Haskell-to-Rocq simulation. Nominal authority and process activation
   remain external. A duplicate is an adversarial state, NOT source syntax. *)

Inductive FSEM02FiniteCloseResult : Type :=
| FSEM02NoCandidate
| FSEM02AmbiguousCandidates (keys : list string)
| FSEM02RetiredCandidate (after : FSEM02OwnerLedger).

Definition fsem02IsMatchingOwner
  (owners : FSEM02OwnerLedger) (process : string) (endpoint : Name)
  (key : string) : bool :=
  match owners key with
  | None => false
  | Some (actualProcess, actualEndpoint) =>
      String.eqb actualProcess process &&
      String.eqb actualEndpoint endpoint
  end.

Definition fsem02FiniteClose
  (owners : FSEM02OwnerLedger) (process : string) (endpoint : Name)
  (enumeratedKeys : list string) : FSEM02FiniteCloseResult :=
  match filter (fsem02IsMatchingOwner owners process endpoint)
      enumeratedKeys with
  | [] => FSEM02NoCandidate
  | [key] =>
      match fsem02RetireSelectedClientOwner owners key process endpoint with
      | None => FSEM02NoCandidate
      | Some after => FSEM02RetiredCandidate after
      end
  | first :: second :: rest =>
      FSEM02AmbiguousCandidates (first :: second :: rest)
  end.

Theorem fsem02TwoExactEndOwnersRefuseBeforeRetirement :
  forall owners process endpoint first second,
    owners first = Some (process, endpoint) ->
    owners second = Some (process, endpoint) ->
    fsem02FiniteClose owners process endpoint [first; second] =
      FSEM02AmbiguousCandidates [first; second].
Proof.
  intros owners process endpoint first second Hfirst Hsecond.
  unfold fsem02FiniteClose, fsem02IsMatchingOwner.
  simpl. rewrite Hfirst, Hsecond.
  simpl. now rewrite !String.eqb_refl.
Qed.

Theorem fsem02AmbiguousEndHasNoRetiredSuccessor :
  forall owners process endpoint first second after,
    owners first = Some (process, endpoint) ->
    owners second = Some (process, endpoint) ->
    fsem02FiniteClose owners process endpoint [first; second] <>
      FSEM02RetiredCandidate after.
Proof.
  intros owners process endpoint first second after Hfirst Hsecond.
  rewrite (fsem02TwoExactEndOwnersRefuseBeforeRetirement
    owners process endpoint first second Hfirst Hsecond).
  discriminate.
Qed.

Definition fsem02WithoutAlias
  (owners : FSEM02OwnerLedger) (alias : string) : FSEM02OwnerLedger :=
  fun key => if String.eqb key alias then None else owners key.

(* A separately authorized, precise duplicate cleanup restores a unique
   finite candidate. That cleanup is an external operation, not an inferred
   source-owned action or permission to mutate the actual protocol state. *)
Theorem fsem02DropOnlyAliasRestoresExactRetirementAndFrames :
  forall owners process endpoint original alias after,
    original <> alias ->
    owners original = Some (process, endpoint) ->
    fsem02RetireSelectedClientOwner
      (fsem02WithoutAlias owners alias) original process endpoint =
      Some after ->
    fsem02FiniteClose
      (fsem02WithoutAlias owners alias) process endpoint
      [original; alias] = FSEM02RetiredCandidate after /\
    after original = None /\
    (forall spectator, spectator <> original ->
      after spectator = fsem02WithoutAlias owners alias spectator).
Proof.
  intros owners process endpoint original alias after
    Hdistinct Howner Hretire.
  assert (Hneq : String.eqb original alias = false).
  { apply String.eqb_neq. exact Hdistinct. }
  assert (Horiginal :
    fsem02WithoutAlias owners alias original =
      Some (process, endpoint)).
  { unfold fsem02WithoutAlias. now rewrite Hneq. }
  assert (Halias : fsem02WithoutAlias owners alias alias = None).
  { unfold fsem02WithoutAlias. now rewrite String.eqb_refl. }
  split.
  - unfold fsem02FiniteClose, fsem02IsMatchingOwner.
    simpl. rewrite Horiginal, Halias.
    simpl. rewrite !String.eqb_refl.
    simpl. now rewrite Hretire.
  - exact (fsem02SelectedClientCloseExactRetirementAndFrame
      (fsem02WithoutAlias owners alias) original process endpoint
      after Hretire).
Qed.
