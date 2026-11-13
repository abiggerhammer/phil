From Stdlib Require Import Strings.String Lists.List Bool.Bool.
From Phil.Core Require Import Syntax FSEM02ChoiceAmbiguousClose
  FSEM02ChoiceNearMissClose FSEM02SelectedClientClose.
Import ListNotations.

(* Non-normative FSEM-02: FINITE supplied key lists only. No proof of
   native Map.toList completeness, process activation or nominal authority. *)

Lemma fsem02FilterArbitraryNearMissKeys :
  forall owners process endpoint near,
    Forall (fun key =>
      fsem02IsMatchingOwner owners process endpoint key = false) near ->
    filter (fsem02IsMatchingOwner owners process endpoint) near = [].
Proof.
  intros owners process endpoint near Hall.
  induction Hall as [| key rest Hfalse Hrest IH].
  - reflexivity.
  - simpl. rewrite Hfalse. exact IH.
Qed.

Lemma fsem02UniqueOwnerWithArbitraryNearMisses :
  forall owners process endpoint before exact after,
    Forall (fun key =>
      fsem02IsMatchingOwner owners process endpoint key = false) before ->
    fsem02IsMatchingOwner owners process endpoint exact = true ->
    Forall (fun key =>
      fsem02IsMatchingOwner owners process endpoint key = false) after ->
    filter (fsem02IsMatchingOwner owners process endpoint)
      (before ++ exact :: after) = [exact].
Proof.
  intros owners process endpoint before exact after Hbefore Hexact Hafter.
  induction Hbefore as [| key rest Hfalse Hrest IH].
  - simpl. rewrite Hexact.
    rewrite (fsem02FilterArbitraryNearMissKeys
      owners process endpoint after Hafter).
    reflexivity.
  - simpl. rewrite Hfalse. exact IH.
Qed.

Theorem fsem02AnyFiniteNearMissPopulationKeepsExactCloseAndFrame :
  forall owners process endpoint before exact after result,
    Forall (fun key =>
      fsem02IsMatchingOwner owners process endpoint key = false) before ->
    fsem02IsMatchingOwner owners process endpoint exact = true ->
    Forall (fun key =>
      fsem02IsMatchingOwner owners process endpoint key = false) after ->
    fsem02RetireSelectedClientOwner owners exact process endpoint =
      Some result ->
    fsem02FiniteClose owners process endpoint
      (before ++ exact :: after) = FSEM02RetiredCandidate result /\
    result exact = None /\
    (forall spectator, spectator <> exact ->
      result spectator = owners spectator).
Proof.
  intros owners process endpoint before exact after result
    Hbefore Hexact Hafter Hretire.
  split.
  - unfold fsem02FiniteClose.
    rewrite (fsem02UniqueOwnerWithArbitraryNearMisses
      owners process endpoint before exact after Hbefore Hexact Hafter).
    simpl. now rewrite Hretire.
  - exact (fsem02SelectedClientCloseExactRetirementAndFrame
      owners exact process endpoint result Hretire).
Qed.

Lemma fsem02TwoExactOwnersWithArbitraryNearMisses :
  forall owners process endpoint prefix first middle second suffix,
    Forall (fun key =>
      fsem02IsMatchingOwner owners process endpoint key = false) prefix ->
    fsem02IsMatchingOwner owners process endpoint first = true ->
    Forall (fun key =>
      fsem02IsMatchingOwner owners process endpoint key = false) middle ->
    fsem02IsMatchingOwner owners process endpoint second = true ->
    Forall (fun key =>
      fsem02IsMatchingOwner owners process endpoint key = false) suffix ->
    filter (fsem02IsMatchingOwner owners process endpoint)
      (prefix ++ first :: middle ++ second :: suffix) = [first; second].
Proof.
  intros owners process endpoint prefix first middle second suffix
    Hprefix Hfirst Hmiddle Hsecond Hsuffix.
  induction Hprefix as [| key rest Hfalse Hrest IH].
  - simpl. rewrite Hfirst.
    rewrite (fsem02UniqueOwnerWithArbitraryNearMisses
      owners process endpoint middle second suffix Hmiddle Hsecond Hsuffix).
    reflexivity.
  - simpl. rewrite Hfalse. exact IH.
Qed.

Theorem fsem02ExactDuplicateAmongArbitraryNearMissesRefusesFirst :
  forall owners process endpoint prefix first middle second suffix,
    Forall (fun key =>
      fsem02IsMatchingOwner owners process endpoint key = false) prefix ->
    fsem02IsMatchingOwner owners process endpoint first = true ->
    Forall (fun key =>
      fsem02IsMatchingOwner owners process endpoint key = false) middle ->
    fsem02IsMatchingOwner owners process endpoint second = true ->
    Forall (fun key =>
      fsem02IsMatchingOwner owners process endpoint key = false) suffix ->
    fsem02FiniteClose owners process endpoint
      (prefix ++ first :: middle ++ second :: suffix) =
        FSEM02AmbiguousCandidates [first; second] /\
    (forall result, fsem02FiniteClose owners process endpoint
      (prefix ++ first :: middle ++ second :: suffix) <>
        FSEM02RetiredCandidate result).
Proof.
  intros owners process endpoint prefix first middle second suffix
    Hprefix Hfirst Hmiddle Hsecond Hsuffix.
  assert (Hfilter :
    filter (fsem02IsMatchingOwner owners process endpoint)
      (prefix ++ first :: middle ++ second :: suffix) = [first; second]).
  { exact (fsem02TwoExactOwnersWithArbitraryNearMisses
      owners process endpoint prefix first middle second suffix
      Hprefix Hfirst Hmiddle Hsecond Hsuffix). }
  split.
  - unfold fsem02FiniteClose. now rewrite Hfilter.
  - intros result. unfold fsem02FiniteClose.
    rewrite Hfilter. discriminate.
Qed.
