From Stdlib Require Import Strings.String Lists.List Bool.Bool.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ChoiceAmbiguousClose.
Import ListNotations.

(* FSEM-02 non-normative complement to exact owner ambiguity.
   Entries count only when BOTH process and End name match. Supplied finite
   enumeration completeness relative to Haskell Map.toList is an EXTERNAL
   premise; nominal permission, activation and root authority are external. *)

Lemma fsem02ExactAndNearMissFilter :
  forall owners process endpoint exact near,
    fsem02IsMatchingOwner owners process endpoint exact = true ->
    fsem02IsMatchingOwner owners process endpoint near = false ->
    filter (fsem02IsMatchingOwner owners process endpoint)
      [exact; near] = [exact].
Proof.
  intros owners process endpoint exact near Hmatch Hmiss.
  cbn [filter].
  now rewrite Hmatch, Hmiss.
Qed.

Lemma fsem02NearMissKeepsUniqueRetirementAndFrame :
  forall owners process endpoint exact near after,
    fsem02IsMatchingOwner owners process endpoint exact = true ->
    fsem02IsMatchingOwner owners process endpoint near = false ->
    fsem02RetireSelectedClientOwner owners exact process endpoint =
      Some after ->
    fsem02FiniteClose owners process endpoint [exact; near] =
      FSEM02RetiredCandidate after /\
    after exact = None /\
    (forall spectator, spectator <> exact -> after spectator = owners spectator).
Proof.
  intros owners process endpoint exact near after Hmatch Hmiss Hretire.
  split.
  - unfold fsem02FiniteClose.
    rewrite (fsem02ExactAndNearMissFilter owners process endpoint
      exact near Hmatch Hmiss).
    simpl. now rewrite Hretire.
  - exact (fsem02SelectedClientCloseExactRetirementAndFrame
      owners exact process endpoint after Hretire).
Qed.

Theorem fsem02ForeignProcessSameEndDoesNotFabricateAmbiguity :
  forall owners process endpoint exact near foreignProcess after,
    owners exact = Some (process, endpoint) ->
    owners near = Some (foreignProcess, endpoint) ->
    foreignProcess <> process ->
    fsem02RetireSelectedClientOwner owners exact process endpoint =
      Some after ->
    fsem02FiniteClose owners process endpoint [exact; near] =
      FSEM02RetiredCandidate after /\
    after exact = None /\
    (forall spectator, spectator <> exact -> after spectator = owners spectator).
Proof.
  intros owners process endpoint exact near foreignProcess after
    Hreal Hforeign Hdifferent Hretire.
  apply (fsem02NearMissKeepsUniqueRetirementAndFrame
    owners process endpoint exact near after).
  - unfold fsem02IsMatchingOwner.
    rewrite Hreal. simpl. now rewrite !String.eqb_refl.
  - unfold fsem02IsMatchingOwner.
    rewrite Hforeign.
    assert (Hneq : String.eqb foreignProcess process = false).
    { apply String.eqb_neq. exact Hdifferent. }
    now rewrite Hneq.
  - exact Hretire.
Qed.

Theorem fsem02SameProcessWrongEndDoesNotFabricateAmbiguity :
  forall owners process endpoint exact near foreignEndpoint after,
    owners exact = Some (process, endpoint) ->
    owners near = Some (process, foreignEndpoint) ->
    foreignEndpoint <> endpoint ->
    fsem02RetireSelectedClientOwner owners exact process endpoint =
      Some after ->
    fsem02FiniteClose owners process endpoint [exact; near] =
      FSEM02RetiredCandidate after /\
    after exact = None /\
    (forall spectator, spectator <> exact -> after spectator = owners spectator).
Proof.
  intros owners process endpoint exact near foreignEndpoint after
    Hreal Hforeign Hdifferent Hretire.
  apply (fsem02NearMissKeepsUniqueRetirementAndFrame
    owners process endpoint exact near after).
  - unfold fsem02IsMatchingOwner.
    rewrite Hreal. simpl. now rewrite !String.eqb_refl.
  - unfold fsem02IsMatchingOwner.
    rewrite Hforeign.
    assert (Hneq : String.eqb foreignEndpoint endpoint = false).
    { apply String.eqb_neq. exact Hdifferent. }
    rewrite String.eqb_refl.
    simpl. exact Hneq.
  - exact Hretire.
Qed.
