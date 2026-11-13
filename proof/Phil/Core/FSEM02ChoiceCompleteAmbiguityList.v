From Stdlib Require Import Strings.String Lists.List Bool.Bool.
From Phil.Core Require Import Syntax FSEM02ChoiceAmbiguousClose.
Import ListNotations.

(* Non-normative FSEM-02. The caller supplies a finite, complete,
   duplicate-free enumeration. Native Map.toList correspondence,
   activation, protocol and architecture authorization are NOT proved. *)

Lemma fsem02MatchingListMembership :
  forall owners process endpoint keys key,
    In key (filter (fsem02IsMatchingOwner owners process endpoint) keys) <->
    In key keys /\
      fsem02IsMatchingOwner owners process endpoint key = true.
Proof.
  intros owners process endpoint keys key.
  apply filter_In.
Qed.

Lemma fsem02MatchingListPreservesNoDup :
  forall owners process endpoint keys,
    NoDup keys ->
    NoDup (filter (fsem02IsMatchingOwner owners process endpoint) keys).
Proof.
  intros owners process endpoint keys Hunique.
  induction Hunique as [| key tail Habsent Htail IH].
  - constructor.
  - simpl.
    destruct (fsem02IsMatchingOwner owners process endpoint key)
      eqn:Hmatches.
    + constructor.
      * intro Hpresent.
        apply Habsent.
        apply filter_In in Hpresent.
        exact (proj1 Hpresent).
      * exact IH.
    + exact IH.
Qed.

Theorem fsem02AllFiniteExactEndOwnersReportedWithoutRetirement :
  forall owners process endpoint population first second remaining,
    NoDup population ->
    filter (fsem02IsMatchingOwner owners process endpoint) population =
      first :: second :: remaining ->
    fsem02FiniteClose owners process endpoint population =
      FSEM02AmbiguousCandidates (first :: second :: remaining) /\
    NoDup (first :: second :: remaining) /\
    (forall key, In key (first :: second :: remaining) <->
      In key population /\
      fsem02IsMatchingOwner owners process endpoint key = true) /\
    (forall successor,
      fsem02FiniteClose owners process endpoint population <>
        FSEM02RetiredCandidate successor).
Proof.
  intros owners process endpoint population first second remaining
    Hunique Hfiltered.
  split.
  - unfold fsem02FiniteClose.
    now rewrite Hfiltered.
  - split.
    + rewrite <- Hfiltered.
      exact (fsem02MatchingListPreservesNoDup
        owners process endpoint population Hunique).
    + split.
      * intros key. rewrite <- Hfiltered.
        apply fsem02MatchingListMembership.
      * intros successor. unfold fsem02FiniteClose.
        rewrite Hfiltered. discriminate.
Qed.
