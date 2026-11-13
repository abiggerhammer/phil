From Stdlib Require Import Strings.String Lists.List Bool.Bool.
From Phil.Core Require Import Syntax FSEM02ChoiceAmbiguousClose
  FSEM02ChoiceCompleteAmbiguityList.
Import ListNotations.

(* Non-normative FSEM-02: the supplied enumerated key population and
   native Map-to-model fidelity are premises, NOT established here.
   Nominal Close authority, activation and architecture are external. *)

Theorem fsem02ZeroMatchingEndOwnersHasNoSuccessor :
  forall owners process endpoint population,
    filter (fsem02IsMatchingOwner owners process endpoint) population = [] ->
    fsem02FiniteClose owners process endpoint population = FSEM02NoCandidate.
Proof.
  intros owners process endpoint population Hempty.
  unfold fsem02FiniteClose.
  now rewrite Hempty.
Qed.

Theorem fsem02SingleMatchingEndOwnerWithGrantedRetirement :
  forall owners process endpoint population key after,
    filter (fsem02IsMatchingOwner owners process endpoint) population = [key] ->
    fsem02RetireSelectedClientOwner owners key process endpoint = Some after ->
    fsem02FiniteClose owners process endpoint population =
      FSEM02RetiredCandidate after.
Proof.
  intros owners process endpoint population key after Hone Hretire.
  unfold fsem02FiniteClose.
  now rewrite Hone, Hretire.
Qed.

Theorem fsem02SingleMatchingEndOwnerWithoutRetirementGrant :
  forall owners process endpoint population key,
    filter (fsem02IsMatchingOwner owners process endpoint) population = [key] ->
    fsem02RetireSelectedClientOwner owners key process endpoint = None ->
    fsem02FiniteClose owners process endpoint population = FSEM02NoCandidate.
Proof.
  intros owners process endpoint population key Hone Hdeny.
  unfold fsem02FiniteClose.
  now rewrite Hone, Hdeny.
Qed.

Theorem fsem02MultipleMatchingEndOwnersPreserveExactCandidates :
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
    (forall after, fsem02FiniteClose owners process endpoint population <>
      FSEM02RetiredCandidate after).
Proof.
  intros owners process endpoint population first second remaining Hunique Htwo.
  exact (fsem02AllFiniteExactEndOwnersReportedWithoutRetirement
    owners process endpoint population first second remaining Hunique Htwo).
Qed.

(* Exhaustive finite cardinality split. The one-key branch still depends
   on a separate successful retirement check. This is NOT permission to
   derive an external protocol grant merely from a matching owner key. *)
Theorem fsem02EveryFiniteEndPopulationHasOneOfThreeShapes :
  forall owners process endpoint population,
    (filter (fsem02IsMatchingOwner owners process endpoint) population = [] /\
      fsem02FiniteClose owners process endpoint population = FSEM02NoCandidate)
    \/
    (exists key, filter (fsem02IsMatchingOwner owners process endpoint)
       population = [key] /\
      (fsem02FiniteClose owners process endpoint population = FSEM02NoCandidate
       \/
       exists after, fsem02FiniteClose owners process endpoint population =
         FSEM02RetiredCandidate after))
    \/
    (exists first second rest,
      filter (fsem02IsMatchingOwner owners process endpoint) population =
        first :: second :: rest /\
      fsem02FiniteClose owners process endpoint population =
        FSEM02AmbiguousCandidates (first :: second :: rest)).
Proof.
  intros owners process endpoint population.
  destruct (filter (fsem02IsMatchingOwner owners process endpoint) population)
    as [| first remaining] eqn:Hmatches.
  - left. split; [exact Hmatches|].
    now apply fsem02ZeroMatchingEndOwnersHasNoSuccessor.
  - destruct remaining as [| second rest].
    + right. left. exists first. split; [exact Hmatches|].
      unfold fsem02FiniteClose. rewrite Hmatches.
      destruct (fsem02RetireSelectedClientOwner owners first process endpoint)
        as [after|] eqn:Hretire.
      * right. now exists after.
      * now left.
    + right. right. exists first, second, rest.
      split; [exact Hmatches|].
      unfold fsem02FiniteClose.
      now rewrite Hmatches.
Qed.
