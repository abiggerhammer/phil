From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import AuthorityAttenuation.

(*
  PHIL-AUTH-ATTEN-IMPL-001 — representation-neutral executable acceptance
  kernels for Certified PHIL-AUTH-ATTEN-001.

  Concrete Text/Set/list operations stay native.  Production reflects their
  exact semantic facts into Booleans; the extracted kernel owns final semantic
  acceptance.  Handwritten diagnostics may explain a rejection but may not turn
  a kernel rejection into success.
*)

Definition decideExplicitAuthorityAttenuation
  (subjectMatches noWiden witnessSourceMatches witnessTargetMatches
   witnessSubjectMatches witnessOperationsMatch : bool) : bool :=
  andb subjectMatches
    (andb noWiden
      (andb witnessSourceMatches
        (andb witnessTargetMatches
          (andb witnessSubjectMatches witnessOperationsMatch)))).

Theorem explicit_authority_attenuation_decision_accept_iff_certified :
  forall source target witness
         subjectMatches noWiden witnessSourceMatches witnessTargetMatches
         witnessSubjectMatches witnessOperationsMatch,
    (subjectMatches = true <->
      surfaceSubject source = surfaceSubject target) ->
    (noWiden = true <-> operationSubset source target) ->
    (witnessSourceMatches = true <->
      witnessSourceContract witness = surfaceContract source) ->
    (witnessTargetMatches = true <->
      witnessTargetContract witness = surfaceContract target) ->
    (witnessSubjectMatches = true <->
      witnessSubject witness = surfaceSubject target) ->
    (witnessOperationsMatch = true <->
      sameOperationSet
        (witnessVisibleOperations witness)
        (surfaceOperations target)) ->
    decideExplicitAuthorityAttenuation
      subjectMatches noWiden witnessSourceMatches witnessTargetMatches
      witnessSubjectMatches witnessOperationsMatch = true <->
    exactAuthorityAttenuation source target witness.
Proof.
  intros source target witness
    subjectMatches noWiden witnessSourceMatches witnessTargetMatches
    witnessSubjectMatches witnessOperationsMatch
    Hsubject Hwiden Hsource Htarget HwitnessSubject Hoperations.
  unfold decideExplicitAuthorityAttenuation, exactAuthorityAttenuation.
  repeat rewrite andb_true_iff.
  rewrite Hsubject, Hwiden, Hsource, Htarget, HwitnessSubject, Hoperations.
  reflexivity.
Qed.

Definition decideAuthorityBoundary
  (subjectMatches noWiden sameContract sameSurface
   changedContract attenuationWitnessValid : bool) : bool :=
  andb subjectMatches
    (andb noWiden
      (orb
        (andb sameContract sameSurface)
        (andb changedContract attenuationWitnessValid))).

Theorem authority_boundary_decision_accept_iff_certified :
  forall kind available visible maybeWitness
         subjectMatches noWiden sameContract sameSurface
         changedContract attenuationWitnessValid,
    (subjectMatches = true <->
      surfaceSubject available = surfaceSubject visible) ->
    (noWiden = true <-> operationSubset available visible) ->
    (sameContract = true <->
      surfaceContract available = surfaceContract visible) ->
    (sameSurface = true <->
      sameOperationSet
        (surfaceOperations available)
        (surfaceOperations visible)) ->
    (changedContract = true <->
      surfaceContract available <> surfaceContract visible) ->
    (attenuationWitnessValid = true <->
      exists witness,
        maybeWitness = Some witness /\
        exactAuthorityAttenuation available visible witness) ->
    decideAuthorityBoundary
      subjectMatches noWiden sameContract sameSurface
      changedContract attenuationWitnessValid = true <->
    authorityBoundaryAllowed kind available visible maybeWitness.
Proof.
  intros kind available visible maybeWitness
    subjectMatches noWiden sameContract sameSurface
    changedContract attenuationWitnessValid
    Hsubject Hwiden HsameContract HsameSurface
    HchangedContract Hattenuation.
  unfold decideAuthorityBoundary, authorityBoundaryAllowed.
  repeat rewrite andb_true_iff.
  rewrite orb_true_iff.
  repeat rewrite andb_true_iff.
  rewrite Hsubject, Hwiden, HsameContract, HsameSurface,
          HchangedContract, Hattenuation.
  reflexivity.
Qed.

Definition decideAuthorityJoin
  (hasContinuingBranch subjectsMatch contractsMatch operationsDoNotWiden : bool)
  : bool :=
  andb hasContinuingBranch
    (andb subjectsMatch
      (andb contractsMatch operationsDoNotWiden)).

Theorem authority_join_decision_accept_iff_certified :
  forall branches continues joined
         hasContinuingBranch subjectsMatch contractsMatch operationsDoNotWiden,
    (hasContinuingBranch = true <->
      exists branch, continues branch = true) ->
    (subjectsMatch = true <->
      forall branch,
        continues branch = true ->
        surfaceSubject (branches branch) = surfaceSubject joined) ->
    (contractsMatch = true <->
      forall branch,
        continues branch = true ->
        surfaceContract (branches branch) = surfaceContract joined) ->
    (operationsDoNotWiden = true <->
      forall branch operation,
        continues branch = true ->
        surfaceOperations joined operation = true ->
        surfaceOperations (branches branch) operation = true) ->
    decideAuthorityJoin
      hasContinuingBranch subjectsMatch contractsMatch operationsDoNotWiden = true <->
    authorityJoinAllowed branches continues joined.
Proof.
  intros branches continues joined
    hasContinuingBranch subjectsMatch contractsMatch operationsDoNotWiden
    Hcontinuing Hsubjects Hcontracts Hoperations.
  unfold decideAuthorityJoin, authorityJoinAllowed.
  repeat rewrite andb_true_iff.
  rewrite Hcontinuing, Hsubjects, Hcontracts, Hoperations.
  reflexivity.
Qed.
