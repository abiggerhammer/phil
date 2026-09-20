From Stdlib Require Import Lists.List Arith.PeanoNat.
From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import SurfaceBinderScopeCore.

Import ListNotations.

(*
  Bounded PHIL-SURFACE-BINDER-SCOPE-001 tranche for let/pattern binders.

  Production PatternBinderScope first projects one source pattern to binder sites
  in exact source preorder, then allocates each site through the already-certified
  term-binder authority. LetPatternScope resolves the initializer in the
  pre-binding scope and only then allocates the pattern binders.

  The concrete parser tree, Text spellings, record labels, SourceSpan values,
  and Haskell traversal remain correspondence boundaries. This theorem models
  only the semantic ordering/identity discipline.
*)

Definition SurfacePatternSite := nat.

Fixpoint allocateSurfacePatternBinders
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (sites : list SurfacePatternSite)
  : list BinderKey * BinderOrdinal :=
  match sites with
  | [] => ([], next)
  | _ :: rest =>
      let '(restKeys, finalOrdinal) :=
        allocateSurfacePatternBinders declaration (S next) rest in
      (semanticBinderKey declaration next :: restKeys, finalOrdinal)
  end.

Theorem empty_pattern_allocates_nothing :
  forall declaration next,
    allocateSurfacePatternBinders declaration next [] = ([], next).
Proof.
  reflexivity.
Qed.

Theorem pattern_allocation_preserves_first_source_position :
  forall declaration next site rest keys finalOrdinal,
    allocateSurfacePatternBinders declaration (S next) rest =
      (keys, finalOrdinal) ->
    allocateSurfacePatternBinders declaration next (site :: rest) =
      (semanticBinderKey declaration next :: keys, finalOrdinal).
Proof.
  intros declaration next site rest keys finalOrdinal Hrest.
  simpl.
  rewrite Hrest.
  reflexivity.
Qed.

Theorem pattern_allocation_consumes_one_fresh_ordinal_per_site :
  forall declaration next sites keys finalOrdinal,
    allocateSurfacePatternBinders declaration next sites =
      (keys, finalOrdinal) ->
    finalOrdinal = next + length sites.
Proof.
  intros declaration next sites.
  revert next.
  induction sites as [|site rest IH]; intros next keys finalOrdinal Hallocate.
  - simpl in Hallocate.
    inversion Hallocate.
    simpl.
    reflexivity.
  - simpl in Hallocate.
    destruct
      (allocateSurfacePatternBinders declaration (S next) rest)
      as [restKeys restFinal] eqn:Hrest.
    inversion Hallocate; subst keys finalOrdinal.
    specialize (IH (S next) restKeys restFinal Hrest).
    simpl.
    rewrite IH.
    rewrite Nat.add_succ_l.
    reflexivity.
Qed.

Theorem pattern_allocation_preserves_binder_count :
  forall declaration next sites,
    length
      (fst (allocateSurfacePatternBinders declaration next sites)) =
    length sites.
Proof.
  intros declaration next sites.
  revert next.
  induction sites as [|site rest IH]; intros next.
  - reflexivity.
  - simpl.
    destruct
      (allocateSurfacePatternBinders declaration (S next) rest)
      as [restKeys restFinal] eqn:Hrest.
    simpl.
    pose proof (IH (S next)) as Hlen.
    rewrite Hrest in Hlen.
    simpl in Hlen.
    rewrite Hlen.
    reflexivity.
Qed.

Theorem alpha_renaming_pattern_sites_preserves_semantic_identity :
  forall declaration next firstSites secondSites,
    length firstSites = length secondSites ->
    fst (allocateSurfacePatternBinders declaration next firstSites) =
    fst (allocateSurfacePatternBinders declaration next secondSites).
Proof.
  intros declaration next firstSites.
  revert next.
  induction firstSites as [|first rest IH]; intros next secondSites Hlength.
  - destruct secondSites; simpl in Hlength |- *.
    + reflexivity.
    + discriminate Hlength.
  - destruct secondSites as [|second secondRest].
    + discriminate Hlength.
    + simpl in Hlength.
      injection Hlength as HrestLength.
      simpl.
      destruct
        (allocateSurfacePatternBinders declaration (S next) rest)
        as [firstKeys firstFinal] eqn:Hfirst.
      destruct
        (allocateSurfacePatternBinders declaration (S next) secondRest)
        as [secondKeys secondFinal] eqn:Hsecond.
      simpl.
      pose proof (IH (S next) secondRest HrestLength) as Hkeys.
      rewrite Hfirst in Hkeys.
      rewrite Hsecond in Hkeys.
      simpl in Hkeys.
      rewrite Hkeys.
      reflexivity.
Qed.

Inductive SurfaceLetInitializerDecision : Type :=
| SurfaceLetInitializerResolved : BinderKey -> SurfaceLetInitializerDecision
| SurfaceLetInitializerOutsideLocalCompetence.

Definition decideSurfaceLetInitializer
  (activeBeforeBinding : option BinderKey)
  : SurfaceLetInitializerDecision :=
  match activeBeforeBinding with
  | Some key => SurfaceLetInitializerResolved key
  | None => SurfaceLetInitializerOutsideLocalCompetence
  end.

Record SurfaceLetScopeResult : Type := mkSurfaceLetScopeResult {
  surfaceLetInitializerDecision : SurfaceLetInitializerDecision;
  surfaceLetPatternBinders : list BinderKey;
  surfaceLetNextOrdinal : BinderOrdinal
}.

Definition checkSurfaceLetStep
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (initializerBeforeBinding : option BinderKey)
  (patternSites : list SurfacePatternSite)
  : SurfaceLetScopeResult :=
  let '(binders, finalOrdinal) :=
    allocateSurfacePatternBinders declaration next patternSites in
  mkSurfaceLetScopeResult
    (decideSurfaceLetInitializer initializerBeforeBinding)
    binders
    finalOrdinal.

Theorem let_initializer_is_resolved_before_pattern_allocation :
  forall declaration next initializer patternSites,
    surfaceLetInitializerDecision
      (checkSurfaceLetStep declaration next initializer patternSites) =
    decideSurfaceLetInitializer initializer.
Proof.
  intros declaration next initializer patternSites.
  unfold checkSurfaceLetStep.
  destruct (allocateSurfacePatternBinders declaration next patternSites).
  reflexivity.
Qed.

Theorem future_let_binder_cannot_make_initializer_resolve :
  forall declaration next patternSites,
    surfaceLetInitializerDecision
      (checkSurfaceLetStep declaration next None patternSites) =
    SurfaceLetInitializerOutsideLocalCompetence.
Proof.
  intros declaration next patternSites.
  rewrite let_initializer_is_resolved_before_pattern_allocation.
  reflexivity.
Qed.

Theorem existing_initializer_binder_is_preserved_exactly :
  forall declaration next key patternSites,
    surfaceLetInitializerDecision
      (checkSurfaceLetStep declaration next (Some key) patternSites) =
    SurfaceLetInitializerResolved key.
Proof.
  intros declaration next key patternSites.
  rewrite let_initializer_is_resolved_before_pattern_allocation.
  reflexivity.
Qed.

Theorem let_pattern_allocation_preserves_exact_generated_identities :
  forall declaration next initializer patternSites,
    surfaceLetPatternBinders
      (checkSurfaceLetStep declaration next initializer patternSites) =
    fst (allocateSurfacePatternBinders declaration next patternSites).
Proof.
  intros declaration next initializer patternSites.
  unfold checkSurfaceLetStep.
  destruct (allocateSurfacePatternBinders declaration next patternSites).
  reflexivity.
Qed.

Theorem let_pattern_next_ordinal_is_monotonic :
  forall declaration next initializer patternSites,
    surfaceLetNextOrdinal
      (checkSurfaceLetStep declaration next initializer patternSites) =
    next + length patternSites.
Proof.
  intros declaration next initializer patternSites.
  unfold checkSurfaceLetStep.
  destruct
    (allocateSurfacePatternBinders declaration next patternSites)
    as [keys finalOrdinal] eqn:Hallocate.
  simpl.
  eapply pattern_allocation_consumes_one_fresh_ordinal_per_site.
  exact Hallocate.
Qed.
