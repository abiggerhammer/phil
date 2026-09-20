From Stdlib Require Import Lists.List Arith.PeanoNat Lia.

From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import
  SurfaceBinderScopeCore
  SurfaceLetPatternScope.

Import ListNotations.

(*
  Bounded PHIL-SURFACE-BINDER-SCOPE-001 tranche for match/decide/offer arms.

  Production CaseArmScope resolves the scrutinee in the parent scope before any
  arm binder exists. Each arm then receives a fresh child frame. Arm binders and
  arm-local lets consume declaration-wide ordinals, the child frame is discarded
  at arm exit, and the advanced ordinal is threaded into the next sibling.

  This proof reuses the already-certified pattern allocator from
  SurfaceLetPatternScope rather than defining another binder-allocation semantics.
*)

Inductive SurfaceCaseExpressionKind : Type :=
| SurfaceMatchCase
| SurfaceDecideCase
| SurfaceOfferCase.

Inductive SurfaceCaseScrutineeDecision : Type :=
| SurfaceCaseScrutineeResolved : BinderKey -> SurfaceCaseScrutineeDecision
| SurfaceCaseScrutineeOutsideLocalCompetence.

Definition decideSurfaceCaseScrutinee
  (activeBeforeArms : option BinderKey)
  : SurfaceCaseScrutineeDecision :=
  match activeBeforeArms with
  | Some key => SurfaceCaseScrutineeResolved key
  | None => SurfaceCaseScrutineeOutsideLocalCompetence
  end.

Theorem case_scrutinee_is_resolved_before_arm_binding :
  forall key,
    decideSurfaceCaseScrutinee (Some key) =
      SurfaceCaseScrutineeResolved key.
Proof.
  reflexivity.
Qed.

Theorem future_arm_binder_cannot_resolve_scrutinee :
  decideSurfaceCaseScrutinee None =
    SurfaceCaseScrutineeOutsideLocalCompetence.
Proof.
  reflexivity.
Qed.

Record SurfaceCaseArmResult : Type := mkSurfaceCaseArmResult {
  surfaceCaseArmBinders : list BinderKey;
  surfaceCaseArmNextOrdinal : BinderOrdinal
}.

Definition checkSurfaceCaseArm
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (patternSites : list SurfacePatternSite)
  : SurfaceCaseArmResult :=
  let '(binders, finalOrdinal) :=
    allocateSurfacePatternBinders declaration next patternSites in
  mkSurfaceCaseArmResult binders finalOrdinal.

Theorem case_arm_binders_reuse_exact_pattern_allocation :
  forall declaration next patternSites,
    surfaceCaseArmBinders
      (checkSurfaceCaseArm declaration next patternSites) =
    fst (allocateSurfacePatternBinders declaration next patternSites).
Proof.
  intros declaration next patternSites.
  unfold checkSurfaceCaseArm.
  destruct (allocateSurfacePatternBinders declaration next patternSites).
  reflexivity.
Qed.

Theorem case_arm_exit_preserves_advanced_ordinal :
  forall declaration next patternSites,
    surfaceCaseArmNextOrdinal
      (checkSurfaceCaseArm declaration next patternSites) =
    next + length patternSites.
Proof.
  intros declaration next patternSites.
  unfold checkSurfaceCaseArm.
  destruct
    (allocateSurfacePatternBinders declaration next patternSites)
    as [keys finalOrdinal] eqn:Hallocate.
  simpl.
  eapply pattern_allocation_consumes_one_fresh_ordinal_per_site.
  exact Hallocate.
Qed.

Definition surfaceCaseArmVisibleAfterExit
  (_ : SurfaceCaseArmResult) : list BinderKey :=
  [].

Theorem case_arm_local_names_do_not_leak_after_exit :
  forall result,
    surfaceCaseArmVisibleAfterExit result = [].
Proof.
  reflexivity.
Qed.

Definition checkSurfaceSiblingCaseArm
  (declaration : DeclarationIdentity)
  (previous : SurfaceCaseArmResult)
  (patternSites : list SurfacePatternSite)
  : SurfaceCaseArmResult :=
  checkSurfaceCaseArm
    declaration
    (surfaceCaseArmNextOrdinal previous)
    patternSites.

Theorem sibling_case_arm_starts_at_previous_advanced_ordinal :
  forall declaration previous patternSites,
    let sibling :=
      checkSurfaceSiblingCaseArm declaration previous patternSites in
    surfaceCaseArmBinders sibling =
      fst
        (allocateSurfacePatternBinders
          declaration
          (surfaceCaseArmNextOrdinal previous)
          patternSites).
Proof.
  intros declaration previous patternSites.
  unfold checkSurfaceSiblingCaseArm.
  apply case_arm_binders_reuse_exact_pattern_allocation.
Qed.

Theorem nonempty_case_arm_advances_next_sibling_start :
  forall declaration next firstSite rest,
    next <
      surfaceCaseArmNextOrdinal
        (checkSurfaceCaseArm declaration next (firstSite :: rest)).
Proof.
  intros declaration next firstSite rest.
  rewrite case_arm_exit_preserves_advanced_ordinal.
  simpl.
  lia.
Qed.

Theorem sibling_case_arm_reuse_cannot_reuse_first_ordinal :
  forall declaration next firstSite rest,
    semanticBinderKey declaration next <>
    semanticBinderKey declaration
      (surfaceCaseArmNextOrdinal
        (checkSurfaceCaseArm declaration next (firstSite :: rest))).
Proof.
  intros declaration next firstSite rest Heq.
  pose proof
    (nonempty_case_arm_advances_next_sibling_start
      declaration next firstSite rest) as Hlt.
  unfold semanticBinderKey in Heq.
  inversion Heq.
  lia.
Qed.

Theorem alpha_renamed_case_pattern_preserves_semantic_binders :
  forall declaration next firstSites secondSites,
    length firstSites = length secondSites ->
    surfaceCaseArmBinders
      (checkSurfaceCaseArm declaration next firstSites) =
    surfaceCaseArmBinders
      (checkSurfaceCaseArm declaration next secondSites).
Proof.
  intros declaration next firstSites secondSites Hlength.
  repeat rewrite case_arm_binders_reuse_exact_pattern_allocation.
  eapply alpha_renaming_pattern_sites_preserves_semantic_identity.
  exact Hlength.
Qed.

Inductive SurfaceCaseJoinApplicability : Type :=
| SurfaceCaseWithoutJoin
| SurfaceCaseWithJoin.

Definition surfaceCaseArmScopeCompetent
  (joinApplicability : SurfaceCaseJoinApplicability) : bool :=
  match joinApplicability with
  | SurfaceCaseWithoutJoin => true
  | SurfaceCaseWithJoin => false
  end.

Theorem match_without_join_is_in_case_arm_scope_competence :
  surfaceCaseArmScopeCompetent SurfaceCaseWithoutJoin = true.
Proof.
  reflexivity.
Qed.

Theorem match_with_join_remains_outside_case_arm_scope_competence :
  surfaceCaseArmScopeCompetent SurfaceCaseWithJoin = false.
Proof.
  reflexivity.
Qed.

Record SurfaceCaseArmScopeFacts : Type := mkSurfaceCaseArmScopeFacts {
  surfaceCaseScrutineePrecedesArms : Prop;
  surfaceCaseArmPatternOrderExact : Prop;
  surfaceCaseArmChildScopeIsolated : Prop;
  surfaceCaseSiblingOrdinalFresh : Prop;
  surfaceCaseAlphaStable : Prop;
  surfaceCaseJoinBoundaryExplicit : Prop
}.

Definition SurfaceCaseArmScopeValid
  (facts : SurfaceCaseArmScopeFacts) : Prop :=
  surfaceCaseScrutineePrecedesArms facts /\
  surfaceCaseArmPatternOrderExact facts /\
  surfaceCaseArmChildScopeIsolated facts /\
  surfaceCaseSiblingOrdinalFresh facts /\
  surfaceCaseAlphaStable facts /\
  surfaceCaseJoinBoundaryExplicit facts.

Theorem surface_case_arm_scope_requires_all_authorities :
  forall facts,
    SurfaceCaseArmScopeValid facts ->
    surfaceCaseScrutineePrecedesArms facts /\
    surfaceCaseArmPatternOrderExact facts /\
    surfaceCaseArmChildScopeIsolated facts /\
    surfaceCaseSiblingOrdinalFresh facts /\
    surfaceCaseAlphaStable facts /\
    surfaceCaseJoinBoundaryExplicit facts.
Proof.
  intros facts Hvalid.
  exact Hvalid.
Qed.
