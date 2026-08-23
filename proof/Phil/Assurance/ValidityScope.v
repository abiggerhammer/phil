From Stdlib Require Import Arith.PeanoNat.

(*
  PHIL-ASSURE-VALIDITY-001 — validity-scope authority is dimension-exact.

  Phil.Assurance.Verify implements ValidityScope as a finite set of required
  key/value dimensions.  An evidence/assumption/export scope matches an
  effective manifest context iff every dimension bound by that scope has the
  exact expected value in the effective context.  The effective context may
  contain additional dimensions that the authority did not bind.

  This normalized model proves the two important halves of that rule:

  - authority cannot be transferred across a context that changes any bound
    dimension (in particular target/profile when those dimensions are bound);
  - changing an unbound dimension does not invalidate authority, because the
    authority made no claim about that dimension.

  Strengthening a scope adds requirements rather than authority: if a stronger
  scope matches, every weaker subset of its requirements also matches.  The
  converse is deliberately not available.

  Concrete Text/Map correspondence and the implementation of scopeMatches in
  Phil.Assurance.Verify remain reviewed implementation boundaries.
*)

Definition ValidityDimension := nat.
Definition ValidityValue := nat.
Definition ValidityMap := ValidityDimension -> option ValidityValue.

Definition ScopeMatches
  (scope effective : ValidityMap) : Prop :=
  forall dimension expected,
    scope dimension = Some expected ->
    effective dimension = Some expected.

Theorem matching_scope_preserves_every_bound_dimension :
  forall scope effective dimension expected,
    ScopeMatches scope effective ->
    scope dimension = Some expected ->
    effective dimension = Some expected.
Proof.
  intros scope effective dimension expected Hmatches Hbound.
  eapply Hmatches.
  exact Hbound.
Qed.

Theorem changed_bound_dimension_cannot_match :
  forall scope effective dimension expected,
    scope dimension = Some expected ->
    effective dimension <> Some expected ->
    ~ ScopeMatches scope effective.
Proof.
  intros scope effective dimension expected Hbound Hchanged Hmatches.
  apply Hchanged.
  eapply matching_scope_preserves_every_bound_dimension; eauto.
Qed.

Theorem evidence_cannot_cross_changed_bound_dimension :
  forall scope oldContext newContext dimension expected,
    ScopeMatches scope oldContext ->
    scope dimension = Some expected ->
    newContext dimension <> Some expected ->
    ~ ScopeMatches scope newContext.
Proof.
  intros scope oldContext newContext dimension expected _ Hbound Hchanged.
  eapply changed_bound_dimension_cannot_match; eauto.
Qed.

(* Target and compilation profile are not magically special to ScopeMatches;
   these corollaries name the two dimensions that proof-bound translation
   certificates intentionally bind. *)

Definition TargetDimension : ValidityDimension := 0.
Definition CompilationProfileDimension : ValidityDimension := 1.

Theorem bound_target_change_invalidates_authority :
  forall scope oldContext newContext expectedTarget,
    ScopeMatches scope oldContext ->
    scope TargetDimension = Some expectedTarget ->
    newContext TargetDimension <> Some expectedTarget ->
    ~ ScopeMatches scope newContext.
Proof.
  intros.
  eapply evidence_cannot_cross_changed_bound_dimension; eauto.
Qed.

Theorem bound_compilation_profile_change_invalidates_authority :
  forall scope oldContext newContext expectedProfile,
    ScopeMatches scope oldContext ->
    scope CompilationProfileDimension = Some expectedProfile ->
    newContext CompilationProfileDimension <> Some expectedProfile ->
    ~ ScopeMatches scope newContext.
Proof.
  intros.
  eapply evidence_cannot_cross_changed_bound_dimension; eauto.
Qed.

Definition ContextDiffersOnlyAt
  (changed : ValidityDimension)
  (before after : ValidityMap) : Prop :=
  forall dimension,
    dimension <> changed ->
    before dimension = after dimension.

Theorem unbound_dimension_change_preserves_match :
  forall scope before after changed,
    ScopeMatches scope before ->
    scope changed = None ->
    ContextDiffersOnlyAt changed before after ->
    ScopeMatches scope after.
Proof.
  intros scope before after changed Hmatches Hunbound Honly.
  unfold ScopeMatches.
  intros dimension expected Hscope.
  destruct (Nat.eq_dec dimension changed) as [Heq | Hneq].
  - subst dimension.
    rewrite Hunbound in Hscope.
    discriminate.
  - rewrite <- (Honly dimension Hneq).
    eapply Hmatches.
    exact Hscope.
Qed.

Definition ScopeStrengthens
  (stronger weaker : ValidityMap) : Prop :=
  forall dimension expected,
    weaker dimension = Some expected ->
    stronger dimension = Some expected.

Theorem stronger_scope_match_implies_weaker_scope_match :
  forall stronger weaker effective,
    ScopeStrengthens stronger weaker ->
    ScopeMatches stronger effective ->
    ScopeMatches weaker effective.
Proof.
  intros stronger weaker effective Hstrengthens Hstrong.
  unfold ScopeMatches.
  intros dimension expected HweakBound.
  eapply Hstrong.
  eapply Hstrengthens.
  exact HweakBound.
Qed.

Theorem strengthening_scope_cannot_excuse_new_mismatch :
  forall stronger weaker effective dimension expected,
    ScopeStrengthens stronger weaker ->
    stronger dimension = Some expected ->
    effective dimension <> Some expected ->
    ~ ScopeMatches stronger effective.
Proof.
  intros stronger weaker effective dimension expected _ Hbound Hmismatch.
  eapply changed_bound_dimension_cannot_match; eauto.
Qed.

(* A scope that binds nothing contributes no validity-context restriction. *)
Definition EmptyScope : ValidityMap := fun _ => None.

Theorem empty_scope_matches_every_context :
  forall effective,
    ScopeMatches EmptyScope effective.
Proof.
  intros effective dimension expected Hbound.
  unfold EmptyScope in Hbound.
  discriminate.
Qed.
