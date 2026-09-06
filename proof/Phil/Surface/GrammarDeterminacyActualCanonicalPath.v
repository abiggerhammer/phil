From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyPathPrefixInvariance.

Import ListNotations.

(*
  Actual/canonical path relation for the final PHIL-SURFACE-DETERM-001 mutual
  ordinary-derivation -> predictive-oracle induction.

  Ordinary derivations carry the complete caller path.  The mechanical
  assembly checker carries a canonical rule-local path that is reset at every
  nonterminal.  The induction therefore keeps an explicit caller prefix
  relating the two paths.

  #772 supplied the underlying prefix-invariance facts.  This file packages
  the relation itself, its structural descent law, and the nonterminal reset
  shape so later conversion lemmas can consume them directly.
*)

Definition phase1_surface_actual_canonical_path
  (actual caller_prefix canonical : SyntaxPath) : Prop :=
  actual = caller_prefix ++ canonical.

Lemma phase1_surface_actual_canonical_path_root :
  forall path,
    phase1_surface_actual_canonical_path path [] path.
Proof.
  intros path.
  unfold phase1_surface_actual_canonical_path.
  reflexivity.
Qed.

Lemma phase1_surface_actual_canonical_path_descend :
  forall actual caller_prefix canonical step,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    phase1_surface_actual_canonical_path
      (descend actual step)
      caller_prefix
      (descend canonical step).
Proof.
  intros actual caller_prefix canonical step Hpath.
  unfold phase1_surface_actual_canonical_path in *.
  subst actual.
  apply descend_prefix_commutes.
Qed.

Lemma phase1_surface_actual_canonical_path_resolver_context :
  forall actual caller_prefix canonical outer_follow,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    canonical <> [] ->
    alternative_resolver_contextb actual outer_follow =
    alternative_resolver_contextb canonical outer_follow.
Proof.
  intros actual caller_prefix canonical outer_follow Hpath Hnonempty.
  unfold phase1_surface_actual_canonical_path in Hpath.
  subst actual.
  apply alternative_resolver_contextb_prefix_irrelevant.
  exact Hnonempty.
Qed.

Theorem phase1_surface_actual_canonical_structural_step :
  forall actual caller_prefix canonical step outer_follow,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    phase1_surface_actual_canonical_path
      (descend actual step)
      caller_prefix
      (descend canonical step) /\
    alternative_resolver_contextb
      (descend actual step) outer_follow =
    alternative_resolver_contextb
      (descend canonical step) outer_follow.
Proof.
  intros actual caller_prefix canonical step outer_follow Hpath.
  split.
  - eapply phase1_surface_actual_canonical_path_descend.
    exact Hpath.
  - eapply phase1_surface_actual_canonical_path_resolver_context.
    + eapply phase1_surface_actual_canonical_path_descend.
      exact Hpath.
    + unfold descend.
      destruct canonical; discriminate.
Qed.

Theorem phase1_surface_actual_canonical_nonterminal_reset :
  forall path name outer_follow,
    phase1_surface_actual_canonical_path
      (descend path (AtNonterminal name))
      path
      [AtNonterminal name] /\
    alternative_resolver_contextb
      (descend path (AtNonterminal name)) outer_follow =
    alternative_resolver_contextb
      [AtNonterminal name] outer_follow.
Proof.
  intros path name outer_follow.
  split.
  - unfold phase1_surface_actual_canonical_path, descend.
    reflexivity.
  - unfold descend.
    apply alternative_resolver_contextb_prefix_irrelevant.
    discriminate.
Qed.
