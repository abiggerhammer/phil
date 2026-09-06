From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyStructuralResolvers.

Import ListNotations.
Open Scope string_scope.

(*
  FOLLOW compatibility for the two resolver roots whose oracle-assembly
  context depends on the current local FOLLOW.

  The final ordinary-derivation -> predictive-oracle induction resets its
  canonical path and FOLLOW at every nonterminal.  At [pattern] and
  [proposition_atom], that reset gives exactly the generated rule FOLLOW.
  After any structural descent, a path can no longer end in either singleton
  nonterminal suffix, so the compatibility obligations become vacuous.
*)

Definition phase1_surface_resolver_follow_compatible
  (path : SyntaxPath)
  (outer_follow : list OverlapToken) : Prop :=
  (path_has_suffixb path pattern_suffix = true ->
    outer_follow =
      lookup_tokens "pattern" phase1_surface_follow_facts) /\
  (path_has_suffixb path proposition_atom_suffix = true ->
    outer_follow =
      lookup_tokens "proposition_atom" phase1_surface_follow_facts).

Lemma path_has_single_nonterminal_suffix_sequence_false :
  forall path index name,
    path_has_suffixb
      (descend path (AtSequence index))
      [AtNonterminal name] = false.
Proof.
  intros path index name.
  unfold descend, path_has_suffixb.
  rewrite List.rev_app_distr.
  simpl.
  reflexivity.
Qed.

Lemma path_has_single_nonterminal_suffix_alternative_false :
  forall path index name,
    path_has_suffixb
      (descend path (AtAlternative index))
      [AtNonterminal name] = false.
Proof.
  intros path index name.
  unfold descend, path_has_suffixb.
  rewrite List.rev_app_distr.
  simpl.
  reflexivity.
Qed.

Lemma path_has_single_nonterminal_suffix_optional_false :
  forall path name,
    path_has_suffixb
      (descend path AtOptionalBody)
      [AtNonterminal name] = false.
Proof.
  intros path name.
  unfold descend, path_has_suffixb.
  rewrite List.rev_app_distr.
  simpl.
  reflexivity.
Qed.

Lemma path_has_single_nonterminal_suffix_repetition_false :
  forall path name,
    path_has_suffixb
      (descend path AtRepetitionBody)
      [AtNonterminal name] = false.
Proof.
  intros path name.
  unfold descend, path_has_suffixb.
  rewrite List.rev_app_distr.
  simpl.
  reflexivity.
Qed.

Theorem phase1_surface_nonterminal_reset_resolver_follow_compatible :
  forall name,
    phase1_surface_resolver_follow_compatible
      [AtNonterminal name]
      (lookup_tokens name phase1_surface_follow_facts).
Proof.
  intros name.
  unfold phase1_surface_resolver_follow_compatible.
  split.
  - intro Hpattern.
    unfold pattern_suffix, path_has_suffixb in Hpattern.
    simpl in Hpattern.
    apply String.eqb_eq in Hpattern.
    subst name.
    reflexivity.
  - intro Hproposition.
    unfold proposition_atom_suffix, path_has_suffixb in Hproposition.
    simpl in Hproposition.
    apply String.eqb_eq in Hproposition.
    subst name.
    reflexivity.
Qed.

Theorem phase1_surface_sequence_descend_resolver_follow_compatible :
  forall path outer_follow index,
    phase1_surface_resolver_follow_compatible
      (descend path (AtSequence index)) outer_follow.
Proof.
  intros path outer_follow index.
  unfold phase1_surface_resolver_follow_compatible.
  split; intro Hsuffix.
  - unfold pattern_suffix in Hsuffix.
    rewrite path_has_single_nonterminal_suffix_sequence_false in Hsuffix.
    discriminate Hsuffix.
  - unfold proposition_atom_suffix in Hsuffix.
    rewrite path_has_single_nonterminal_suffix_sequence_false in Hsuffix.
    discriminate Hsuffix.
Qed.

Theorem phase1_surface_alternative_descend_resolver_follow_compatible :
  forall path outer_follow index,
    phase1_surface_resolver_follow_compatible
      (descend path (AtAlternative index)) outer_follow.
Proof.
  intros path outer_follow index.
  unfold phase1_surface_resolver_follow_compatible.
  split; intro Hsuffix.
  - unfold pattern_suffix in Hsuffix.
    rewrite path_has_single_nonterminal_suffix_alternative_false in Hsuffix.
    discriminate Hsuffix.
  - unfold proposition_atom_suffix in Hsuffix.
    rewrite path_has_single_nonterminal_suffix_alternative_false in Hsuffix.
    discriminate Hsuffix.
Qed.

Theorem phase1_surface_optional_descend_resolver_follow_compatible :
  forall path outer_follow,
    phase1_surface_resolver_follow_compatible
      (descend path AtOptionalBody) outer_follow.
Proof.
  intros path outer_follow.
  unfold phase1_surface_resolver_follow_compatible.
  split; intro Hsuffix.
  - unfold pattern_suffix in Hsuffix.
    rewrite path_has_single_nonterminal_suffix_optional_false in Hsuffix.
    discriminate Hsuffix.
  - unfold proposition_atom_suffix in Hsuffix.
    rewrite path_has_single_nonterminal_suffix_optional_false in Hsuffix.
    discriminate Hsuffix.
Qed.

Theorem phase1_surface_repetition_descend_resolver_follow_compatible :
  forall path outer_follow,
    phase1_surface_resolver_follow_compatible
      (descend path AtRepetitionBody) outer_follow.
Proof.
  intros path outer_follow.
  unfold phase1_surface_resolver_follow_compatible.
  split; intro Hsuffix.
  - unfold pattern_suffix in Hsuffix.
    rewrite path_has_single_nonterminal_suffix_repetition_false in Hsuffix.
    discriminate Hsuffix.
  - unfold proposition_atom_suffix in Hsuffix.
    rewrite path_has_single_nonterminal_suffix_repetition_false in Hsuffix.
    discriminate Hsuffix.
Qed.
