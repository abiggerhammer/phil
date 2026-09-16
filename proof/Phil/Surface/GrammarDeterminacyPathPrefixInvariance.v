From Stdlib Require Import Arith.PeanoNat Lists.List Lia.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyOracleAssemblyCoverage.

Import ListNotations.

(*
  Prefix-invariance foundation for the final PHIL-SURFACE-DETERM-001 mutual
  induction.

  Ordinary derivations retain their complete caller path, while the mechanical
  oracle-assembly checker deliberately resets at each nonterminal and checks a
  canonical rule-local path beginning with [AtNonterminal name].  Resolver
  classification is suffix-based, so the final induction needs small lemmas
  showing when an arbitrary caller prefix is irrelevant.

  This file proves the generic length-bounded suffix fact and instantiates it
  for the six one-step alternative resolver roots.  The latter is the seam
  needed to consume canonical rule-local assembly coverage while making the
  predictive-oracle decision at the derivation's full path.
*)

Lemma reversed_path_prefixb_append_irrelevant :
  forall expected actual extra,
    List.length expected <= List.length actual ->
    reversed_path_prefixb expected (actual ++ extra) =
    reversed_path_prefixb expected actual.
Proof.
  induction expected as [| expected_step expected_rest IH];
    intros actual extra Hlength.
  - reflexivity.
  - destruct actual as [| actual_step actual_rest].
    + simpl in Hlength.
      lia.
    + simpl in Hlength.
      simpl.
      rewrite IH by lia.
      reflexivity.
Qed.

Lemma path_has_suffixb_prefix_irrelevant_when_long_enough :
  forall prefix path suffix,
    List.length suffix <= List.length path ->
    path_has_suffixb (prefix ++ path) suffix =
    path_has_suffixb path suffix.
Proof.
  intros prefix path suffix Hlength.
  unfold path_has_suffixb.
  rewrite List.rev_app_distr.
  apply reversed_path_prefixb_append_irrelevant.
  repeat rewrite List.length_rev.
  exact Hlength.
Qed.

Lemma path_has_single_nonterminal_suffix_prefix_irrelevant :
  forall prefix path name,
    path <> [] ->
    path_has_suffixb
      (prefix ++ path) [AtNonterminal name] =
    path_has_suffixb path [AtNonterminal name].
Proof.
  intros prefix path name Hnonempty.
  apply path_has_suffixb_prefix_irrelevant_when_long_enough.
  destruct path as [| head tail].
  - contradiction.
  - simpl.
    lia.
Qed.

Lemma descend_prefix_commutes :
  forall prefix path step,
    descend (prefix ++ path) step =
    prefix ++ descend path step.
Proof.
  intros prefix path step.
  unfold descend.
  rewrite List.app_assoc.
  reflexivity.
Qed.

Theorem alternative_resolver_contextb_prefix_irrelevant :
  forall prefix path outer_follow,
    path <> [] ->
    alternative_resolver_contextb
      (prefix ++ path) outer_follow =
    alternative_resolver_contextb path outer_follow.
Proof.
  intros prefix path outer_follow Hnonempty.
  unfold alternative_resolver_contextb.
  unfold provider_declaration_suffix,
    generic_requirement_suffix,
    pattern_suffix,
    primary_expression_suffix,
    proposition_atom_suffix,
    static_argument_suffix.
  repeat rewrite
    path_has_single_nonterminal_suffix_prefix_irrelevant
      by exact Hnonempty.
  reflexivity.
Qed.
