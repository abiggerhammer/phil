From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPathPrefixInvariance
  GrammarDeterminacyActualCanonicalPath
  GrammarDeterminacyAlternativeResolverSomeSuffix.

Import ListNotations.
Open Scope string_scope.

(*
  Transport the six-way certified-resolver-Some path classification from the
  full derivation path to the canonical rule-local path carried by the final
  PHIL-SURFACE-DETERM-001 mutual induction.

  All six alternative resolver roots are one-step nonterminal suffixes, so
  #772's singleton-suffix prefix invariance is exactly the needed bridge.
*)

Lemma phase1_surface_actual_canonical_single_nonterminal_suffix :
  forall actual caller_prefix canonical name,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    canonical <> [] ->
    path_has_suffixb actual [AtNonterminal name] =
    path_has_suffixb canonical [AtNonterminal name].
Proof.
  intros actual caller_prefix canonical name Hpath Hnonempty.
  unfold phase1_surface_actual_canonical_path in Hpath.
  subst actual.
  apply path_has_single_nonterminal_suffix_prefix_irrelevant.
  exact Hnonempty.
Qed.

Theorem phase1_surface_actual_canonical_resolver_suffix :
  forall actual caller_prefix canonical,
    phase1_surface_actual_canonical_path
      actual caller_prefix canonical ->
    canonical <> [] ->
    Phase1AlternativeResolverSuffix actual ->
    Phase1AlternativeResolverSuffix canonical.
Proof.
  intros actual caller_prefix canonical Hpath Hnonempty Hsuffix.
  destruct Hsuffix as
      [Hdeclaration
      | Hgeneric
      | Hpattern
      | Hprimary
      | Hproposition
      | Hstatic].
  - apply alternative_resolver_suffix_declaration.
    unfold provider_declaration_suffix in *.
    rewrite
      (phase1_surface_actual_canonical_single_nonterminal_suffix
        actual caller_prefix canonical "declaration"
        Hpath Hnonempty)
      in Hdeclaration.
    exact Hdeclaration.
  - apply alternative_resolver_suffix_generic_requirement.
    unfold generic_requirement_suffix in *.
    rewrite
      (phase1_surface_actual_canonical_single_nonterminal_suffix
        actual caller_prefix canonical "generic_requirement"
        Hpath Hnonempty)
      in Hgeneric.
    exact Hgeneric.
  - apply alternative_resolver_suffix_pattern.
    unfold pattern_suffix in *.
    rewrite
      (phase1_surface_actual_canonical_single_nonterminal_suffix
        actual caller_prefix canonical "pattern"
        Hpath Hnonempty)
      in Hpattern.
    exact Hpattern.
  - apply alternative_resolver_suffix_primary_expression.
    unfold primary_expression_suffix in *.
    rewrite
      (phase1_surface_actual_canonical_single_nonterminal_suffix
        actual caller_prefix canonical "primary_expression"
        Hpath Hnonempty)
      in Hprimary.
    exact Hprimary.
  - apply alternative_resolver_suffix_proposition_atom.
    unfold proposition_atom_suffix in *.
    rewrite
      (phase1_surface_actual_canonical_single_nonterminal_suffix
        actual caller_prefix canonical "proposition_atom"
        Hpath Hnonempty)
      in Hproposition.
    exact Hproposition.
  - apply alternative_resolver_suffix_static_argument.
    unfold static_argument_suffix in *.
    rewrite
      (phase1_surface_actual_canonical_single_nonterminal_suffix
        actual caller_prefix canonical "static_argument"
        Hpath Hnonempty)
      in Hstatic.
    exact Hstatic.
Qed.
