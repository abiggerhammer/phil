From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyOracleAssemblyReflection.

Import ListNotations.
Open Scope string_scope.

(*
  Root classification for the alternative half of the final
  PHIL-SURFACE-DETERM-001 ordinary-derivation -> predictive-oracle bridge.

  Oracle-assembly coverage marks six alternative rule roots as resolver
  contexts.  The final mutual induction should not have to unfold path suffix
  tests or rediscover which generated rule body it is traversing.  This file
  reflects that boolean classification into one small propositional sum.
*)

Lemma path_has_single_nonterminal_suffix_shape :
  forall path name,
    path_has_suffixb path [AtNonterminal name] = true ->
    exists prefix,
      path = List.app prefix [AtNonterminal name].
Proof.
  intros path name Hsuffix.
  unfold path_has_suffixb in Hsuffix.
  simpl in Hsuffix.
  destruct (List.rev path) as [| last reversed] eqn:Hrev.
  - discriminate Hsuffix.
  - destruct last as [actual | index | index | |].
    + simpl in Hsuffix.
      apply andb_true_iff in Hsuffix as [Hname _].
      apply String.eqb_eq in Hname.
      subst actual.
      exists (List.rev reversed).
      pose proof (f_equal (@List.rev SyntaxPathStep) Hrev) as Hshape.
      rewrite List.rev_involutive in Hshape.
      simpl in Hshape.
      exact Hshape.
    + discriminate Hsuffix.
    + discriminate Hsuffix.
    + discriminate Hsuffix.
    + discriminate Hsuffix.
Qed.

Lemma phase1_surface_single_nonterminal_suffix_lookup :
  forall path name expression,
    path_has_suffixb path [AtNonterminal name] = true ->
    phase1_surface_expression_at_path path = Some expression ->
    lookupRule name phase1_surface_rules = Some expression.
Proof.
  intros path name expression Hsuffix Hpath.
  destruct
    (path_has_single_nonterminal_suffix_shape path name Hsuffix)
    as [prefix Hshape].
  subst path.
  pose proof Hpath as Hfinal.
  unfold phase1_surface_expression_at_path in Hpath.
  rewrite expression_at_path_app in Hpath.
  destruct
    (expression_at_path
      phase1_surface_rules phase1_surface_root_expression prefix)
    as [middle |] eqn:Hprefix.
  - destruct middle as
      [literal | class_name | actual | items | items | body | body].
    + discriminate Hpath.
    + discriminate Hpath.
    + change
        (phase1_surface_expression_at_path prefix =
          Some (ENonterminal actual)) in Hprefix.
      pose proof
        (phase1_surface_expression_at_descend
          prefix (ENonterminal actual) (AtNonterminal name) Hprefix)
        as Hstep.
      unfold descend in Hstep.
      rewrite Hfinal in Hstep.
      unfold step_expression in Hstep.
      destruct (String.eqb name actual) eqn:Hname.
      * symmetry.
        exact Hstep.
      * discriminate Hstep.
    + discriminate Hpath.
    + discriminate Hpath.
    + discriminate Hpath.
    + discriminate Hpath.
  - discriminate Hpath.
Qed.

Inductive Phase1AlternativeResolverRoot
  (path : SyntaxPath)
  (outer_follow : list OverlapToken)
  (items : list EbnfExpression) : Prop :=
| alternative_resolver_root_declaration :
    path_has_suffixb path provider_declaration_suffix = true ->
    lookupRule "declaration" phase1_surface_rules =
      Some (EAlternative items) ->
    Phase1AlternativeResolverRoot path outer_follow items
| alternative_resolver_root_generic_requirement :
    path_has_suffixb path generic_requirement_suffix = true ->
    lookupRule "generic_requirement" phase1_surface_rules =
      Some (EAlternative items) ->
    Phase1AlternativeResolverRoot path outer_follow items
| alternative_resolver_root_pattern :
    path_has_suffixb path pattern_suffix = true ->
    lookupRule "pattern" phase1_surface_rules =
      Some (EAlternative items) ->
    outer_follow = lookup_tokens "pattern" phase1_surface_follow_facts ->
    Phase1AlternativeResolverRoot path outer_follow items
| alternative_resolver_root_primary_expression :
    path_has_suffixb path primary_expression_suffix = true ->
    lookupRule "primary_expression" phase1_surface_rules =
      Some (EAlternative items) ->
    Phase1AlternativeResolverRoot path outer_follow items
| alternative_resolver_root_proposition_atom :
    path_has_suffixb path proposition_atom_suffix = true ->
    lookupRule "proposition_atom" phase1_surface_rules =
      Some (EAlternative items) ->
    outer_follow =
      lookup_tokens "proposition_atom" phase1_surface_follow_facts ->
    Phase1AlternativeResolverRoot path outer_follow items
| alternative_resolver_root_static_argument :
    path_has_suffixb path static_argument_suffix = true ->
    lookupRule "static_argument" phase1_surface_rules =
      Some (EAlternative items) ->
    Phase1AlternativeResolverRoot path outer_follow items.

Theorem phase1_surface_alternative_resolver_root_classified :
  forall path outer_follow items,
    phase1_surface_expression_path_context path (EAlternative items) ->
    alternative_resolver_contextb path outer_follow = true ->
    Phase1AlternativeResolverRoot path outer_follow items.
Proof.
  intros path outer_follow items Hpath Hresolver.
  unfold phase1_surface_expression_path_context in Hpath.
  unfold alternative_resolver_contextb in Hresolver.
  destruct
    (path_has_suffixb path provider_declaration_suffix)
    eqn:Hprovider.
  - apply alternative_resolver_root_declaration.
    + exact Hprovider.
    + eapply phase1_surface_single_nonterminal_suffix_lookup.
      * unfold provider_declaration_suffix in Hprovider.
        exact Hprovider.
      * exact Hpath.
  - destruct
      (path_has_suffixb path generic_requirement_suffix)
      eqn:Hgeneric.
    + apply alternative_resolver_root_generic_requirement.
      * exact Hgeneric.
      * eapply phase1_surface_single_nonterminal_suffix_lookup.
        -- unfold generic_requirement_suffix in Hgeneric.
           exact Hgeneric.
        -- exact Hpath.
    + destruct
        (path_has_suffixb path pattern_suffix)
        eqn:Hpattern.
      * apply alternative_resolver_root_pattern.
        -- exact Hpattern.
        -- eapply phase1_surface_single_nonterminal_suffix_lookup.
           ++ unfold pattern_suffix in Hpattern.
              exact Hpattern.
           ++ exact Hpath.
        -- apply assembly_overlap_token_list_eqb_eq.
           exact Hresolver.
      * destruct
          (path_has_suffixb path primary_expression_suffix)
          eqn:Hprimary.
        -- apply alternative_resolver_root_primary_expression.
           ++ exact Hprimary.
           ++ eapply phase1_surface_single_nonterminal_suffix_lookup.
              ** unfold primary_expression_suffix in Hprimary.
                 exact Hprimary.
              ** exact Hpath.
        -- destruct
            (path_has_suffixb path proposition_atom_suffix)
            eqn:Hproposition.
           ++ apply alternative_resolver_root_proposition_atom.
              ** exact Hproposition.
              ** eapply phase1_surface_single_nonterminal_suffix_lookup.
                 --- unfold proposition_atom_suffix in Hproposition.
                     exact Hproposition.
                 --- exact Hpath.
              ** apply assembly_overlap_token_list_eqb_eq.
                 exact Hresolver.
           ++ destruct
                (path_has_suffixb path static_argument_suffix)
                eqn:Hstatic.
              ** apply alternative_resolver_root_static_argument.
                 --- exact Hstatic.
                 --- eapply phase1_surface_single_nonterminal_suffix_lookup.
                     +++ unfold static_argument_suffix in Hstatic.
                         exact Hstatic.
                     +++ exact Hpath.
              ** discriminate Hresolver.
Qed.
