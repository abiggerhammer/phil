From Stdlib Require Import Bool.Bool Lists.List.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyDerivationPathSoundness
  GrammarDeterminacyAlternativeTrailingCommaExclusion.

(*
  Path-only classification for the certified-resolver-Some half of the final
  PHIL-SURFACE-DETERM-001 alternative conversion.

  #781 proves that no valid EAlternative path can be one of the five
  trailing-comma repetition sites.  The combined certified resolver therefore
  has only six possible path families left when it returns Some at an
  alternative node.  Keep this fact independent of outer FOLLOW so the final
  conversion can supply the FOLLOW invariant separately.
*)

Inductive Phase1AlternativeResolverSuffix
  (path : SyntaxPath) : Prop :=
| alternative_resolver_suffix_declaration :
    path_has_suffixb path provider_declaration_suffix = true ->
    Phase1AlternativeResolverSuffix path
| alternative_resolver_suffix_generic_requirement :
    path_has_suffixb path generic_requirement_suffix = true ->
    Phase1AlternativeResolverSuffix path
| alternative_resolver_suffix_pattern :
    path_has_suffixb path pattern_suffix = true ->
    Phase1AlternativeResolverSuffix path
| alternative_resolver_suffix_primary_expression :
    path_has_suffixb path primary_expression_suffix = true ->
    Phase1AlternativeResolverSuffix path
| alternative_resolver_suffix_proposition_atom :
    path_has_suffixb path proposition_atom_suffix = true ->
    Phase1AlternativeResolverSuffix path
| alternative_resolver_suffix_static_argument :
    path_has_suffixb path static_argument_suffix = true ->
    Phase1AlternativeResolverSuffix path.

Theorem phase1_surface_alternative_resolver_some_suffix_classified :
  forall path items input decision,
    phase1_surface_expression_path_context path (EAlternative items) ->
    phase1_surface_certified_overlap_resolver path input = Some decision ->
    Phase1AlternativeResolverSuffix path.
Proof.
  intros path items input decision Hpath Hresolver.
  pose proof
    (phase1_surface_alternative_excludes_trailing_comma_path
      path items Hpath) as Htrail.
  unfold phase1_surface_certified_overlap_resolver in Hresolver.
  unfold phase1_surface_simple_resolver in Hresolver.
  destruct
    (path_has_suffixb path provider_declaration_suffix)
    eqn:Hprovider.
  - apply alternative_resolver_suffix_declaration.
    exact Hprovider.
  - destruct
      (path_has_suffixb path generic_requirement_suffix)
      eqn:Hgeneric.
    + apply alternative_resolver_suffix_generic_requirement.
      exact Hgeneric.
    + rewrite Htrail in Hresolver.
      simpl in Hresolver.
      unfold phase1_surface_structural_resolver in Hresolver.
      destruct (path_has_suffixb path pattern_suffix) eqn:Hpattern.
      * apply alternative_resolver_suffix_pattern.
        exact Hpattern.
      * destruct
          (path_has_suffixb path primary_expression_suffix)
          eqn:Hprimary.
        -- apply alternative_resolver_suffix_primary_expression.
           exact Hprimary.
        -- destruct
            (path_has_suffixb path proposition_atom_suffix)
            eqn:Hproposition.
           ++ apply alternative_resolver_suffix_proposition_atom.
              exact Hproposition.
           ++ destruct
                (path_has_suffixb path static_argument_suffix)
                eqn:Hstatic.
              ** apply alternative_resolver_suffix_static_argument.
                 exact Hstatic.
              ** discriminate Hresolver.
Qed.
