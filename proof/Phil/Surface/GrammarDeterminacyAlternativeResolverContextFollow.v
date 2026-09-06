From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacyWitnessSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyAlternativeResolverSomeSuffix.

Open Scope string_scope.

(*
  FOLLOW-sensitive bridge for the six alternative resolver suffixes.

  Four resolver roots make alternative_resolver_contextb true solely from the
  path suffix.  The pattern and proposition_atom roots additionally require
  that the local outer FOLLOW is exactly the generated rule FOLLOW.  Keep those
  two assumptions explicit so the final ordinary-derivation -> oracle
  conversion can discharge them from its nonterminal-reset invariant.
*)

Lemma overlap_token_list_eqb_refl :
  forall tokens,
    overlap_token_list_eqb tokens tokens = true.
Proof.
  induction tokens as [| token rest IH].
  - reflexivity.
  - simpl.
    rewrite overlap_token_eqb_refl.
    exact IH.
Qed.

Theorem phase1_surface_resolver_suffix_context_follow :
  forall path outer_follow,
    Phase1AlternativeResolverSuffix path ->
    (path_has_suffixb path pattern_suffix = true ->
      outer_follow =
        lookup_tokens "pattern" phase1_surface_follow_facts) ->
    (path_has_suffixb path proposition_atom_suffix = true ->
      outer_follow =
        lookup_tokens "proposition_atom" phase1_surface_follow_facts) ->
    alternative_resolver_contextb path outer_follow = true.
Proof.
  intros path outer_follow Hsuffix Hpattern_follow Hproposition_follow.
  unfold alternative_resolver_contextb.
  destruct
    (path_has_suffixb path provider_declaration_suffix)
    eqn:Hdeclaration.
  - reflexivity.
  - destruct
      (path_has_suffixb path generic_requirement_suffix)
      eqn:Hgeneric.
    + reflexivity.
    + destruct (path_has_suffixb path pattern_suffix) eqn:Hpattern.
      * rewrite (Hpattern_follow Hpattern).
        apply overlap_token_list_eqb_refl.
      * destruct
          (path_has_suffixb path primary_expression_suffix)
          eqn:Hprimary.
        -- reflexivity.
        -- destruct
            (path_has_suffixb path proposition_atom_suffix)
            eqn:Hproposition.
           ++ rewrite (Hproposition_follow Hproposition).
              apply overlap_token_list_eqb_refl.
           ++ destruct
                (path_has_suffixb path static_argument_suffix)
                eqn:Hstatic.
              ** reflexivity.
              ** destruct Hsuffix as
                   [Hsuffix | Hsuffix | Hsuffix | Hsuffix | Hsuffix | Hsuffix];
                   congruence.
Qed.
