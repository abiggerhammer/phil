From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyStaticArgumentParenthesisSoundness
  GrammarDeterminacyRefinementBraceSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Final static-argument seam for the alternative-resolver dispatcher.

  Branch 0 of static_argument is nonreference_type_expression.  The existing
  parenthesis proof already lifts tuple_type through that branch.  The brace
  proof commits refinement_type itself, but the final ordinary-derivation ->
  predictive-oracle conversion sees the enclosing nonreference type branch.
  Reflect brace-led ordinary derivations through that one remaining level.
*)

Lemma phase1_surface_float_type_brace_derivation_impossible :
  forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "float_type") input rest tree ->
    input = TLiteral "{" :: tail ->
    False.
Proof.
  intros path input rest tree tail Hderive Hinput_brace.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "float_type" input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite phase1_surface_float_type_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "float_type"))
      [ELiteral "F32"; ELiteral "F64"]
      input rest subtree Hbody)
    as [index [item [branch_tree [Hnth [_ Hbranch]]]]].
  destruct index as [| index].
  - vm_compute in Hnth.
    inversion Hnth; subst item.
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "F32" input rest branch_tree Hbranch)
      as [suffix [Hstart _]].
    rewrite Hinput_brace in Hstart.
    discriminate Hstart.
  - destruct index as [| index].
    + vm_compute in Hnth.
      inversion Hnth; subst item.
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "F64" input rest branch_tree Hbranch)
        as [suffix [Hstart _]].
      rewrite Hinput_brace in Hstart.
      discriminate Hstart.
    + destruct index; vm_compute in Hnth; discriminate Hnth.
Qed.

Theorem phase1_surface_nonreference_type_expression_brace_derivation_exposes_refinement :
  forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_type_expression") input rest tree ->
    input = TLiteral "{" :: tail ->
    exists refinement_path refinement_tree,
      Derives phase1_surface_rules refinement_path
        (ENonterminal "refinement_type") input rest refinement_tree.
Proof.
  intros path input rest tree tail Hderive Hinput_brace.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "nonreference_type_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite phase1_surface_nonreference_type_expression_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "nonreference_type_expression"))
      phase1_surface_nonreference_type_expression_items
      input rest subtree Hbody)
    as [index [item [branch_tree [Hnth [_ Hbranch]]]]].
  destruct index as [| index].
  - vm_compute in Hnth.
    inversion Hnth; subst item.
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "Unit" input rest branch_tree Hbranch)
      as [suffix [Hstart _]].
    rewrite Hinput_brace in Hstart.
    discriminate Hstart.
  - destruct index as [| index].
    + vm_compute in Hnth.
      inversion Hnth; subst item.
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "Bool" input rest branch_tree Hbranch)
        as [suffix [Hstart _]].
      rewrite Hinput_brace in Hstart.
      discriminate Hstart.
    + destruct index as [| index].
      * vm_compute in Hnth.
        inversion Hnth; subst item.
        destruct
          (derives_nonterminal_lexical_starts
            _ "uint_type" "UINT_TYPE" input rest branch_tree
            phase1_surface_uint_type_lookup_exact Hbranch)
          as [lexeme [suffix Hstart]].
        rewrite Hinput_brace in Hstart.
        discriminate Hstart.
      * destruct index as [| index].
        -- vm_compute in Hnth.
           inversion Hnth; subst item.
           destruct
             (derives_nonterminal_lexical_starts
               _ "sint_type" "SINT_TYPE" input rest branch_tree
               phase1_surface_sint_type_lookup_exact Hbranch)
             as [lexeme [suffix Hstart]].
           rewrite Hinput_brace in Hstart.
           discriminate Hstart.
        -- destruct index as [| index].
           ++ vm_compute in Hnth.
              inversion Hnth; subst item.
              exfalso.
              eapply phase1_surface_float_type_brace_derivation_impossible.
              ** exact Hbranch.
              ** exact Hinput_brace.
           ++ destruct index as [| index].
              ** vm_compute in Hnth.
                 inversion Hnth; subst item.
                 destruct
                   (derives_sequence_literal_head_starts _ "Bytes" _
                     input rest branch_tree Hbranch)
                   as [suffix Hstart].
                 rewrite Hinput_brace in Hstart.
                 discriminate Hstart.
              ** destruct index as [| index].
                 --- vm_compute in Hnth.
                     inversion Hnth; subst item.
                     destruct
                       (derives_sequence_literal_head_starts _ "Frame" _
                         input rest branch_tree Hbranch)
                       as [suffix Hstart].
                     rewrite Hinput_brace in Hstart.
                     discriminate Hstart.
                 --- destruct index as [| index].
                     +++ vm_compute in Hnth.
                         inversion Hnth; subst item.
                         destruct
                           (derives_sequence_literal_head_starts _ "Proof" _
                             input rest branch_tree Hbranch)
                           as [suffix Hstart].
                         rewrite Hinput_brace in Hstart.
                         discriminate Hstart.
                     +++ destruct index as [| index].
                         *** vm_compute in Hnth.
                             inversion Hnth; subst item.
                             destruct
                               (derives_sequence_literal_head_starts _ "Validated" _
                                 input rest branch_tree Hbranch)
                               as [suffix Hstart].
                             rewrite Hinput_brace in Hstart.
                             discriminate Hstart.
                         *** destruct index as [| index].
                             ---- vm_compute in Hnth.
                                  inversion Hnth; subst item.
                                  eexists.
                                  eexists.
                                  exact Hbranch.
                             ---- destruct index as [| index].
                                  ++++ vm_compute in Hnth.
                                       inversion Hnth; subst item.
                                       destruct phase1_surface_tuple_type_lookup_prefix
                                         as [tail_items Htuple].
                                       destruct
                                         (derives_nonterminal_sequence_literal_head_starts
                                           _ "tuple_type" "(" tail_items
                                           input rest branch_tree Htuple Hbranch)
                                         as [suffix Hstart].
                                       rewrite Hinput_brace in Hstart.
                                       discriminate Hstart.
                                  ++++ destruct index; vm_compute in Hnth; discriminate Hnth.
Qed.

Theorem phase1_surface_nonreference_type_expression_brace_derivation_commits_static_argument_branch :
  forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_type_expression") input rest tree ->
    input = TLiteral "{" :: tail ->
    static_argument_decision input = Some (ChooseAlternative 0).
Proof.
  intros path input rest tree tail Hderive Hinput_brace.
  destruct
    (phase1_surface_nonreference_type_expression_brace_derivation_exposes_refinement
      path input rest tree tail Hderive Hinput_brace)
    as [refinement_path [refinement_tree Hrefinement]].
  eapply phase1_surface_refinement_type_derivation_commits_static_argument_branch.
  exact Hrefinement.
Qed.
