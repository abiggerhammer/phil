From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPropositionSpine
  GrammarAstGenericRequirementsTotality
  GrammarAstSourceHeaderTotality
  GrammarAstTopLevelTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the shared proposition precedence-spine correspondence. *)

Definition phase1_surface_proposition_atom_items_for_totality
  : list EbnfExpression :=
  [ ENonterminal "relation_proposition";
    ESequence
      [ ELiteral "(";
        ENonterminal "proposition";
        ELiteral ")"
      ];
    ELiteral "true";
    ELiteral "false";
    ENonterminal "claim_application"
  ].

Definition phase1_surface_proposition_not_items_for_totality
  : list EbnfExpression :=
  [ ESequence
      [ ELiteral "not";
        ENonterminal "proposition_not"
      ];
    ENonterminal "proposition_atom"
  ].

Definition phase1_surface_proposition_and_suffix_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral "and";
      ENonterminal "proposition_not"
    ].

Definition phase1_surface_proposition_or_suffix_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral "or";
      ENonterminal "proposition_and"
    ].

Lemma phase1_surface_proposition_lookup_for_totality :
  lookupRule "proposition" phase1_surface_rules =
    Some (ENonterminal "proposition_or").
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_proposition_or_lookup_for_totality :
  lookupRule "proposition_or" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "proposition_and";
          ERepetition phase1_surface_proposition_or_suffix_expression_for_totality
        ]).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_proposition_and_lookup_for_totality :
  lookupRule "proposition_and" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "proposition_not";
          ERepetition phase1_surface_proposition_and_suffix_expression_for_totality
        ]).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_proposition_not_lookup_for_totality :
  lookupRule "proposition_not" phase1_surface_rules =
    Some (EAlternative phase1_surface_proposition_not_items_for_totality).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_proposition_atom_lookup_for_totality :
  lookupRule "proposition_atom" phase1_surface_rules =
    Some (EAlternative phase1_surface_proposition_atom_items_for_totality).
Proof. vm_compute. reflexivity. Qed.

Theorem phase1_surface_normalize_proposition_atom_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "proposition_atom")
      input rest tree ->
    exists atom,
      phase1_surface_normalize_proposition_atom_spine tree = Some atom /\
      phase1_surface_proposition_atom_spine_tree atom = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "proposition_atom"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_proposition_atom_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "proposition_atom"))
      phase1_surface_proposition_atom_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth. inversion Hnth; subst item.
    pose proof
      (phase1_surface_validate_named_node_total_from_derivation
        "relation_proposition" _ _ _ selected Hselected)
      as Hvalidate.
    let atom := constr:(Phase1RelationPropositionAtom selected) in
    assert (Hnormalize :
      phase1_surface_normalize_proposition_atom_spine tree = Some atom).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_proposition_atom_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn. rewrite String.eqb_refl, Hvalidate. reflexivity.
    }
    exists atom. split; [exact Hnormalize|].
    eapply phase1_surface_normalize_proposition_atom_spine_round_trip.
    exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth. inversion Hnth; subst item.
      destruct
        (derives_sequence_expression_exposes_items
          phase1_surface_rules _
          [ELiteral "("; ENonterminal "proposition"; ELiteral ")"]
          input rest selected Hselected)
        as [trees [Hselected_tree Hitems]].
      repeat match goal with
      | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
          inversion Hseq; subst; clear Hseq
      end.
      match goal with
      | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
          inversion Hnil; subst; clear Hnil
      end.
      match goal with
      | Hopen : Derives phase1_surface_rules _ (ELiteral "(") _ _ ?open_tree,
        Hproposition : Derives phase1_surface_rules _
          (ENonterminal "proposition") _ _ ?proposition_tree,
        Hclose : Derives phase1_surface_rules _ (ELiteral ")") _ _ ?close_tree |- _ =>
          destruct
            (literal_derivation_is_exact
              phase1_surface_rules _ "(" _ _ open_tree Hopen)
            as [open_tail [_ [_ Hopen_tree]]];
          pose proof
            (phase1_surface_validate_named_node_total_from_derivation
              "proposition" _ _ _ proposition_tree Hproposition)
            as Hproposition_validate;
          destruct
            (literal_derivation_is_exact
              phase1_surface_rules _ ")" _ _ close_tree Hclose)
            as [close_tail [_ [_ Hclose_tree]]];
          let atom := constr:(Phase1ParenthesizedPropositionAtom proposition_tree) in
          assert (Hnormalize :
            phase1_surface_normalize_proposition_atom_spine tree = Some atom);
          [ rewrite Htree, Hsubtree, Hselected_tree, Hopen_tree, Hclose_tree;
            unfold phase1_surface_normalize_proposition_atom_spine,
              phase1_surface_expect_nonterminal,
              phase1_surface_expect_alternative,
              phase1_surface_expect_sequence,
              phase1_surface_exact3,
              phase1_surface_expect_literal;
            cbn;
            repeat rewrite String.eqb_refl;
            rewrite Hproposition_validate;
            reflexivity
          | exists atom; split;
            [ exact Hnormalize
            | eapply phase1_surface_normalize_proposition_atom_spine_round_trip;
              exact Hnormalize ] ]
      end.
    + destruct index as [|index].
      * cbn in Hnth. inversion Hnth; subst item.
        destruct
          (literal_derivation_is_exact
            phase1_surface_rules _ "true" _ _ selected Hselected)
          as [tail [_ [_ Hselected_tree]]].
        let atom := constr:(Phase1TruePropositionAtom) in
        assert (Hnormalize :
          phase1_surface_normalize_proposition_atom_spine tree = Some atom).
        {
          rewrite Htree, Hsubtree, Hselected_tree.
          unfold phase1_surface_normalize_proposition_atom_spine,
            phase1_surface_expect_nonterminal,
            phase1_surface_expect_alternative,
            phase1_surface_expect_literal.
          cbn. repeat rewrite String.eqb_refl. reflexivity.
        }
        exists atom. split; [exact Hnormalize|].
        eapply phase1_surface_normalize_proposition_atom_spine_round_trip.
        exact Hnormalize.
      * destruct index as [|index].
        -- cbn in Hnth. inversion Hnth; subst item.
           destruct
             (literal_derivation_is_exact
               phase1_surface_rules _ "false" _ _ selected Hselected)
             as [tail [_ [_ Hselected_tree]]].
           let atom := constr:(Phase1FalsePropositionAtom) in
           assert (Hnormalize :
             phase1_surface_normalize_proposition_atom_spine tree = Some atom).
           {
             rewrite Htree, Hsubtree, Hselected_tree.
             unfold phase1_surface_normalize_proposition_atom_spine,
               phase1_surface_expect_nonterminal,
               phase1_surface_expect_alternative,
               phase1_surface_expect_literal.
             cbn. repeat rewrite String.eqb_refl. reflexivity.
           }
           exists atom. split; [exact Hnormalize|].
           eapply phase1_surface_normalize_proposition_atom_spine_round_trip.
           exact Hnormalize.
        -- destruct index as [|index].
           ++ cbn in Hnth. inversion Hnth; subst item.
              pose proof
                (phase1_surface_validate_named_node_total_from_derivation
                  "claim_application" _ _ _ selected Hselected)
                as Hvalidate.
              let atom := constr:(Phase1ClaimPropositionAtom selected) in
              assert (Hnormalize :
                phase1_surface_normalize_proposition_atom_spine tree = Some atom).
              {
                rewrite Htree, Hsubtree.
                unfold phase1_surface_normalize_proposition_atom_spine,
                  phase1_surface_expect_nonterminal,
                  phase1_surface_expect_alternative.
                cbn. rewrite String.eqb_refl, Hvalidate. reflexivity.
              }
              exists atom. split; [exact Hnormalize|].
              eapply phase1_surface_normalize_proposition_atom_spine_round_trip.
              exact Hnormalize.
           ++ cbn in Hnth. discriminate Hnth.
Qed.

Theorem phase1_surface_normalize_proposition_not_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "proposition_not")
      input rest tree ->
    exists proposition,
      phase1_surface_normalize_proposition_not_spine tree = Some proposition /\
      phase1_surface_proposition_not_spine_tree proposition = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "proposition_not"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_proposition_not_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "proposition_not"))
      phase1_surface_proposition_not_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth. inversion Hnth; subst item.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules _
        [ELiteral "not"; ENonterminal "proposition_not"]
        input rest selected Hselected)
      as [trees [Hselected_tree Hitems]].
    repeat match goal with
    | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
        inversion Hseq; subst; clear Hseq
    end.
    match goal with
    | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
        inversion Hnil; subst; clear Hnil
    end.
    match goal with
    | Hnot : Derives phase1_surface_rules _ (ELiteral "not") _ _ ?not_tree,
      Hchild : Derives phase1_surface_rules _
        (ENonterminal "proposition_not") _ _ ?child_tree |- _ =>
        destruct
          (literal_derivation_is_exact
            phase1_surface_rules _ "not" _ _ not_tree Hnot)
          as [not_tail [_ [_ Hnot_tree]]];
        pose proof
          (phase1_surface_validate_named_node_total_from_derivation
            "proposition_not" _ _ _ child_tree Hchild)
          as Hchild_validate;
        let proposition := constr:(Phase1NotPropositionSpine child_tree) in
        assert (Hnormalize :
          phase1_surface_normalize_proposition_not_spine tree = Some proposition);
        [ rewrite Htree, Hsubtree, Hselected_tree, Hnot_tree;
          unfold phase1_surface_normalize_proposition_not_spine,
            phase1_surface_expect_nonterminal,
            phase1_surface_expect_alternative,
            phase1_surface_expect_sequence,
            phase1_surface_exact2,
            phase1_surface_expect_literal;
          cbn;
          repeat rewrite String.eqb_refl;
          rewrite Hchild_validate;
          reflexivity
        | exists proposition; split;
          [ exact Hnormalize
          | eapply phase1_surface_normalize_proposition_not_spine_round_trip;
            exact Hnormalize ] ]
    end.
  - destruct index as [|index].
    + cbn in Hnth. inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_proposition_atom_spine_total_from_derivation
          _ _ _ selected Hselected)
        as [atom [Hatom Hatom_tree]].
      let proposition := constr:(Phase1AtomPropositionSpine atom) in
      assert (Hnormalize :
        phase1_surface_normalize_proposition_not_spine tree = Some proposition).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_proposition_not_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn. rewrite String.eqb_refl, Hatom. reflexivity.
      }
      exists proposition. split; [exact Hnormalize|].
      eapply phase1_surface_normalize_proposition_not_spine_round_trip.
      exact Hnormalize.
    + cbn in Hnth. discriminate Hnth.
Qed.

Lemma phase1_surface_normalize_proposition_and_suffix_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_proposition_and_suffix_expression_for_totality
      input rest tree ->
    exists proposition,
      phase1_surface_normalize_proposition_and_suffix tree = Some proposition.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_proposition_and_suffix_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ELiteral "and"; ENonterminal "proposition_not"]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hand : Derives phase1_surface_rules _ (ELiteral "and") _ _ ?and_tree,
    Hproposition : Derives phase1_surface_rules _
      (ENonterminal "proposition_not") _ _ ?proposition_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "and" _ _ and_tree Hand)
        as [and_tail [_ [_ Hand_tree]]];
      destruct
        (phase1_surface_normalize_proposition_not_spine_total_from_derivation
          _ _ _ proposition_tree Hproposition)
        as [proposition [Hproposition_normalize Hproposition_tree]];
      exists proposition;
      rewrite Htree, Hand_tree;
      unfold phase1_surface_normalize_proposition_and_suffix,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_expect_literal;
      cbn;
      rewrite String.eqb_refl, Hproposition_normalize;
      reflexivity
  end.
Qed.

Lemma phase1_surface_normalize_proposition_and_suffixes_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_proposition_and_suffix_expression_for_totality ->
    exists propositions,
      phase1_surface_normalize_proposition_and_suffixes trees = Some propositions.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists []. reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_proposition_and_suffix_total_from_derivation
        (descend path AtRepetitionBody) input middle tree Hbody)
      as [proposition Hproposition].
    destruct (IHrest eq_refl) as [propositions Hpropositions].
    exists (proposition :: propositions).
    cbn. rewrite Hproposition, Hpropositions. reflexivity.
Qed.

Theorem phase1_surface_normalize_proposition_and_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "proposition_and")
      input rest tree ->
    exists proposition,
      phase1_surface_normalize_proposition_and_spine tree = Some proposition /\
      phase1_surface_proposition_and_spine_tree proposition = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "proposition_and"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_proposition_and_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules _
      [ ENonterminal "proposition_not";
        ERepetition phase1_surface_proposition_and_suffix_expression_for_totality ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hfirst : Derives phase1_surface_rules _
      (ENonterminal "proposition_not") _ _ ?first_tree,
    Hrest : Derives phase1_surface_rules _
      (ERepetition phase1_surface_proposition_and_suffix_expression_for_totality)
      _ _ ?rest_tree |- _ =>
      destruct
        (phase1_surface_normalize_proposition_not_spine_total_from_derivation
          _ _ _ first_tree Hfirst)
        as [first [Hfirst_normalize Hfirst_tree_round]];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ phase1_surface_proposition_and_suffix_expression_for_totality
          _ _ rest_tree Hrest)
        as [rest_trees [Hrest_tree Hrest_body]];
      destruct
        (phase1_surface_normalize_proposition_and_suffixes_total_from_repetition
          _ phase1_surface_proposition_and_suffix_expression_for_totality
          _ _ rest_trees Hrest_body eq_refl)
        as [rest_values Hrest_normalize];
      let proposition := constr:(
        {| phase1_proposition_and_spine_first := first;
           phase1_proposition_and_spine_rest := rest_values |}) in
      assert (Hnormalize :
        phase1_surface_normalize_proposition_and_spine tree = Some proposition);
      [ rewrite Htree, Hsubtree, Hrest_tree;
        unfold phase1_surface_normalize_proposition_and_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_repetition;
        cbn;
        repeat rewrite String.eqb_refl;
        rewrite Hfirst_normalize, Hrest_normalize;
        reflexivity
      | exists proposition; split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_proposition_and_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_proposition_or_suffix_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_proposition_or_suffix_expression_for_totality
      input rest tree ->
    exists proposition,
      phase1_surface_normalize_proposition_or_suffix tree = Some proposition.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_proposition_or_suffix_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ELiteral "or"; ENonterminal "proposition_and"]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hor : Derives phase1_surface_rules _ (ELiteral "or") _ _ ?or_tree,
    Hproposition : Derives phase1_surface_rules _
      (ENonterminal "proposition_and") _ _ ?proposition_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "or" _ _ or_tree Hor)
        as [or_tail [_ [_ Hor_tree]]];
      destruct
        (phase1_surface_normalize_proposition_and_spine_total_from_derivation
          _ _ _ proposition_tree Hproposition)
        as [proposition [Hproposition_normalize Hproposition_tree]];
      exists proposition;
      rewrite Htree, Hor_tree;
      unfold phase1_surface_normalize_proposition_or_suffix,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_expect_literal;
      cbn;
      rewrite String.eqb_refl, Hproposition_normalize;
      reflexivity
  end.
Qed.

Lemma phase1_surface_normalize_proposition_or_suffixes_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_proposition_or_suffix_expression_for_totality ->
    exists propositions,
      phase1_surface_normalize_proposition_or_suffixes trees = Some propositions.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists []. reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_proposition_or_suffix_total_from_derivation
        (descend path AtRepetitionBody) input middle tree Hbody)
      as [proposition Hproposition].
    destruct (IHrest eq_refl) as [propositions Hpropositions].
    exists (proposition :: propositions).
    cbn. rewrite Hproposition, Hpropositions. reflexivity.
Qed.

Theorem phase1_surface_normalize_proposition_or_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "proposition_or")
      input rest tree ->
    exists proposition,
      phase1_surface_normalize_proposition_or_spine tree = Some proposition /\
      phase1_surface_proposition_or_spine_tree proposition = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "proposition_or"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_proposition_or_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules _
      [ ENonterminal "proposition_and";
        ERepetition phase1_surface_proposition_or_suffix_expression_for_totality ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hfirst : Derives phase1_surface_rules _
      (ENonterminal "proposition_and") _ _ ?first_tree,
    Hrest : Derives phase1_surface_rules _
      (ERepetition phase1_surface_proposition_or_suffix_expression_for_totality)
      _ _ ?rest_tree |- _ =>
      destruct
        (phase1_surface_normalize_proposition_and_spine_total_from_derivation
          _ _ _ first_tree Hfirst)
        as [first [Hfirst_normalize Hfirst_tree_round]];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ phase1_surface_proposition_or_suffix_expression_for_totality
          _ _ rest_tree Hrest)
        as [rest_trees [Hrest_tree Hrest_body]];
      destruct
        (phase1_surface_normalize_proposition_or_suffixes_total_from_repetition
          _ phase1_surface_proposition_or_suffix_expression_for_totality
          _ _ rest_trees Hrest_body eq_refl)
        as [rest_values Hrest_normalize];
      let proposition := constr:(
        {| phase1_proposition_or_spine_first := first;
           phase1_proposition_or_spine_rest := rest_values |}) in
      assert (Hnormalize :
        phase1_surface_normalize_proposition_or_spine tree = Some proposition);
      [ rewrite Htree, Hsubtree, Hrest_tree;
        unfold phase1_surface_normalize_proposition_or_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_repetition;
        cbn;
        repeat rewrite String.eqb_refl;
        rewrite Hfirst_normalize, Hrest_normalize;
        reflexivity
      | exists proposition; split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_proposition_or_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Theorem phase1_surface_normalize_proposition_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "proposition")
      input rest tree ->
    exists proposition,
      phase1_surface_normalize_proposition_spine tree = Some proposition /\
      phase1_surface_proposition_spine_tree proposition = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "proposition"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_proposition_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (phase1_surface_normalize_proposition_or_spine_total_from_derivation
      (descend path (AtNonterminal "proposition"))
      input rest subtree Hbody)
    as [proposition_or [Hor Hor_tree]].
  let proposition := constr:(
    {| phase1_proposition_spine_or := proposition_or |}) in
  assert (Hnormalize :
    phase1_surface_normalize_proposition_spine tree = Some proposition).
  {
    rewrite Htree.
    unfold phase1_surface_normalize_proposition_spine,
      phase1_surface_expect_nonterminal.
    cbn. rewrite String.eqb_refl, Hor. reflexivity.
  }
  exists proposition. split; [exact Hnormalize|].
  eapply phase1_surface_normalize_proposition_spine_round_trip.
  exact Hnormalize.
Qed.
