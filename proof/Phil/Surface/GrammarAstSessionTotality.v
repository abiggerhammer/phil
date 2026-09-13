From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionSpine
  GrammarAstTopLevelTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the first recursive session-expression correspondence layer. *)

Definition phase1_surface_nonreference_session_items_for_totality
  : list EbnfExpression :=
  [ ESequence
      [ ELiteral "send";
        ELiteral "(";
        ENonterminal "term_param";
        ELiteral ")";
        EOptional
          (ESequence
            [ ELiteral "using";
              ENonterminal "static_reference"
            ]);
        EOptional
          (ESequence
            [ ELiteral "when";
              ENonterminal "proposition"
            ]);
        ELiteral "then";
        ENonterminal "session_expression"
      ];
    ESequence
      [ ELiteral "receive";
        ELiteral "(";
        ENonterminal "term_param";
        ELiteral ")";
        EOptional
          (ESequence
            [ ELiteral "using";
              ENonterminal "static_reference"
            ]);
        EOptional
          (ESequence
            [ ELiteral "when";
              ENonterminal "proposition"
            ]);
        ELiteral "then";
        ENonterminal "session_expression"
      ];
    ESequence
      [ ELiteral "select";
        ELiteral "{";
        ENonterminal "session_branch";
        ERepetition
          (ESequence
            [ ELiteral "|";
              ENonterminal "session_branch"
            ]);
        ELiteral "}"
      ];
    ESequence
      [ ELiteral "offer";
        ELiteral "{";
        ENonterminal "session_branch";
        ERepetition
          (ESequence
            [ ELiteral "|";
              ENonterminal "session_branch"
            ]);
        ELiteral "}"
      ];
    ESequence
      [ ELiteral "end";
        ENonterminal "identifier"
      ];
    ESequence
      [ ELiteral "recursive";
        ENonterminal "identifier";
        ELiteral "=";
        ENonterminal "session_expression"
      ];
    ESequence
      [ ELiteral "continue";
        ENonterminal "identifier"
      ]
  ].

Definition phase1_surface_session_items_for_totality
  : list EbnfExpression :=
  [ ENonterminal "nonreference_session_expression";
    ENonterminal "static_reference"
  ].

Lemma phase1_surface_nonreference_session_lookup_for_totality :
  lookupRule "nonreference_session_expression" phase1_surface_rules =
    Some (EAlternative phase1_surface_nonreference_session_items_for_totality).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_session_lookup_for_totality :
  lookupRule "session_expression" phase1_surface_rules =
    Some (EAlternative phase1_surface_session_items_for_totality).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_nonreference_session_item_matches_tag :
  forall index item,
    nth_error phase1_surface_nonreference_session_items_for_totality index =
      Some item ->
    exists tag,
      phase1_surface_nonreference_session_tag_of_index index = Some tag.
Proof.
  intros index item Hnth.
  destruct index as [|index]; cbn in Hnth.
  - exists Phase1SendSession. reflexivity.
  - destruct index as [|index]; cbn in Hnth.
    + exists Phase1ReceiveSession. reflexivity.
    + destruct index as [|index]; cbn in Hnth.
      * exists Phase1SelectSession. reflexivity.
      * destruct index as [|index]; cbn in Hnth.
        -- exists Phase1OfferSession. reflexivity.
        -- destruct index as [|index]; cbn in Hnth.
           ++ exists Phase1EndSession. reflexivity.
           ++ destruct index as [|index]; cbn in Hnth.
              ** exists Phase1RecursiveSession. reflexivity.
              ** destruct index as [|index]; cbn in Hnth.
                 --- exists Phase1ContinueSession. reflexivity.
                 --- discriminate Hnth.
Qed.

Theorem phase1_surface_normalize_nonreference_session_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_session_expression")
      input rest tree ->
    exists session,
      phase1_surface_normalize_nonreference_session_spine tree = Some session /\
      phase1_surface_nonreference_session_spine_tree session = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "nonreference_session_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_nonreference_session_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "nonreference_session_expression"))
      phase1_surface_nonreference_session_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct
    (phase1_surface_nonreference_session_item_matches_tag index item Hnth)
    as [tag Htag].
  let session := constr:(
    {| phase1_nonreference_session_spine_tag := tag;
       phase1_nonreference_session_spine_selected_tree := selected |}) in
  assert (Hnormalize :
    phase1_surface_normalize_nonreference_session_spine tree = Some session).
  {
    rewrite Htree.
    rewrite Hsubtree.
    unfold phase1_surface_normalize_nonreference_session_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_alternative.
    cbn.
    rewrite Htag.
    reflexivity.
  }
  exists session.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_nonreference_session_spine_round_trip.
    exact Hnormalize.
Qed.

Theorem phase1_surface_normalize_session_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "session_expression")
      input rest tree ->
    exists session,
      phase1_surface_normalize_session_spine tree = Some session /\
      phase1_surface_session_spine_tree session = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "session_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_session_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "session_expression"))
      phase1_surface_session_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_nonreference_session_spine_total_from_derivation
        (descend
          (descend path (AtNonterminal "session_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [nonreference [Hnonreference Hround_trip]].
    let session := constr:(Phase1NonreferenceSessionSpine nonreference) in
    assert (Hnormalize :
      phase1_surface_normalize_session_spine tree = Some session).
    {
      rewrite Htree.
      rewrite Hsubtree.
      unfold phase1_surface_normalize_session_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite Hnonreference.
      reflexivity.
    }
    exists session.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_session_spine_round_trip.
      exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      let session := constr:(Phase1StaticReferenceSessionSpine selected) in
      assert (Hnormalize :
        phase1_surface_normalize_session_spine tree = Some session).
      {
        rewrite Htree.
        rewrite Hsubtree.
        unfold phase1_surface_normalize_session_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        reflexivity.
      }
      exists session.
      split.
      * exact Hnormalize.
      * eapply phase1_surface_normalize_session_spine_round_trip.
        exact Hnormalize.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
