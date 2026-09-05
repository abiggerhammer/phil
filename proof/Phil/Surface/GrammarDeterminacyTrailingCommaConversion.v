From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyPredictiveFallbackSoundness
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyOracleAssemblyReflection.

Import ListNotations.
Open Scope string_scope.

(*
  Trailing-comma specialization for the final PHIL-SURFACE-DETERM-001
  ordinary-derivation -> predictive-oracle conversion.

  The assembly checker deliberately retained two pieces of information that a
  one-token FOLLOW set cannot express:

    - a continuing repeated item starts with comma and then an IDENTIFIER; and
    - after the repetition, the enclosing sequence has exactly the optional
      trailing comma / close-brace shape.

  This file reflects those booleans into exact syntax shapes.  It also proves
  the semantic half of the continuing case: any ordinary derivation of a
  certified repeated body exposes the concrete `, IDENTIFIER` token prefix, so
  the trailing-comma resolver must choose Continue.
*)

Lemma comma_identifier_repetition_bodyb_sequence_equation :
  forall comma first tail,
    comma_identifier_repetition_bodyb
      (ESequence (ELiteral comma :: first :: tail)) =
    andb (String.eqb comma ",")
      (andb
        (negb
          (nullable_expression
            phase1_surface_nullable_facts first))
        (andb
          (overlap_token_list_eqb
            (first_expression
              phase1_surface_nullable_facts
              phase1_surface_first_facts
              first)
            [OverlapLexicalClass "IDENTIFIER"])
          (choice_bodies_nonnullable_fuel expression_fuel first))).
Proof.
  reflexivity.
Qed.

Lemma comma_identifier_repetition_bodyb_shape :
  forall body,
    comma_identifier_repetition_bodyb body = true ->
    exists first tail,
      body = ESequence (ELiteral "," :: first :: tail) /\
      nullable_expression phase1_surface_nullable_facts first = false /\
      first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        first = [OverlapLexicalClass "IDENTIFIER"] /\
      choice_bodies_nonnullable_fuel expression_fuel first = true.
Proof.
  intros body Hshape.
  destruct body as
    [literal | class_name | name | items | items | body | body];
    try discriminate Hshape.
  destruct items as [| head rest]; try discriminate Hshape.
  destruct head as
    [comma | class_name | name | seq_items | alt_items | optional_body | repeat_body];
    try discriminate Hshape.
  destruct rest as [| first tail]; try discriminate Hshape.
  rewrite comma_identifier_repetition_bodyb_sequence_equation in Hshape.
  apply andb_true_iff in Hshape as [Hcomma Hshape].
  apply String.eqb_eq in Hcomma.
  subst comma.
  apply andb_true_iff in Hshape as [Hnullable Hshape].
  apply negb_true_iff in Hnullable.
  apply andb_true_iff in Hshape as [Hfirst Hsafe].
  apply assembly_overlap_token_list_eqb_eq in Hfirst.
  exists first, tail.
  repeat split; assumption || reflexivity.
Qed.

Lemma trailing_comma_tail_shapeb_cases :
  forall items outer_follow,
    trailing_comma_tail_shapeb items outer_follow = true ->
    items = [EOptional (ELiteral ","); ELiteral "}"] \/
    (items = [EOptional (ELiteral ",")] /\
     outer_follow = [OverlapLiteral "}"]).
Proof.
  intros items outer_follow Hshape.
  unfold trailing_comma_tail_shapeb in Hshape.
  destruct items as [| first rest].
  - discriminate Hshape.
  - destruct rest as [| second rest].
    + destruct first as
        [literal | class_name | name | seq_items | alt_items |
         optional_body | repeat_body];
        try discriminate Hshape.
      destruct optional_body as
        [comma | class_name | name | seq_items | alt_items |
         nested_optional | nested_repeat];
        try discriminate Hshape.
      simpl in Hshape.
      apply andb_true_iff in Hshape as [Hcomma Hfollow].
      apply String.eqb_eq in Hcomma.
      subst comma.
      apply assembly_overlap_token_list_eqb_eq in Hfollow.
      right.
      split.
      * reflexivity.
      * exact Hfollow.
    + destruct rest as [| third rest].
      * destruct first as
          [literal | class_name | name | seq_items | alt_items |
           optional_body | repeat_body];
          try discriminate Hshape.
        destruct optional_body as
          [comma | class_name | name | seq_items | alt_items |
           nested_optional | nested_repeat];
          try discriminate Hshape.
        destruct second as
          [close | class_name | name | seq_items | alt_items |
           optional_body | repeat_body];
          try discriminate Hshape.
        simpl in Hshape.
        apply andb_true_iff in Hshape as [Hcomma Hclose].
        apply String.eqb_eq in Hcomma.
        apply String.eqb_eq in Hclose.
        subst comma close.
        left.
        reflexivity.
      * destruct first as
          [literal | class_name | name | seq_items | alt_items |
           optional_body | repeat_body];
          try (simpl in Hshape; discriminate Hshape).
        destruct optional_body as
          [comma | class_name | name | seq_items | alt_items |
           nested_optional | nested_repeat];
          simpl in Hshape;
          discriminate Hshape.
Qed.

Lemma trailing_comma_body_derivation_has_identifier_prefix :
  forall path body input rest tree,
    comma_identifier_repetition_bodyb body = true ->
    Derives phase1_surface_rules path body input rest tree ->
    exists lexeme tail,
      input = TLiteral "," :: TLexical "IDENTIFIER" lexeme :: tail.
Proof.
  intros path body input rest tree Hshape Hderive.
  destruct (comma_identifier_repetition_bodyb_shape body Hshape)
    as [first [tail_items
      [Hbody [Hnonnullable [Hfirst Hsafe]]]]].
  subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      (ELiteral "," :: first :: tail_items)
      input rest tree Hderive)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 0
      (ELiteral ",") (first :: tail_items)
      input rest trees Hitems)
    as [middle [comma_tree [tail_trees [Hcomma Htail]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend path (AtSequence 0))
      "," input middle comma_tree Hcomma)
    as [after_comma [Hinput [Hmiddle _]]].
  subst middle.
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 1
      first tail_items
      after_comma rest tail_trees Htail)
    as [after_first [first_tree [rest_trees [Hfirst_derive _]]]].
  pose proof
    (phase1_surface_nonnullable_derivation_starts_inputb
      (descend path (AtSequence 1))
      first after_comma after_first first_tree
      Hfirst_derive Hsafe Hnonnullable)
    as Hstarts.
  destruct after_comma as [| first_token remaining].
  - rewrite expression_starts_inputb_nil_equation in Hstarts.
    rewrite Hnonnullable in Hstarts.
    discriminate Hstarts.
  - rewrite expression_starts_inputb_cons_equation in Hstarts.
    rewrite Hfirst in Hstarts.
    destruct first_token as [literal | class_name lexeme].
    + simpl in Hstarts.
      discriminate Hstarts.
    + simpl in Hstarts.
      apply String.eqb_eq in Hstarts.
      subst class_name.
      exists lexeme, remaining.
      rewrite Hinput.
      reflexivity.
Qed.

Theorem trailing_comma_body_derivation_continues :
  forall path body input rest tree,
    comma_identifier_repetition_bodyb body = true ->
    Derives phase1_surface_rules path body input rest tree ->
    trailing_comma_repeat_decision input = Some ChooseRepetitionContinue.
Proof.
  intros path body input rest tree Hshape Hderive.
  destruct
    (trailing_comma_body_derivation_has_identifier_prefix
      path body input rest tree Hshape Hderive)
    as [lexeme [tail Hinput]].
  rewrite Hinput.
  apply trailing_comma_decision_identifier_tail_continues.
Qed.
