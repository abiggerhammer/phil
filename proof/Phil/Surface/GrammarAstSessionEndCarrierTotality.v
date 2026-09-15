From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionEndCarrierSpine
  GrammarAstSourceHeaderTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the terminal `end identifier` carrier from #1071. *)

Theorem phase1_surface_normalize_end_session_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_end_session_expression_for_totality
      input rest tree ->
    exists session,
      phase1_surface_normalize_end_session_spine tree = Some session /\
      phase1_surface_end_session_spine_tree session = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_end_session_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "end";
        ENonterminal "identifier"
      ]
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
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral "end") _ _ ?keyword_tree,
    Houtcome : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ ?outcome_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "end" _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (phase1_surface_normalize_identifier_total_from_derivation
          _ _ _ outcome_tree Houtcome)
        as [outcome Houtcome_normalize];
      let session := constr:(
        {| phase1_end_session_outcome := outcome |}) in
      assert (Hnormalize :
        phase1_surface_normalize_end_session_spine tree = Some session);
      [ rewrite Htree, Hkeyword_tree;
        unfold phase1_surface_normalize_end_session_spine,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_literal;
        cbn;
        rewrite String.eqb_refl;
        rewrite Houtcome_normalize;
        reflexivity
      | exists session;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_end_session_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.
