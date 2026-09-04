From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyStructuralScannerSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic soundness for the refinement-type side of the brace-led
  static_argument overlap.

  The structural resolver commits branch 0 when the input begins
  "{" IDENTIFIER ":".  This file connects that token-level scanner theorem
  to arbitrary ordinary Grammar-v1 derivations of refinement_type.
*)

Lemma phase1_surface_refinement_type_lookup_prefix :
  exists tail_items,
    lookupRule "refinement_type" phase1_surface_rules =
      Some
        (ESequence
          (ELiteral "{" ::
           ENonterminal "identifier" ::
           ELiteral ":" ::
           tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Theorem phase1_surface_refinement_type_derivation_commits_static_argument_branch :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "refinement_type") input rest tree ->
    static_argument_decision input = Some (ChooseAlternative 0).
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_refinement_type_lookup_prefix
    as [tail_items Hlookup_exact].
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "refinement_type"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite Hlookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "refinement_type"))
      (ELiteral "{" ::
       ENonterminal "identifier" ::
       ELiteral ":" ::
       tail_items)
      input rest subtree Hbody)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "refinement_type")) 0
      (ELiteral "{")
      (ENonterminal "identifier" :: ELiteral ":" :: tail_items)
      input rest trees Hitems)
    as [after_open [open_tree [tail_trees [Hopen Htail]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend
        (descend path (AtNonterminal "refinement_type"))
        (AtSequence 0))
      "{" input after_open open_tree Hopen)
    as [open_tail [Hinput [Hafter_open _]]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "refinement_type")) 1
      (ENonterminal "identifier")
      (ELiteral ":" :: tail_items)
      after_open rest tail_trees Htail)
    as [after_identifier
        [identifier_tree [remaining_trees [Hidentifier Hremaining]]]].
  destruct
    (phase1_surface_identifier_derivation_is_exact
      (descend
        (descend path (AtNonterminal "refinement_type"))
        (AtSequence 1))
      after_open after_identifier identifier_tree Hidentifier)
    as [lexeme
        [identifier_tail [Hidentifier_input Hidentifier_rest]]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "refinement_type")) 2
      (ELiteral ":") tail_items
      after_identifier rest remaining_trees Hremaining)
    as [after_colon [colon_tree [tail_after_colon [Hcolon _]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend
        (descend path (AtNonterminal "refinement_type"))
        (AtSequence 2))
      ":" after_identifier after_colon colon_tree Hcolon)
    as [colon_tail [Hcolon_input [_ _]]].
  rewrite Hinput.
  rewrite <- Hafter_open.
  rewrite Hidentifier_input.
  rewrite <- Hidentifier_rest.
  rewrite Hcolon_input.
  apply static_argument_brace_colon_tail_commits_refinement.
Qed.
