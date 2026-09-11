From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarParserRecognizer
  GrammarParserProgress
  GrammarParserProductionKernel.

Import ListNotations.
Open Scope string_scope.

(*
  First universal proof-side AST correspondence carrier for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  The Haskell correspondence audit now covers a complete source value, but the
  ledger correctly keeps that evidence at Tested until the production
  representation is mechanically connected to a proof-side translation.

  This slice starts that translation at the outer source_file spine.  The
  normalized carrier deliberately retains the certified ParseTree subtrees for
  module/import/top-level bodies; later slices refine those subtrees into the
  proof-side normalized declaration carrier.  What becomes mechanical here is
  the source_file decomposition itself and its binding to the certified total
  parser.
*)

Record Phase1SurfaceSourceSpine : Type := {
  phase1_source_spine_module : option ParseTree;
  phase1_source_spine_imports : list ParseTree;
  phase1_source_spine_top_levels : list ParseTree
}.

Definition phase1_surface_source_spine_tree
  (spine : Phase1SurfaceSourceSpine) : ParseTree :=
  PTNonterminal phase1_surface_start
    (PTSequence
      [ match phase1_source_spine_module spine with
        | Some module_tree => PTOptionalSome module_tree
        | None => PTOptionalNone
        end;
        PTRepetition (phase1_source_spine_imports spine);
        PTRepetition (phase1_source_spine_top_levels spine)
      ]).

Definition phase1_surface_normalize_source_spine
  (tree : ParseTree) : option Phase1SurfaceSourceSpine :=
  match tree with
  | PTNonterminal name
      (PTSequence
        [ module_part;
          PTRepetition imports;
          PTRepetition top_levels
        ]) =>
      if String.eqb name phase1_surface_start then
        match module_part with
        | PTOptionalNone =>
            Some
              {| phase1_source_spine_module := None;
                 phase1_source_spine_imports := imports;
                 phase1_source_spine_top_levels := top_levels |}
        | PTOptionalSome module_tree =>
            Some
              {| phase1_source_spine_module := Some module_tree;
                 phase1_source_spine_imports := imports;
                 phase1_source_spine_top_levels := top_levels |}
        | _ => None
        end
      else None
  | _ => None
  end.

Theorem phase1_surface_normalize_source_spine_round_trip :
  forall tree spine,
    phase1_surface_normalize_source_spine tree = Some spine ->
    phase1_surface_source_spine_tree spine = tree.
Proof.
  intros tree spine Hnormalize.
  destruct tree as
    [root_literal
    | root_class root_lexeme
    | name body
    | root_trees
    | root_index root_branch
    |
    | root_optional_body
    | root_repeated];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct body as
    [body_literal
    | body_class body_lexeme
    | body_child_name body_child_body
    | fields
    | body_index body_branch
    |
    | body_optional_body
    | body_repeated];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct fields as [| module_part fields].
  - discriminate Hnormalize.
  - destruct fields as [| imports_part fields].
    + discriminate Hnormalize.
    + destruct fields as [| top_levels_part fields].
      * destruct imports_part;
          cbn in Hnormalize;
          discriminate Hnormalize.
      * destruct fields as [| extra rest].
        -- destruct imports_part;
             destruct top_levels_part;
             cbn in Hnormalize;
             try discriminate Hnormalize.
           destruct (String.eqb name phase1_surface_start) eqn:Hname;
             cbn in Hnormalize; try discriminate Hnormalize.
           apply String.eqb_eq in Hname.
           subst name.
           destruct module_part;
             cbn in Hnormalize; try discriminate Hnormalize.
           ++ inversion Hnormalize; subst; reflexivity.
           ++ inversion Hnormalize; subst; reflexivity.
        -- destruct imports_part;
             destruct top_levels_part;
             cbn in Hnormalize;
             discriminate Hnormalize.
Qed.

Lemma phase1_surface_start_rule :
  lookupRule phase1_surface_start phase1_surface_rules =
    Some
      (ESequence
        [ EOptional (ENonterminal "module_decl");
          ERepetition (ENonterminal "import_decl");
          ERepetition (ENonterminal "top_level_decl")
        ]).
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_normalize_source_spine_total :
  forall tokens tree,
    Phase1CompleteDerivation tokens tree ->
    exists spine,
      phase1_surface_normalize_source_spine tree = Some spine /\
      phase1_surface_source_spine_tree spine = tree.
Proof.
  intros tokens tree Hcomplete.
  unfold Phase1CompleteDerivation, CompleteDerivation in Hcomplete.
  inversion Hcomplete; subst.
  match goal with
  | Hlookup : lookupRule phase1_surface_start phase1_surface_rules = Some ?body,
    Hbody : Derives phase1_surface_rules _ ?body _ _ ?body_tree |- _ =>
      rewrite phase1_surface_start_rule in Hlookup;
      inversion Hlookup; subst body
  end.
  match goal with
  | Hbody : Derives phase1_surface_rules _ (ESequence _) _ _ _ |- _ =>
      inversion Hbody; subst; clear Hbody
  end.
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Himports : Derives phase1_surface_rules _
      (ERepetition (ENonterminal "import_decl")) _ _ _ |- _ =>
      inversion Himports; subst; clear Himports
  end.
  match goal with
  | Htops : Derives phase1_surface_rules _
      (ERepetition (ENonterminal "top_level_decl")) _ _ _ |- _ =>
      inversion Htops; subst; clear Htops
  end.
  match goal with
  | Hmodule : Derives phase1_surface_rules _
      (EOptional (ENonterminal "module_decl")) _ _ _ |- _ =>
      inversion Hmodule; subst; clear Hmodule
  end.
  - eexists. split; reflexivity.
  - eexists. split; reflexivity.
Qed.

Definition phase1_surface_reference_source_spine
  (tokens : list ConcreteToken) : option Phase1SurfaceSourceSpine :=
  match phase1_surface_reference_parse tokens with
  | Some ([], ResultTree tree) =>
      phase1_surface_normalize_source_spine tree
  | _ => None
  end.

Theorem phase1_surface_reference_source_spine_sound :
  forall tokens spine,
    phase1_surface_reference_source_spine tokens = Some spine ->
    exists tree,
      phase1_surface_reference_parse tokens =
        Some ([], ResultTree tree) /\
      phase1_surface_source_spine_tree spine = tree /\
      Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens spine Hnormalize.
  unfold phase1_surface_reference_source_spine in Hnormalize.
  destruct (phase1_surface_reference_parse tokens)
    as [[rest result] |] eqn:Hparse;
    try discriminate Hnormalize.
  destruct rest as [| token rest]; try discriminate Hnormalize.
  destruct result as [tree | trees]; try discriminate Hnormalize.
  exists tree.
  split.
  - reflexivity.
  - split.
    + eapply phase1_surface_normalize_source_spine_round_trip.
      exact Hnormalize.
    + unfold phase1_surface_reference_parse in Hparse.
      eapply phase1_surface_predictive_parse_fuel_ordinary_sound.
      exact Hparse.
Qed.
