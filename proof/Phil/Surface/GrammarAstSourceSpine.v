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
    [literal
    | class lexeme
    | name body
    | trees
    | index branch
    |
    | optional_body
    | repeated];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct body as
    [literal
    | class lexeme
    | child_name child_body
    | fields
    | index branch
    |
    | optional_body
    | repeated];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct fields as [| module_part fields];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct fields as [| imports_part fields];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct fields as [| top_levels_part fields];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct fields as [| extra fields];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct imports_part as
    [literal
    | class lexeme
    | child_name child_body
    | sequence
    | index branch
    |
    | optional_body
    | imports];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct top_levels_part as
    [literal
    | class lexeme
    | child_name child_body
    | sequence
    | index branch
    |
    | optional_body
    | top_levels];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct (String.eqb name phase1_surface_start) eqn:Hname;
    cbn in Hnormalize; try discriminate Hnormalize.
  apply String.eqb_eq in Hname.
  subst name.
  destruct module_part as
    [literal
    | class lexeme
    | child_name child_body
    | sequence
    | index branch
    |
    | module_tree
    | repeated];
    cbn in Hnormalize; try discriminate Hnormalize;
    inversion Hnormalize; subst; reflexivity.
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
  - exact Hparse.
  - split.
    + eapply phase1_surface_normalize_source_spine_round_trip.
      exact Hnormalize.
    + unfold phase1_surface_reference_parse in Hparse.
      eapply phase1_surface_predictive_parse_fuel_ordinary_sound.
      exact Hparse.
Qed.
