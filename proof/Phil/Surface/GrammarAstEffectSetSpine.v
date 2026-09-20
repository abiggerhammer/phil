From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsSpine
  GrammarAstStaticReferenceSpine.

Import ListNotations.
Open Scope string_scope.

(*
  First Rocq refinement for effect_set_expression.

  This slice closes the exact two-way effect-set choice and the complete
  brace-delimited literal/list shell. Each literal element is retained as an
  exact certified effect_expression ParseTree for the dedicated effect-expression
  payload slice. The static-reference branch reuses the established
  Phase1SurfaceStaticReferenceSpine.
*)

Definition phase1_surface_effect_expression_tree
  (tree : ParseTree) : ParseTree := tree.

Definition phase1_surface_normalize_effect_expression_node
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_validate_named_node "effect_expression" tree with
  | Some tt => Some tree
  | None => None
  end.

Theorem phase1_surface_normalize_effect_expression_node_round_trip :
  forall tree refined,
    phase1_surface_normalize_effect_expression_node tree = Some refined ->
    phase1_surface_effect_expression_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_effect_expression_node in Hnormalize.
  destruct
    (phase1_surface_validate_named_node "effect_expression" tree)
    as [[] |] eqn:Hvalidate; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  reflexivity.
Qed.

Definition phase1_surface_effect_set_suffix_tree
  (effect : ParseTree) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_effect_expression_tree effect
    ].

Definition phase1_surface_normalize_effect_set_suffix
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (comma_tree, effect_tree) =>
          match phase1_surface_expect_literal "," comma_tree,
                phase1_surface_normalize_effect_expression_node effect_tree with
          | Some tt, Some effect => Some effect
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_effect_set_suffix_round_trip :
  forall tree effect,
    phase1_surface_normalize_effect_set_suffix tree = Some effect ->
    phase1_surface_effect_set_suffix_tree effect = tree.
Proof.
  intros tree effect Hnormalize.
  unfold phase1_surface_normalize_effect_set_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[comma_tree effect_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma_tree)
    as [[] |] eqn:Hcomma; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_effect_expression_node effect_tree)
    as [actual |] eqn:Heffect; try discriminate Hnormalize.
  inversion Hnormalize; subst effect.
  unfold phase1_surface_effect_set_suffix_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items comma_tree effect_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "," comma_tree Hcomma).
  rewrite
    (phase1_surface_normalize_effect_expression_node_round_trip
      effect_tree actual Heffect).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_effect_set_suffixes
  (trees : list ParseTree) : option (list ParseTree) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_effect_set_suffix tree,
            phase1_surface_normalize_effect_set_suffixes rest with
      | Some effect, Some effects => Some (effect :: effects)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_effect_set_suffixes_round_trip :
  forall trees effects,
    phase1_surface_normalize_effect_set_suffixes trees = Some effects ->
    map phase1_surface_effect_set_suffix_tree effects = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros effects Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst effects.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_effect_set_suffix tree)
      as [effect |] eqn:Heffect; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_effect_set_suffixes rest)
      as [rest_effects |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst effects.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_effect_set_suffix_round_trip.
      exact Heffect.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_effect_set_entries_tree
  (effects : list ParseTree) : ParseTree :=
  match effects with
  | [] => PTOptionalNone
  | first :: rest =>
      PTOptionalSome
        (PTSequence
          [ phase1_surface_effect_expression_tree first;
            PTRepetition
              (map phase1_surface_effect_set_suffix_tree rest)
          ])
  end.

Definition phase1_surface_normalize_effect_set_entries
  (tree : ParseTree) : option (list ParseTree) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some []
  | Some (Some body) =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (first_tree, rest_tree) =>
              match phase1_surface_normalize_effect_expression_node first_tree,
                    phase1_surface_expect_repetition rest_tree with
              | Some first, Some rest_trees =>
                  match
                    phase1_surface_normalize_effect_set_suffixes rest_trees
                  with
                  | Some rest => Some (first :: rest)
                  | None => None
                  end
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_effect_set_entries_round_trip :
  forall tree effects,
    phase1_surface_normalize_effect_set_entries tree = Some effects ->
    phase1_surface_effect_set_entries_tree effects = tree.
Proof.
  intros tree effects Hnormalize.
  unfold phase1_surface_normalize_effect_set_entries in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_expect_sequence body)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact2 items)
      as [[first_tree rest_tree] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct (phase1_surface_normalize_effect_expression_node first_tree)
      as [first |] eqn:Hfirst; try discriminate Hnormalize.
    destruct (phase1_surface_expect_repetition rest_tree)
      as [rest_trees |] eqn:Hrepetition; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_effect_set_suffixes rest_trees)
      as [rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst effects.
    unfold phase1_surface_effect_set_entries_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_expect_sequence_round_trip
      body items Hsequence).
    rewrite (phase1_surface_exact2_round_trip
      items first_tree rest_tree Hitems).
    rewrite
      (phase1_surface_normalize_effect_expression_node_round_trip
        first_tree first Hfirst).
    rewrite (phase1_surface_expect_repetition_round_trip
      rest_tree rest_trees Hrepetition).
    rewrite <-
      (phase1_surface_normalize_effect_set_suffixes_round_trip
        rest_trees rest Hrest).
    reflexivity.
  - inversion Hnormalize; subst effects.
    unfold phase1_surface_effect_set_entries_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceEffectSetLiteralSpine : Type := {
  phase1_effect_set_literal_spine_effects : list ParseTree
}.

Definition phase1_surface_effect_set_literal_spine_tree
  (literal : Phase1SurfaceEffectSetLiteralSpine) : ParseTree :=
  PTNonterminal "effect_set_literal"
    (PTSequence
      [ PTLiteral "{";
        phase1_surface_effect_set_entries_tree
          (phase1_effect_set_literal_spine_effects literal);
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_effect_set_literal_spine
  (tree : ParseTree) : option Phase1SurfaceEffectSetLiteralSpine :=
  match phase1_surface_expect_nonterminal "effect_set_literal" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact3 items with
          | Some (open_tree, entries_tree, close_tree) =>
              match phase1_surface_expect_literal "{" open_tree,
                    phase1_surface_normalize_effect_set_entries entries_tree,
                    phase1_surface_expect_literal "}" close_tree with
              | Some tt, Some effects, Some tt =>
                  Some
                    {| phase1_effect_set_literal_spine_effects := effects |}
              | _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_effect_set_literal_spine_round_trip :
  forall tree literal,
    phase1_surface_normalize_effect_set_literal_spine tree = Some literal ->
    phase1_surface_effect_set_literal_spine_tree literal = tree.
Proof.
  intros tree literal Hnormalize.
  unfold phase1_surface_normalize_effect_set_literal_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "effect_set_literal" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[open_tree entries_tree] close_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "{" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_effect_set_entries entries_tree)
    as [effects |] eqn:Hentries; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "}" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  inversion Hnormalize; subst literal.
  unfold phase1_surface_effect_set_literal_spine_tree.
  cbn.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "effect_set_literal" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip
    body items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items open_tree entries_tree close_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "{" open_tree Hopen).
  rewrite
    (phase1_surface_normalize_effect_set_entries_round_trip
      entries_tree effects Hentries).
  rewrite (phase1_surface_expect_literal_round_trip
    "}" close_tree Hclose).
  reflexivity.
Qed.

Inductive Phase1SurfaceEffectSetSpine : Type :=
| Phase1EffectSetLiteral
    (literal : Phase1SurfaceEffectSetLiteralSpine)
| Phase1EffectSetReference
    (reference : Phase1SurfaceStaticReferenceSpine).

Definition phase1_surface_effect_set_spine_tree
  (effects : Phase1SurfaceEffectSetSpine) : ParseTree :=
  match effects with
  | Phase1EffectSetLiteral literal =>
      PTNonterminal "effect_set_expression"
        (PTAlternative 0
          (phase1_surface_effect_set_literal_spine_tree literal))
  | Phase1EffectSetReference reference =>
      PTNonterminal "effect_set_expression"
        (PTAlternative 1
          (phase1_surface_static_reference_spine_tree reference))
  end.

Definition phase1_surface_normalize_effect_set_spine
  (tree : ParseTree) : option Phase1SurfaceEffectSetSpine :=
  match phase1_surface_expect_nonterminal "effect_set_expression" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          match phase1_surface_normalize_effect_set_literal_spine selected with
          | Some literal => Some (Phase1EffectSetLiteral literal)
          | None => None
          end
      | Some (1, selected) =>
          match phase1_surface_normalize_static_reference_spine selected with
          | Some reference => Some (Phase1EffectSetReference reference)
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_effect_set_spine_round_trip :
  forall tree effects,
    phase1_surface_normalize_effect_set_spine tree = Some effects ->
    phase1_surface_effect_set_spine_tree effects = tree.
Proof.
  intros tree effects Hnormalize.
  unfold phase1_surface_normalize_effect_set_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "effect_set_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct (phase1_surface_normalize_effect_set_literal_spine selected)
      as [literal |] eqn:Hliteral; try discriminate Hnormalize.
    inversion Hnormalize; subst effects.
    unfold phase1_surface_effect_set_spine_tree.
    rewrite (phase1_surface_expect_nonterminal_round_trip
      "effect_set_expression" tree body Hnode).
    rewrite (phase1_surface_expect_alternative_round_trip
      body 0 selected Halternative).
    rewrite
      (phase1_surface_normalize_effect_set_literal_spine_round_trip
        selected literal Hliteral).
    reflexivity.
  - destruct index as [|index].
    + destruct (phase1_surface_normalize_static_reference_spine selected)
        as [reference |] eqn:Hreference; try discriminate Hnormalize.
      inversion Hnormalize; subst effects.
      unfold phase1_surface_effect_set_spine_tree.
      rewrite (phase1_surface_expect_nonterminal_round_trip
        "effect_set_expression" tree body Hnode).
      rewrite (phase1_surface_expect_alternative_round_trip
        body 1 selected Halternative).
      rewrite
        (phase1_surface_normalize_static_reference_spine_round_trip
          selected reference Hreference).
      reflexivity.
    + discriminate Hnormalize.
Qed.
