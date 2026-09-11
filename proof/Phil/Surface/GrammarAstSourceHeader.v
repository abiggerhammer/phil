From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSourceSpine
  GrammarParserProductionKernel.

Import ListNotations.
Open Scope string_scope.

(*
  Second universal proof-side AST correspondence carrier for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  GrammarAstSourceSpine proves that every certified complete parse has the
  exact outer source_file shape.  This layer refines the module/import header
  payloads into semantic name lists while deliberately leaving top-level
  declaration subtrees unchanged for the next tranche.
*)

Record Phase1SurfaceNameList : Type := {
  phase1_name_list_first : string;
  phase1_name_list_rest : list string
}.

Record Phase1SurfaceImportHeader : Type := {
  phase1_import_header_name : Phase1SurfaceNameList;
  phase1_import_header_selection : option Phase1SurfaceNameList
}.

Record Phase1SurfaceSourceHeader : Type := {
  phase1_source_header_module : option Phase1SurfaceNameList;
  phase1_source_header_imports : list Phase1SurfaceImportHeader;
  phase1_source_header_top_levels : list ParseTree
}.

(* Small structural destructors keep the normalization proofs independent of
   Rocq's compilation order for nested constructor patterns. *)

Definition phase1_surface_expect_nonterminal
  (expected : string)
  (tree : ParseTree) : option ParseTree :=
  match tree with
  | PTNonterminal actual body =>
      if String.eqb actual expected then Some body else None
  | _ => None
  end.

Lemma phase1_surface_expect_nonterminal_round_trip :
  forall expected tree body,
    phase1_surface_expect_nonterminal expected tree = Some body ->
    tree = PTNonterminal expected body.
Proof.
  intros expected tree body Hexpect.
  destruct tree as
    [root_literal
    | root_class root_lexeme
    | actual actual_body
    | root_trees
    | root_index root_branch
    |
    | root_optional_body
    | root_repeated];
    cbn in Hexpect; try discriminate Hexpect.
  destruct (String.eqb actual expected) eqn:Heq;
    cbn in Hexpect; try discriminate Hexpect.
  apply String.eqb_eq in Heq.
  subst actual.
  inversion Hexpect; subst.
  reflexivity.
Qed.

Definition phase1_surface_expect_sequence
  (tree : ParseTree) : option (list ParseTree) :=
  match tree with
  | PTSequence items => Some items
  | _ => None
  end.

Lemma phase1_surface_expect_sequence_round_trip :
  forall tree items,
    phase1_surface_expect_sequence tree = Some items ->
    tree = PTSequence items.
Proof.
  intros tree items Hexpect.
  destruct tree;
    cbn in Hexpect; try discriminate Hexpect.
  inversion Hexpect; subst.
  reflexivity.
Qed.

Definition phase1_surface_expect_literal
  (expected : string)
  (tree : ParseTree) : option unit :=
  match tree with
  | PTLiteral actual =>
      if String.eqb actual expected then Some tt else None
  | _ => None
  end.

Lemma phase1_surface_expect_literal_round_trip :
  forall expected tree,
    phase1_surface_expect_literal expected tree = Some tt ->
    tree = PTLiteral expected.
Proof.
  intros expected tree Hexpect.
  destruct tree as
    [actual
    | root_class root_lexeme
    | root_name root_body
    | root_trees
    | root_index root_branch
    |
    | root_optional_body
    | root_repeated];
    cbn in Hexpect; try discriminate Hexpect.
  destruct (String.eqb actual expected) eqn:Heq;
    cbn in Hexpect; try discriminate Hexpect.
  apply String.eqb_eq in Heq.
  subst actual.
  reflexivity.
Qed.

Definition phase1_surface_expect_lexical
  (expected_class : string)
  (tree : ParseTree) : option string :=
  match tree with
  | PTLexical actual_class value =>
      if String.eqb actual_class expected_class then Some value else None
  | _ => None
  end.

Lemma phase1_surface_expect_lexical_round_trip :
  forall expected_class tree value,
    phase1_surface_expect_lexical expected_class tree = Some value ->
    tree = PTLexical expected_class value.
Proof.
  intros expected_class tree value Hexpect.
  destruct tree as
    [root_literal
    | actual_class actual_value
    | root_name root_body
    | root_trees
    | root_index root_branch
    |
    | root_optional_body
    | root_repeated];
    cbn in Hexpect; try discriminate Hexpect.
  destruct (String.eqb actual_class expected_class) eqn:Heq;
    cbn in Hexpect; try discriminate Hexpect.
  apply String.eqb_eq in Heq.
  subst actual_class.
  inversion Hexpect; subst.
  reflexivity.
Qed.

Definition phase1_surface_expect_repetition
  (tree : ParseTree) : option (list ParseTree) :=
  match tree with
  | PTRepetition items => Some items
  | _ => None
  end.

Lemma phase1_surface_expect_repetition_round_trip :
  forall tree items,
    phase1_surface_expect_repetition tree = Some items ->
    tree = PTRepetition items.
Proof.
  intros tree items Hexpect.
  destruct tree;
    cbn in Hexpect; try discriminate Hexpect.
  inversion Hexpect; subst.
  reflexivity.
Qed.

Definition phase1_surface_expect_optional
  (tree : ParseTree) : option (option ParseTree) :=
  match tree with
  | PTOptionalNone => Some None
  | PTOptionalSome body => Some (Some body)
  | _ => None
  end.

Lemma phase1_surface_expect_optional_round_trip :
  forall tree body,
    phase1_surface_expect_optional tree = Some body ->
    tree =
      match body with
      | None => PTOptionalNone
      | Some body_tree => PTOptionalSome body_tree
      end.
Proof.
  intros tree body Hexpect.
  destruct tree;
    cbn in Hexpect; try discriminate Hexpect;
    inversion Hexpect; subst; reflexivity.
Qed.

Definition phase1_surface_exact2 {A : Type}
  (items : list A) : option (A * A) :=
  match items with
  | [a; b] => Some (a, b)
  | _ => None
  end.

Lemma phase1_surface_exact2_round_trip {A : Type} :
  forall (items : list A) (a b : A),
    phase1_surface_exact2 items = Some (a, b) ->
    items = [a; b].
Proof.
  intros items a b Hitems.
  destruct items as [|x xs]; cbn in Hitems; try discriminate Hitems.
  destruct xs as [|y ys]; cbn in Hitems; try discriminate Hitems.
  destruct ys as [|z zs]; cbn in Hitems; try discriminate Hitems.
  inversion Hitems; subst.
  reflexivity.
Qed.

Definition phase1_surface_exact3 {A : Type}
  (items : list A) : option (A * A * A) :=
  match items with
  | [a; b; c] => Some (a, b, c)
  | _ => None
  end.

Lemma phase1_surface_exact3_round_trip {A : Type} :
  forall (items : list A) (a b c : A),
    phase1_surface_exact3 items = Some (a, b, c) ->
    items = [a; b; c].
Proof.
  intros items a b c Hitems.
  destruct items as [|w ws]; cbn in Hitems; try discriminate Hitems.
  destruct ws as [|x xs]; cbn in Hitems; try discriminate Hitems.
  destruct xs as [|y ys]; cbn in Hitems; try discriminate Hitems.
  destruct ys as [|z zs]; cbn in Hitems; try discriminate Hitems.
  inversion Hitems; subst.
  reflexivity.
Qed.

Definition phase1_surface_exact4 {A : Type}
  (items : list A) : option (A * A * A * A) :=
  match items with
  | [a; b; c; d] => Some (a, b, c, d)
  | _ => None
  end.

Lemma phase1_surface_exact4_round_trip {A : Type} :
  forall (items : list A) (a b c d : A),
    phase1_surface_exact4 items = Some (a, b, c, d) ->
    items = [a; b; c; d].
Proof.
  intros items a b c d Hitems.
  destruct items as [|v vs]; cbn in Hitems; try discriminate Hitems.
  destruct vs as [|w ws]; cbn in Hitems; try discriminate Hitems.
  destruct ws as [|x xs]; cbn in Hitems; try discriminate Hitems.
  destruct xs as [|y ys]; cbn in Hitems; try discriminate Hitems.
  destruct ys as [|z zs]; cbn in Hitems; try discriminate Hitems.
  inversion Hitems; subst.
  reflexivity.
Qed.

Definition phase1_surface_identifier_tree (value : string) : ParseTree :=
  PTNonterminal "identifier" (PTLexical "IDENTIFIER" value).

Definition phase1_surface_normalize_identifier
  (tree : ParseTree) : option string :=
  match phase1_surface_expect_nonterminal "identifier" tree with
  | Some body => phase1_surface_expect_lexical "IDENTIFIER" body
  | None => None
  end.

Theorem phase1_surface_normalize_identifier_round_trip :
  forall tree value,
    phase1_surface_normalize_identifier tree = Some value ->
    phase1_surface_identifier_tree value = tree.
Proof.
  intros tree value Hnormalize.
  unfold phase1_surface_normalize_identifier in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "identifier" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_lexical "IDENTIFIER" body)
    as [actual |] eqn:Hlex; try discriminate Hnormalize.
  inversion Hnormalize; subst actual.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "identifier" tree body Hnode).
  rewrite (phase1_surface_expect_lexical_round_trip
    "IDENTIFIER" body value Hlex).
  reflexivity.
Qed.

Definition phase1_surface_name_suffix_tree
  (separator value : string) : ParseTree :=
  PTSequence
    [ PTLiteral separator;
      phase1_surface_identifier_tree value
    ].

Definition phase1_surface_normalize_name_suffix
  (separator : string)
  (tree : ParseTree) : option string :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (separator_tree, identifier_tree) =>
          match phase1_surface_expect_literal separator separator_tree with
          | Some tt => phase1_surface_normalize_identifier identifier_tree
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_name_suffix_round_trip :
  forall separator tree value,
    phase1_surface_normalize_name_suffix separator tree = Some value ->
    phase1_surface_name_suffix_tree separator value = tree.
Proof.
  intros separator tree value Hnormalize.
  unfold phase1_surface_normalize_name_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[separator_tree identifier_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal separator separator_tree)
    as [[] |] eqn:Hseparator; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_identifier_round_trip
      identifier_tree value Hnormalize) as Hidentifier.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items separator_tree identifier_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    separator separator_tree Hseparator).
  rewrite Hidentifier.
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_name_suffixes
  (separator : string)
  (trees : list ParseTree) : option (list string) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_name_suffix separator tree,
            phase1_surface_normalize_name_suffixes separator rest with
      | Some value, Some values => Some (value :: values)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_name_suffixes_round_trip :
  forall separator trees values,
    phase1_surface_normalize_name_suffixes separator trees = Some values ->
    map (phase1_surface_name_suffix_tree separator) values = trees.
Proof.
  intros separator trees.
  induction trees as [|tree rest IH]; intros values Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_name_suffix separator tree)
      as [value |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_name_suffixes separator rest)
      as [rest_values |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_name_suffix_round_trip.
      exact Htree.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_name_list_tree
  (nonterminal separator : string)
  (names : Phase1SurfaceNameList) : ParseTree :=
  PTNonterminal nonterminal
    (PTSequence
      [ phase1_surface_identifier_tree (phase1_name_list_first names);
        PTRepetition
          (map
            (phase1_surface_name_suffix_tree separator)
            (phase1_name_list_rest names))
      ]).

Definition phase1_surface_normalize_name_list
  (nonterminal separator : string)
  (tree : ParseTree) : option Phase1SurfaceNameList :=
  match phase1_surface_expect_nonterminal nonterminal tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (first_tree, suffix_tree) =>
              match phase1_surface_expect_repetition suffix_tree with
              | Some suffix_trees =>
                  match phase1_surface_normalize_identifier first_tree,
                        phase1_surface_normalize_name_suffixes separator suffix_trees with
                  | Some first_value, Some rest_values =>
                      Some
                        {| phase1_name_list_first := first_value;
                           phase1_name_list_rest := rest_values |}
                  | _, _ => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_name_list_round_trip :
  forall nonterminal separator tree names,
    phase1_surface_normalize_name_list nonterminal separator tree = Some names ->
    phase1_surface_name_list_tree nonterminal separator names = tree.
Proof.
  intros nonterminal separator tree names Hnormalize.
  unfold phase1_surface_normalize_name_list in Hnormalize.
  destruct (phase1_surface_expect_nonterminal nonterminal tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[first_tree suffix_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition suffix_tree)
    as [suffix_trees |] eqn:Hrepetition; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier first_tree)
    as [first_value |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_name_suffixes separator suffix_trees)
    as [rest_values |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst names.
  unfold phase1_surface_name_list_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    nonterminal tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact2_round_trip items first_tree suffix_tree Hitems).
  rewrite (phase1_surface_expect_repetition_round_trip
    suffix_tree suffix_trees Hrepetition).
  rewrite (phase1_surface_normalize_identifier_round_trip
    first_tree first_value Hfirst).
  rewrite (phase1_surface_normalize_name_suffixes_round_trip
    separator suffix_trees rest_values Hrest).
  reflexivity.
Qed.

Definition phase1_surface_qualified_name_tree :=
  phase1_surface_name_list_tree "qualified_name" ".".

Definition phase1_surface_normalize_qualified_name :=
  phase1_surface_normalize_name_list "qualified_name" ".".

Definition phase1_surface_identifier_list_tree :=
  phase1_surface_name_list_tree "identifier_list" ",".

Definition phase1_surface_normalize_identifier_list :=
  phase1_surface_normalize_name_list "identifier_list" ",".

Definition phase1_surface_module_decl_tree
  (name : Phase1SurfaceNameList) : ParseTree :=
  PTNonterminal "module_decl"
    (PTSequence
      [ PTLiteral "module";
        phase1_surface_qualified_name_tree name;
        PTLiteral ";"
      ]).

Definition phase1_surface_normalize_module_decl
  (tree : ParseTree) : option Phase1SurfaceNameList :=
  match phase1_surface_expect_nonterminal "module_decl" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact3 items with
          | Some (keyword_tree, qualified_name_tree, terminator_tree) =>
              match phase1_surface_expect_literal "module" keyword_tree,
                    phase1_surface_expect_literal ";" terminator_tree with
              | Some tt, Some tt =>
                  phase1_surface_normalize_qualified_name qualified_name_tree
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_module_decl_round_trip :
  forall tree name,
    phase1_surface_normalize_module_decl tree = Some name ->
    phase1_surface_module_decl_tree name = tree.
Proof.
  intros tree name Hnormalize.
  unfold phase1_surface_normalize_module_decl in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "module_decl" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[keyword_tree qualified_name_tree] terminator_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "module" keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ";" terminator_tree)
    as [[] |] eqn:Hterminator; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_name_list_round_trip
      "qualified_name" "." qualified_name_tree name Hnormalize) as Hname.
  unfold phase1_surface_module_decl_tree,
    phase1_surface_qualified_name_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "module_decl" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items keyword_tree qualified_name_tree terminator_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "module" keyword_tree Hkeyword).
  rewrite (phase1_surface_expect_literal_round_trip
    ";" terminator_tree Hterminator).
  rewrite Hname.
  reflexivity.
Qed.

Definition phase1_surface_import_selection_tree
  (selection : option Phase1SurfaceNameList) : ParseTree :=
  match selection with
  | None => PTOptionalNone
  | Some identifiers =>
      PTOptionalSome
        (PTSequence
          [ PTLiteral "{";
            phase1_surface_identifier_list_tree identifiers;
            PTLiteral "}"
          ])
  end.

Definition phase1_surface_normalize_import_selection
  (tree : ParseTree) : option (option Phase1SurfaceNameList) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some body) =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact3 items with
          | Some (open_tree, identifiers_tree, close_tree) =>
              match phase1_surface_expect_literal "{" open_tree,
                    phase1_surface_expect_literal "}" close_tree with
              | Some tt, Some tt =>
                  match phase1_surface_normalize_identifier_list identifiers_tree with
                  | Some identifiers => Some (Some identifiers)
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

Theorem phase1_surface_normalize_import_selection_round_trip :
  forall tree selection,
    phase1_surface_normalize_import_selection tree = Some selection ->
    phase1_surface_import_selection_tree selection = tree.
Proof.
  intros tree selection Hnormalize.
  unfold phase1_surface_normalize_import_selection in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_expect_sequence body)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact3 items)
      as [[[open_tree identifiers_tree] close_tree] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal "{" open_tree)
      as [[] |] eqn:Hopen; try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal "}" close_tree)
      as [[] |] eqn:Hclose; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_identifier_list identifiers_tree)
      as [identifiers |] eqn:Hidentifiers; try discriminate Hnormalize.
    inversion Hnormalize; subst selection.
    cbn.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
    rewrite (phase1_surface_exact3_round_trip
      items open_tree identifiers_tree close_tree Hitems).
    rewrite (phase1_surface_expect_literal_round_trip
      "{" open_tree Hopen).
    rewrite (phase1_surface_expect_literal_round_trip
      "}" close_tree Hclose).
    unfold phase1_surface_identifier_list_tree,
      phase1_surface_normalize_identifier_list in Hidentifiers.
    rewrite (phase1_surface_normalize_name_list_round_trip
      "identifier_list" "," identifiers_tree identifiers Hidentifiers).
    reflexivity.
  - inversion Hnormalize; subst selection.
    cbn.
    rewrite (phase1_surface_expect_optional_round_trip
      tree None Hoptional).
    reflexivity.
Qed.

Definition phase1_surface_import_decl_tree
  (import_header : Phase1SurfaceImportHeader) : ParseTree :=
  PTNonterminal "import_decl"
    (PTSequence
      [ PTLiteral "import";
        phase1_surface_qualified_name_tree
          (phase1_import_header_name import_header);
        phase1_surface_import_selection_tree
          (phase1_import_header_selection import_header);
        PTLiteral ";"
      ]).

Definition phase1_surface_normalize_import_decl
  (tree : ParseTree) : option Phase1SurfaceImportHeader :=
  match phase1_surface_expect_nonterminal "import_decl" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact4 items with
          | Some (keyword_tree, qualified_name_tree, selection_tree, terminator_tree) =>
              match phase1_surface_expect_literal "import" keyword_tree,
                    phase1_surface_expect_literal ";" terminator_tree with
              | Some tt, Some tt =>
                  match phase1_surface_normalize_qualified_name qualified_name_tree,
                        phase1_surface_normalize_import_selection selection_tree with
                  | Some name, Some selection =>
                      Some
                        {| phase1_import_header_name := name;
                           phase1_import_header_selection := selection |}
                  | _, _ => None
                  end
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_import_decl_round_trip :
  forall tree import_header,
    phase1_surface_normalize_import_decl tree = Some import_header ->
    phase1_surface_import_decl_tree import_header = tree.
Proof.
  intros tree import_header Hnormalize.
  unfold phase1_surface_normalize_import_decl in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "import_decl" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact4 items)
    as [[[[keyword_tree qualified_name_tree] selection_tree] terminator_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "import" keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ";" terminator_tree)
    as [[] |] eqn:Hterminator; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_qualified_name qualified_name_tree)
    as [name |] eqn:Hname; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_import_selection selection_tree)
    as [selection |] eqn:Hselection; try discriminate Hnormalize.
  inversion Hnormalize; subst import_header.
  cbn.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "import_decl" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact4_round_trip
    items keyword_tree qualified_name_tree selection_tree terminator_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "import" keyword_tree Hkeyword).
  rewrite (phase1_surface_expect_literal_round_trip
    ";" terminator_tree Hterminator).
  unfold phase1_surface_qualified_name_tree,
    phase1_surface_normalize_qualified_name in Hname.
  rewrite (phase1_surface_normalize_name_list_round_trip
    "qualified_name" "." qualified_name_tree name Hname).
  rewrite (phase1_surface_normalize_import_selection_round_trip
    selection_tree selection Hselection).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_import_decls
  (trees : list ParseTree) : option (list Phase1SurfaceImportHeader) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_import_decl tree,
            phase1_surface_normalize_import_decls rest with
      | Some import_header, Some import_headers =>
          Some (import_header :: import_headers)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_import_decls_round_trip :
  forall trees import_headers,
    phase1_surface_normalize_import_decls trees = Some import_headers ->
    map phase1_surface_import_decl_tree import_headers = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros import_headers Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_import_decl tree)
      as [import_header |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_import_decls rest)
      as [rest_headers |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_import_decl_round_trip.
      exact Htree.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_normalize_optional_module
  (module_tree : option ParseTree) : option (option Phase1SurfaceNameList) :=
  match module_tree with
  | None => Some None
  | Some tree =>
      match phase1_surface_normalize_module_decl tree with
      | Some name => Some (Some name)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_optional_module_round_trip :
  forall module_tree module_name,
    phase1_surface_normalize_optional_module module_tree = Some module_name ->
    match module_name with
    | None => PTOptionalNone
    | Some name => PTOptionalSome (phase1_surface_module_decl_tree name)
    end =
    match module_tree with
    | None => PTOptionalNone
    | Some tree => PTOptionalSome tree
    end.
Proof.
  intros module_tree module_name Hnormalize.
  destruct module_tree as [tree |].
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_module_decl tree)
      as [name |] eqn:Htree; try discriminate Hnormalize.
    inversion Hnormalize; subst.
    cbn.
    rewrite (phase1_surface_normalize_module_decl_round_trip
      tree name Htree).
    reflexivity.
  - cbn in Hnormalize.
    inversion Hnormalize; subst.
    reflexivity.
Qed.

Definition phase1_surface_source_header_tree
  (header : Phase1SurfaceSourceHeader) : ParseTree :=
  PTNonterminal phase1_surface_start
    (PTSequence
      [ match phase1_source_header_module header with
        | None => PTOptionalNone
        | Some name => PTOptionalSome (phase1_surface_module_decl_tree name)
        end;
        PTRepetition
          (map
            phase1_surface_import_decl_tree
            (phase1_source_header_imports header));
        PTRepetition (phase1_source_header_top_levels header)
      ]).

Definition phase1_surface_normalize_source_header
  (spine : Phase1SurfaceSourceSpine) : option Phase1SurfaceSourceHeader :=
  match phase1_surface_normalize_optional_module
          (phase1_source_spine_module spine),
        phase1_surface_normalize_import_decls
          (phase1_source_spine_imports spine) with
  | Some module_name, Some import_headers =>
      Some
        {| phase1_source_header_module := module_name;
           phase1_source_header_imports := import_headers;
           phase1_source_header_top_levels :=
             phase1_source_spine_top_levels spine |}
  | _, _ => None
  end.

Theorem phase1_surface_normalize_source_header_round_trip :
  forall spine header,
    phase1_surface_normalize_source_header spine = Some header ->
    phase1_surface_source_header_tree header =
      phase1_surface_source_spine_tree spine.
Proof.
  intros spine header Hnormalize.
  destruct spine as [module_tree import_trees top_levels].
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_optional_module module_tree)
    as [module_name |] eqn:Hmodule; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_import_decls import_trees)
    as [import_headers |] eqn:Himports; try discriminate Hnormalize.
  inversion Hnormalize; subst.
  cbn.
  rewrite (phase1_surface_normalize_import_decls_round_trip
    import_trees import_headers Himports).
  pose proof
    (phase1_surface_normalize_optional_module_round_trip
      module_tree module_name Hmodule) as Hmodule_round_trip.
  destruct module_tree as [module_body |];
    destruct module_name as [name |];
    cbn in Hmodule_round_trip;
    try discriminate Hmodule_round_trip;
    rewrite Hmodule_round_trip;
    reflexivity.
Qed.

Definition phase1_surface_normalize_source_header_tree
  (tree : ParseTree) : option Phase1SurfaceSourceHeader :=
  match phase1_surface_normalize_source_spine tree with
  | Some spine => phase1_surface_normalize_source_header spine
  | None => None
  end.

Theorem phase1_surface_normalize_source_header_tree_round_trip :
  forall tree header,
    phase1_surface_normalize_source_header_tree tree = Some header ->
    phase1_surface_source_header_tree header = tree.
Proof.
  intros tree header Hnormalize.
  unfold phase1_surface_normalize_source_header_tree in Hnormalize.
  destruct (phase1_surface_normalize_source_spine tree)
    as [spine |] eqn:Hspine; try discriminate Hnormalize.
  transitivity (phase1_surface_source_spine_tree spine).
  - eapply phase1_surface_normalize_source_header_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_source_spine_round_trip.
    exact Hspine.
Qed.

Definition phase1_surface_reference_source_header
  (tokens : list ConcreteToken) : option Phase1SurfaceSourceHeader :=
  match phase1_surface_reference_parse tokens with
  | Some ([], ResultTree tree) =>
      phase1_surface_normalize_source_header_tree tree
  | _ => None
  end.

Theorem phase1_surface_reference_source_header_sound :
  forall tokens header,
    phase1_surface_reference_source_header tokens = Some header ->
    exists tree,
      phase1_surface_reference_parse tokens =
        Some ([], ResultTree tree) /\
      phase1_surface_source_header_tree header = tree /\
      Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens header Hnormalize.
  unfold phase1_surface_reference_source_header in Hnormalize.
  destruct (phase1_surface_reference_parse tokens)
    as [[rest result] |] eqn:Hparse; try discriminate Hnormalize.
  destruct rest as [|token rest]; try discriminate Hnormalize.
  destruct result as [tree | trees]; try discriminate Hnormalize.
  exists tree.
  split.
  - reflexivity.
  - split.
    + eapply phase1_surface_normalize_source_header_tree_round_trip.
      exact Hnormalize.
    + unfold phase1_surface_reference_parse in Hparse.
      eapply phase1_surface_predictive_parse_fuel_ordinary_sound.
      exact Hparse.
Qed.
