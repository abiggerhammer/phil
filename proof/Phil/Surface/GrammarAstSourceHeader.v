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

Definition phase1_surface_identifier_tree (value : string) : ParseTree :=
  PTNonterminal "identifier" (PTLexical "IDENTIFIER" value).

Definition phase1_surface_normalize_identifier
  (tree : ParseTree) : option string :=
  match tree with
  | PTNonterminal name (PTLexical class value) =>
      if String.eqb name "identifier" then
        if String.eqb class "IDENTIFIER" then Some value else None
      else None
  | _ => None
  end.

Theorem phase1_surface_normalize_identifier_round_trip :
  forall tree value,
    phase1_surface_normalize_identifier tree = Some value ->
    phase1_surface_identifier_tree value = tree.
Proof.
  intros tree value Hnormalize.
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
    | class lexeme
    | body_child_name body_child_body
    | body_trees
    | body_index body_branch
    |
    | body_optional_body
    | body_repeated];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct (String.eqb name "identifier") eqn:Hname;
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct (String.eqb class "IDENTIFIER") eqn:Hclass;
    cbn in Hnormalize; try discriminate Hnormalize.
  apply String.eqb_eq in Hname.
  apply String.eqb_eq in Hclass.
  subst name.
  subst class.
  inversion Hnormalize; subst.
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
  match tree with
  | PTSequence [PTLiteral actual_separator; identifier_tree] =>
      if String.eqb actual_separator separator then
        phase1_surface_normalize_identifier identifier_tree
      else None
  | _ => None
  end.

Theorem phase1_surface_normalize_name_suffix_round_trip :
  forall separator tree value,
    phase1_surface_normalize_name_suffix separator tree = Some value ->
    phase1_surface_name_suffix_tree separator value = tree.
Proof.
  intros separator tree value Hnormalize.
  destruct tree as
    [root_literal
    | root_class root_lexeme
    | root_name root_body
    | fields
    | root_index root_branch
    |
    | root_optional_body
    | root_repeated];
    cbn in Hnormalize; try discriminate Hnormalize.
  destruct fields as [| first fields].
  - discriminate Hnormalize.
  - destruct fields as [| second fields].
    + discriminate Hnormalize.
    + destruct fields as [| extra rest].
      * destruct first as
          [actual_separator
          | first_class first_lexeme
          | first_name first_body
          | first_trees
          | first_index first_branch
          |
          | first_optional_body
          | first_repeated];
          cbn in Hnormalize; try discriminate Hnormalize.
        destruct (String.eqb actual_separator separator) eqn:Hseparator;
          cbn in Hnormalize; try discriminate Hnormalize.
        apply String.eqb_eq in Hseparator.
        subst actual_separator.
        pose proof
          (phase1_surface_normalize_identifier_round_trip
            second value Hnormalize) as Hidentifier.
        cbn.
        rewrite Hidentifier.
        reflexivity.
      * discriminate Hnormalize.
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
  induction trees as [| tree rest IH]; intros values Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_name_suffix separator tree)
      as [value |] eqn:Htree;
      try discriminate Hnormalize.
    destruct (phase1_surface_normalize_name_suffixes separator rest)
      as [rest_values |] eqn:Hrest;
      try discriminate Hnormalize.
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
  match tree with
  | PTNonterminal actual_name
      (PTSequence [first_tree; PTRepetition suffix_trees]) =>
      if String.eqb actual_name nonterminal then
        match phase1_surface_normalize_identifier first_tree,
              phase1_surface_normalize_name_suffixes separator suffix_trees with
        | Some first_value, Some rest_values =>
            Some
              {| phase1_name_list_first := first_value;
                 phase1_name_list_rest := rest_values |}
        | _, _ => None
        end
      else None
  | _ => None
  end.

Theorem phase1_surface_normalize_name_list_round_trip :
  forall nonterminal separator tree names,
    phase1_surface_normalize_name_list nonterminal separator tree = Some names ->
    phase1_surface_name_list_tree nonterminal separator names = tree.
Proof.
  intros nonterminal separator tree names Hnormalize.
  destruct tree as
    [root_literal
    | root_class root_lexeme
    | actual_name body
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
  destruct fields as [| first_tree fields].
  - discriminate Hnormalize.
  - destruct fields as [| suffix_tree fields].
    + discriminate Hnormalize.
    + destruct fields as [| extra rest].
      * destruct suffix_tree as
          [suffix_literal
          | suffix_class suffix_lexeme
          | suffix_name suffix_body
          | suffix_sequence
          | suffix_index suffix_branch
          |
          | suffix_optional_body
          | suffix_trees];
          cbn in Hnormalize; try discriminate Hnormalize.
        destruct (String.eqb actual_name nonterminal) eqn:Hname;
          cbn in Hnormalize; try discriminate Hnormalize.
        destruct (phase1_surface_normalize_identifier first_tree)
          as [first_value |] eqn:Hfirst;
          try discriminate Hnormalize.
        destruct (phase1_surface_normalize_name_suffixes separator suffix_trees)
          as [rest_values |] eqn:Hsuffixes;
          try discriminate Hnormalize.
        inversion Hnormalize; subst.
        apply String.eqb_eq in Hname.
        subst actual_name.
        cbn.
        rewrite
          (phase1_surface_normalize_identifier_round_trip
            first_tree first_value Hfirst).
        rewrite
          (phase1_surface_normalize_name_suffixes_round_trip
            separator suffix_trees rest_values Hsuffixes).
        reflexivity.
      * discriminate Hnormalize.
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
  match tree with
  | PTNonterminal actual_name
      (PTSequence
        [ PTLiteral keyword;
          qualified_name_tree;
          PTLiteral terminator
        ]) =>
      if String.eqb actual_name "module_decl" then
        if String.eqb keyword "module" then
          if String.eqb terminator ";" then
            phase1_surface_normalize_qualified_name qualified_name_tree
          else None
        else None
      else None
  | _ => None
  end.

Theorem phase1_surface_normalize_module_decl_round_trip :
  forall tree name,
    phase1_surface_normalize_module_decl tree = Some name ->
    phase1_surface_module_decl_tree name = tree.
Proof.
  intros tree name Hnormalize.
  destruct tree as
    [root_literal
    | root_class root_lexeme
    | actual_name body
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
  destruct fields as [| keyword_tree fields].
  - discriminate Hnormalize.
  - destruct fields as [| qualified_name_tree fields].
    + discriminate Hnormalize.
    + destruct fields as [| terminator_tree fields].
      * discriminate Hnormalize.
      * destruct fields as [| extra rest].
        -- destruct keyword_tree as
             [keyword
             | keyword_class keyword_lexeme
             | keyword_name keyword_body
             | keyword_trees
             | keyword_index keyword_branch
             |
             | keyword_optional_body
             | keyword_repeated];
             cbn in Hnormalize; try discriminate Hnormalize.
           destruct terminator_tree as
             [terminator
             | terminator_class terminator_lexeme
             | terminator_name terminator_body
             | terminator_trees
             | terminator_index terminator_branch
             |
             | terminator_optional_body
             | terminator_repeated];
             cbn in Hnormalize; try discriminate Hnormalize.
           destruct (String.eqb actual_name "module_decl") eqn:Hnode;
             cbn in Hnormalize; try discriminate Hnormalize.
           destruct (String.eqb keyword "module") eqn:Hkeyword;
             cbn in Hnormalize; try discriminate Hnormalize.
           destruct (String.eqb terminator ";") eqn:Hterminator;
             cbn in Hnormalize; try discriminate Hnormalize.
           apply String.eqb_eq in Hnode.
           apply String.eqb_eq in Hkeyword.
           apply String.eqb_eq in Hterminator.
           subst actual_name.
           subst keyword.
           subst terminator.
           unfold phase1_surface_qualified_name_tree,
             phase1_surface_normalize_qualified_name.
           rewrite
             (phase1_surface_normalize_name_list_round_trip
               "qualified_name" "." qualified_name_tree name Hnormalize).
           reflexivity.
        -- discriminate Hnormalize.
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
  match tree with
  | PTOptionalNone => Some None
  | PTOptionalSome
      (PTSequence
        [ PTLiteral open_brace;
          identifiers_tree;
          PTLiteral close_brace
        ]) =>
      if String.eqb open_brace "{" then
        if String.eqb close_brace "}" then
          match phase1_surface_normalize_identifier_list identifiers_tree with
          | Some identifiers => Some (Some identifiers)
          | None => None
          end
        else None
      else None
  | _ => None
  end.

Theorem phase1_surface_normalize_import_selection_round_trip :
  forall tree selection,
    phase1_surface_normalize_import_selection tree = Some selection ->
    phase1_surface_import_selection_tree selection = tree.
Proof.
  intros tree selection Hnormalize.
  destruct tree as
    [root_literal
    | root_class root_lexeme
    | root_name root_body
    | root_trees
    | root_index root_branch
    |
    | body
    | root_repeated];
    cbn in Hnormalize; try discriminate Hnormalize.
  - inversion Hnormalize; subst.
    reflexivity.
  - destruct body as
      [body_literal
      | body_class body_lexeme
      | body_name body_body
      | fields
      | body_index body_branch
      |
      | body_optional_body
      | body_repeated];
      cbn in Hnormalize; try discriminate Hnormalize.
    destruct fields as [| open_tree fields].
    + discriminate Hnormalize.
    + destruct fields as [| identifiers_tree fields].
      * discriminate Hnormalize.
      * destruct fields as [| close_tree fields].
        -- discriminate Hnormalize.
        -- destruct fields as [| extra rest].
           ++ destruct open_tree as
                [open_brace
                | open_class open_lexeme
                | open_name open_body
                | open_trees
                | open_index open_branch
                |
                | open_optional_body
                | open_repeated];
                cbn in Hnormalize; try discriminate Hnormalize.
              destruct close_tree as
                [close_brace
                | close_class close_lexeme
                | close_name close_body
                | close_trees
                | close_index close_branch
                |
                | close_optional_body
                | close_repeated];
                cbn in Hnormalize; try discriminate Hnormalize.
              destruct (String.eqb open_brace "{") eqn:Hopen;
                cbn in Hnormalize; try discriminate Hnormalize.
              destruct (String.eqb close_brace "}") eqn:Hclose;
                cbn in Hnormalize; try discriminate Hnormalize.
              destruct (phase1_surface_normalize_identifier_list identifiers_tree)
                as [identifiers |] eqn:Hidentifiers;
                try discriminate Hnormalize.
              inversion Hnormalize; subst.
              apply String.eqb_eq in Hopen.
              apply String.eqb_eq in Hclose.
              subst open_brace.
              subst close_brace.
              unfold phase1_surface_identifier_list_tree,
                phase1_surface_normalize_identifier_list in *.
              rewrite
                (phase1_surface_normalize_name_list_round_trip
                  "identifier_list" "," identifiers_tree identifiers Hidentifiers).
              reflexivity.
           ++ discriminate Hnormalize.
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
  match tree with
  | PTNonterminal actual_name
      (PTSequence
        [ PTLiteral keyword;
          qualified_name_tree;
          selection_tree;
          PTLiteral terminator
        ]) =>
      if String.eqb actual_name "import_decl" then
        if String.eqb keyword "import" then
          if String.eqb terminator ";" then
            match phase1_surface_normalize_qualified_name qualified_name_tree,
                  phase1_surface_normalize_import_selection selection_tree with
            | Some name, Some selection =>
                Some
                  {| phase1_import_header_name := name;
                     phase1_import_header_selection := selection |}
            | _, _ => None
            end
          else None
        else None
      else None
  | _ => None
  end.

Theorem phase1_surface_normalize_import_decl_round_trip :
  forall tree import_header,
    phase1_surface_normalize_import_decl tree = Some import_header ->
    phase1_surface_import_decl_tree import_header = tree.
Proof.
  intros tree import_header Hnormalize.
  destruct tree as
    [root_literal
    | root_class root_lexeme
    | actual_name body
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
  destruct fields as [| keyword_tree fields].
  - discriminate Hnormalize.
  - destruct fields as [| qualified_name_tree fields].
    + discriminate Hnormalize.
    + destruct fields as [| selection_tree fields].
      * discriminate Hnormalize.
      * destruct fields as [| terminator_tree fields].
        -- discriminate Hnormalize.
        -- destruct fields as [| extra rest].
           ++ destruct keyword_tree as
                [keyword
                | keyword_class keyword_lexeme
                | keyword_name keyword_body
                | keyword_trees
                | keyword_index keyword_branch
                |
                | keyword_optional_body
                | keyword_repeated];
                cbn in Hnormalize; try discriminate Hnormalize.
              destruct terminator_tree as
                [terminator
                | terminator_class terminator_lexeme
                | terminator_name terminator_body
                | terminator_trees
                | terminator_index terminator_branch
                |
                | terminator_optional_body
                | terminator_repeated];
                cbn in Hnormalize; try discriminate Hnormalize.
              destruct (String.eqb actual_name "import_decl") eqn:Hnode;
                cbn in Hnormalize; try discriminate Hnormalize.
              destruct (String.eqb keyword "import") eqn:Hkeyword;
                cbn in Hnormalize; try discriminate Hnormalize.
              destruct (String.eqb terminator ";") eqn:Hterminator;
                cbn in Hnormalize; try discriminate Hnormalize.
              destruct (phase1_surface_normalize_qualified_name qualified_name_tree)
                as [name |] eqn:Hname;
                try discriminate Hnormalize.
              destruct (phase1_surface_normalize_import_selection selection_tree)
                as [selection |] eqn:Hselection;
                try discriminate Hnormalize.
              inversion Hnormalize; subst.
              apply String.eqb_eq in Hnode.
              apply String.eqb_eq in Hkeyword.
              apply String.eqb_eq in Hterminator.
              subst actual_name.
              subst keyword.
              subst terminator.
              cbn.
              unfold phase1_surface_qualified_name_tree,
                phase1_surface_normalize_qualified_name in *.
              rewrite
                (phase1_surface_normalize_name_list_round_trip
                  "qualified_name" "." qualified_name_tree name Hname).
              rewrite
                (phase1_surface_normalize_import_selection_round_trip
                  selection_tree selection Hselection).
              reflexivity.
           ++ discriminate Hnormalize.
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
  induction trees as [| tree rest IH]; intros import_headers Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_import_decl tree)
      as [import_header |] eqn:Htree;
      try discriminate Hnormalize.
    destruct (phase1_surface_normalize_import_decls rest)
      as [rest_headers |] eqn:Hrest;
      try discriminate Hnormalize.
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
      as [name |] eqn:Htree;
      try discriminate Hnormalize.
    inversion Hnormalize; subst.
    cbn.
    rewrite
      (phase1_surface_normalize_module_decl_round_trip
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
    as [module_name |] eqn:Hmodule;
    try discriminate Hnormalize.
  destruct (phase1_surface_normalize_import_decls import_trees)
    as [import_headers |] eqn:Himports;
    try discriminate Hnormalize.
  inversion Hnormalize; subst.
  cbn.
  rewrite
    (phase1_surface_normalize_import_decls_round_trip
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
    as [spine |] eqn:Hspine;
    try discriminate Hnormalize.
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
    as [[rest result] |] eqn:Hparse;
    try discriminate Hnormalize.
  destruct rest as [| token rest]; try discriminate Hnormalize.
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
