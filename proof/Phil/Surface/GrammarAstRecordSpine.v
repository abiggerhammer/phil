From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine.

Import ListNotations.
Open Scope string_scope.

(*
  First declaration-family-specific correspondence layer for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  The top-level carrier identifies declaration family and deliberately retains
  the selected declaration subtree.  This layer begins descending the first
  family, record_decl.  It normalizes the record name and exact outer record
  syntax while retaining the shared generic/mode/requirement/field payload
  slots as certified ParseTree values for their own successor refinements.
*)

Record Phase1SurfaceExact8 (A : Type) : Type := {
  phase1_exact8_1 : A;
  phase1_exact8_2 : A;
  phase1_exact8_3 : A;
  phase1_exact8_4 : A;
  phase1_exact8_5 : A;
  phase1_exact8_6 : A;
  phase1_exact8_7 : A;
  phase1_exact8_8 : A
}.

Definition phase1_surface_exact8 {A : Type}
  (items : list A) : option (Phase1SurfaceExact8 A) :=
  match items with
  | [a; b; c; d; e; f; g; h] =>
      Some
        {| phase1_exact8_1 := a;
           phase1_exact8_2 := b;
           phase1_exact8_3 := c;
           phase1_exact8_4 := d;
           phase1_exact8_5 := e;
           phase1_exact8_6 := f;
           phase1_exact8_7 := g;
           phase1_exact8_8 := h |}
  | _ => None
  end.

Lemma phase1_surface_exact8_round_trip {A : Type} :
  forall (items : list A) (fields : Phase1SurfaceExact8 A),
    phase1_surface_exact8 items = Some fields ->
    items =
      [ phase1_exact8_1 fields;
        phase1_exact8_2 fields;
        phase1_exact8_3 fields;
        phase1_exact8_4 fields;
        phase1_exact8_5 fields;
        phase1_exact8_6 fields;
        phase1_exact8_7 fields;
        phase1_exact8_8 fields
      ].
Proof.
  intros items fields Hitems.
  destruct items as [|a rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|b rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|c rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|d rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|e rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|f rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|g rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|h rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|extra rest]; cbn in Hitems; try discriminate Hitems.
  inversion Hitems; subst.
  reflexivity.
Qed.

Record Phase1SurfaceRecordSpine : Type := {
  phase1_record_spine_name : string;
  phase1_record_spine_generic_params_tree : ParseTree;
  phase1_record_spine_mode_tree : ParseTree;
  phase1_record_spine_requirements_tree : ParseTree;
  phase1_record_spine_fields_tree : ParseTree
}.

Definition phase1_surface_record_spine_tree
  (record : Phase1SurfaceRecordSpine) : ParseTree :=
  PTNonterminal "record_decl"
    (PTSequence
      [ PTLiteral "record";
        phase1_surface_identifier_tree (phase1_record_spine_name record);
        phase1_record_spine_generic_params_tree record;
        phase1_record_spine_mode_tree record;
        phase1_record_spine_requirements_tree record;
        PTLiteral "{";
        phase1_record_spine_fields_tree record;
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_record_spine
  (tree : ParseTree) : option Phase1SurfaceRecordSpine :=
  match phase1_surface_expect_nonterminal "record_decl" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact8 items with
          | Some fields =>
              let keyword_tree := phase1_exact8_1 fields in
              let name_tree := phase1_exact8_2 fields in
              let generic_tree := phase1_exact8_3 fields in
              let mode_tree := phase1_exact8_4 fields in
              let requirements_tree := phase1_exact8_5 fields in
              let open_tree := phase1_exact8_6 fields in
              let field_tree := phase1_exact8_7 fields in
              let close_tree := phase1_exact8_8 fields in
              match phase1_surface_expect_literal "record" keyword_tree,
                    phase1_surface_expect_literal "{" open_tree,
                    phase1_surface_expect_literal "}" close_tree with
              | Some tt, Some tt, Some tt =>
                  match phase1_surface_normalize_identifier name_tree with
                  | Some name =>
                      Some
                        {| phase1_record_spine_name := name;
                           phase1_record_spine_generic_params_tree := generic_tree;
                           phase1_record_spine_mode_tree := mode_tree;
                           phase1_record_spine_requirements_tree := requirements_tree;
                           phase1_record_spine_fields_tree := field_tree |}
                  | None => None
                  end
              | _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_record_spine_round_trip :
  forall tree record,
    phase1_surface_normalize_record_spine tree = Some record ->
    phase1_surface_record_spine_tree record = tree.
Proof.
  intros tree record Hnormalize.
  unfold phase1_surface_normalize_record_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "record_decl" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact8 items)
    as [fields |] eqn:Hitems; try discriminate Hnormalize.
  destruct fields as
    [keyword_tree name_tree generic_tree mode_tree requirements_tree
     open_tree field_tree close_tree].
  cbn in Hnormalize.
  destruct (phase1_surface_expect_literal "record" keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "{" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "}" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier name_tree)
    as [name |] eqn:Hname; try discriminate Hnormalize.
  inversion Hnormalize; subst record.
  unfold phase1_surface_record_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "record_decl" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact8_round_trip
    items
    {| phase1_exact8_1 := keyword_tree;
       phase1_exact8_2 := name_tree;
       phase1_exact8_3 := generic_tree;
       phase1_exact8_4 := mode_tree;
       phase1_exact8_5 := requirements_tree;
       phase1_exact8_6 := open_tree;
       phase1_exact8_7 := field_tree;
       phase1_exact8_8 := close_tree |}
    Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "record" keyword_tree Hkeyword).
  rewrite (phase1_surface_normalize_identifier_round_trip
    name_tree name Hname).
  rewrite (phase1_surface_expect_literal_round_trip "{" open_tree Hopen).
  rewrite (phase1_surface_expect_literal_round_trip "}" close_tree Hclose).
  reflexivity.
Qed.

Definition phase1_surface_normalize_record_declaration_spine
  (declaration : Phase1SurfaceDeclarationSpine)
  : option Phase1SurfaceRecordSpine :=
  match phase1_declaration_spine_tag declaration with
  | Phase1RecordDeclaration =>
      phase1_surface_normalize_record_spine
        (phase1_declaration_spine_selected_tree declaration)
  | _ => None
  end.

Theorem phase1_surface_normalize_record_declaration_spine_round_trip :
  forall declaration record,
    phase1_surface_normalize_record_declaration_spine declaration = Some record ->
    phase1_surface_record_spine_tree record =
      phase1_declaration_spine_selected_tree declaration.
Proof.
  intros [tag selected] record Hnormalize.
  destruct tag; cbn in Hnormalize; try discriminate Hnormalize.
  eapply phase1_surface_normalize_record_spine_round_trip.
  exact Hnormalize.
Qed.

Definition phase1_surface_normalize_record_declaration_tree
  (tree : ParseTree) : option Phase1SurfaceRecordSpine :=
  match phase1_surface_normalize_declaration_spine tree with
  | Some declaration =>
      phase1_surface_normalize_record_declaration_spine declaration
  | None => None
  end.

Theorem phase1_surface_normalize_record_declaration_tree_round_trip :
  forall tree record,
    phase1_surface_normalize_record_declaration_tree tree = Some record ->
    PTNonterminal "declaration"
      (PTAlternative 0 (phase1_surface_record_spine_tree record)) = tree.
Proof.
  intros tree record Hnormalize.
  unfold phase1_surface_normalize_record_declaration_tree in Hnormalize.
  destruct (phase1_surface_normalize_declaration_spine tree)
    as [declaration |] eqn:Hdeclaration; try discriminate Hnormalize.
  destruct declaration as [tag selected].
  destruct tag; cbn in Hnormalize; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_record_spine_round_trip
      selected record Hnormalize) as Hrecord.
  pose proof
    (phase1_surface_normalize_declaration_spine_round_trip
      tree
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := selected |}
      Hdeclaration) as Hdecl.
  cbn in Hdecl.
  rewrite <- Hrecord in Hdecl.
  exact Hdecl.
Qed.
