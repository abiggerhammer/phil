From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstShallowCompoundTypePayloadSpine
  GrammarAstVariantPayloadSpine
  GrammarAstGenericRequirementsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Final nonreference type-shell refinement below the shallow compound layer.

  refinement_type and tuple_type are normalized structurally here while their
  recursive type_expression / proposition children remain exact certified
  ParseTree values for dedicated recursive correspondence slices.
*)

Definition phase1_surface_exact6 {A : Type}
  (items : list A) : option (A * A * A * A * A * A) :=
  match items with
  | [a; b; c; d; e; f] => Some (a, b, c, d, e, f)
  | _ => None
  end.

Lemma phase1_surface_exact6_round_trip {A : Type} :
  forall (items : list A) (a b c d e f : A),
    phase1_surface_exact6 items = Some (a, b, c, d, e, f) ->
    items = [a; b; c; d; e; f].
Proof.
  intros items a b c d e f Hitems.
  destruct items as [|x1 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|x2 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|x3 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|x4 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|x5 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|x6 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|extra items]; cbn in Hitems; try discriminate Hitems.
  inversion Hitems; subst.
  reflexivity.
Qed.

Definition phase1_surface_exact7 {A : Type}
  (items : list A) : option (A * A * A * A * A * A * A) :=
  match items with
  | [a; b; c; d; e; f; g] => Some (a, b, c, d, e, f, g)
  | _ => None
  end.

Lemma phase1_surface_exact7_round_trip {A : Type} :
  forall (items : list A) (a b c d e f g : A),
    phase1_surface_exact7 items = Some (a, b, c, d, e, f, g) ->
    items = [a; b; c; d; e; f; g].
Proof.
  intros items a b c d e f g Hitems.
  destruct items as [|x1 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|x2 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|x3 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|x4 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|x5 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|x6 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|x7 items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|extra items]; cbn in Hitems; try discriminate Hitems.
  inversion Hitems; subst.
  reflexivity.
Qed.

Record Phase1SurfaceRefinementTypeSpine : Type := {
  phase1_refinement_type_spine_binder : string;
  phase1_refinement_type_spine_base_type_tree : ParseTree;
  phase1_refinement_type_spine_proposition_tree : ParseTree
}.

Definition phase1_surface_refinement_type_spine_tree
  (refinement : Phase1SurfaceRefinementTypeSpine) : ParseTree :=
  PTNonterminal "refinement_type"
    (PTSequence
      [ PTLiteral "{";
        phase1_surface_identifier_tree
          (phase1_refinement_type_spine_binder refinement);
        PTLiteral ":";
        phase1_refinement_type_spine_base_type_tree refinement;
        PTLiteral "|";
        phase1_refinement_type_spine_proposition_tree refinement;
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_refinement_type_spine
  (tree : ParseTree) : option Phase1SurfaceRefinementTypeSpine :=
  match phase1_surface_expect_nonterminal "refinement_type" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact7 items with
          | Some
              (open_tree, binder_tree, colon_tree, base_type_tree,
               bar_tree, proposition_tree, close_tree) =>
              match
                phase1_surface_expect_literal "{" open_tree,
                phase1_surface_normalize_identifier binder_tree,
                phase1_surface_expect_literal ":" colon_tree,
                phase1_surface_validate_named_node
                  "type_expression" base_type_tree,
                phase1_surface_expect_literal "|" bar_tree,
                phase1_surface_validate_named_node
                  "proposition" proposition_tree,
                phase1_surface_expect_literal "}" close_tree
              with
              | Some tt, Some binder, Some tt, Some tt,
                Some tt, Some tt, Some tt =>
                  Some
                    {| phase1_refinement_type_spine_binder := binder;
                       phase1_refinement_type_spine_base_type_tree :=
                         base_type_tree;
                       phase1_refinement_type_spine_proposition_tree :=
                         proposition_tree |}
              | _, _, _, _, _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_refinement_type_spine_round_trip :
  forall tree refinement,
    phase1_surface_normalize_refinement_type_spine tree = Some refinement ->
    phase1_surface_refinement_type_spine_tree refinement = tree.
Proof.
  intros tree refinement Hnormalize.
  unfold phase1_surface_normalize_refinement_type_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "refinement_type" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact7 items)
    as [[[[[[[open_tree binder_tree] colon_tree] base_type_tree]
             bar_tree] proposition_tree] close_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "{" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier binder_tree)
    as [binder |] eqn:Hbinder; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ":" colon_tree)
    as [[] |] eqn:Hcolon; try discriminate Hnormalize.
  destruct
    (phase1_surface_validate_named_node "type_expression" base_type_tree)
    as [[] |] eqn:Hbase; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "|" bar_tree)
    as [[] |] eqn:Hbar; try discriminate Hnormalize.
  destruct
    (phase1_surface_validate_named_node "proposition" proposition_tree)
    as [[] |] eqn:Hproposition; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "}" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  inversion Hnormalize; subst refinement.
  unfold phase1_surface_refinement_type_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "refinement_type" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact7_round_trip
    items open_tree binder_tree colon_tree base_type_tree bar_tree
    proposition_tree close_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "{" open_tree Hopen).
  rewrite (phase1_surface_normalize_identifier_round_trip
    binder_tree binder Hbinder).
  rewrite (phase1_surface_expect_literal_round_trip ":" colon_tree Hcolon).
  rewrite (phase1_surface_expect_literal_round_trip "|" bar_tree Hbar).
  rewrite (phase1_surface_expect_literal_round_trip "}" close_tree Hclose).
  reflexivity.
Qed.

Record Phase1SurfaceTupleTypeSpine : Type := {
  phase1_tuple_type_spine_first : ParseTree;
  phase1_tuple_type_spine_second : ParseTree;
  phase1_tuple_type_spine_rest : list ParseTree
}.

Definition phase1_surface_tuple_type_spine_tree
  (tuple_type : Phase1SurfaceTupleTypeSpine) : ParseTree :=
  PTNonterminal "tuple_type"
    (PTSequence
      [ PTLiteral "(";
        phase1_tuple_type_spine_first tuple_type;
        PTLiteral ",";
        phase1_tuple_type_spine_second tuple_type;
        PTRepetition
          (map phase1_surface_tuple_type_suffix_tree
            (phase1_tuple_type_spine_rest tuple_type));
        PTLiteral ")"
      ]).

Definition phase1_surface_normalize_tuple_type_spine
  (tree : ParseTree) : option Phase1SurfaceTupleTypeSpine :=
  match phase1_surface_expect_nonterminal "tuple_type" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact6 items with
          | Some
              (open_tree, first_tree, comma_tree, second_tree,
               rest_tree, close_tree) =>
              match
                phase1_surface_expect_literal "(" open_tree,
                phase1_surface_validate_named_node
                  "type_expression" first_tree,
                phase1_surface_expect_literal "," comma_tree,
                phase1_surface_validate_named_node
                  "type_expression" second_tree,
                phase1_surface_expect_repetition rest_tree,
                phase1_surface_expect_literal ")" close_tree
              with
              | Some tt, Some tt, Some tt, Some tt,
                Some rest_trees, Some tt =>
                  match
                    phase1_surface_normalize_tuple_type_suffixes rest_trees
                  with
                  | Some rest =>
                      Some
                        {| phase1_tuple_type_spine_first := first_tree;
                           phase1_tuple_type_spine_second := second_tree;
                           phase1_tuple_type_spine_rest := rest |}
                  | None => None
                  end
              | _, _, _, _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_tuple_type_spine_round_trip :
  forall tree tuple_type,
    phase1_surface_normalize_tuple_type_spine tree = Some tuple_type ->
    phase1_surface_tuple_type_spine_tree tuple_type = tree.
Proof.
  intros tree tuple_type Hnormalize.
  unfold phase1_surface_normalize_tuple_type_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "tuple_type" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact6 items)
    as [[[[[[open_tree first_tree] comma_tree] second_tree]
           rest_tree] close_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "(" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct
    (phase1_surface_validate_named_node "type_expression" first_tree)
    as [[] |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma_tree)
    as [[] |] eqn:Hcomma; try discriminate Hnormalize.
  destruct
    (phase1_surface_validate_named_node "type_expression" second_tree)
    as [[] |] eqn:Hsecond; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition rest_tree)
    as [rest_trees |] eqn:Hrest_trees; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ")" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_tuple_type_suffixes rest_trees)
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst tuple_type.
  unfold phase1_surface_tuple_type_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "tuple_type" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact6_round_trip
    items open_tree first_tree comma_tree second_tree rest_tree close_tree
    Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "(" open_tree Hopen).
  rewrite (phase1_surface_expect_literal_round_trip "," comma_tree Hcomma).
  rewrite (phase1_surface_expect_repetition_round_trip
    rest_tree rest_trees Hrest_trees).
  rewrite (phase1_surface_normalize_tuple_type_suffixes_round_trip
    rest_trees rest Hrest).
  rewrite (phase1_surface_expect_literal_round_trip ")" close_tree Hclose).
  reflexivity.
Qed.

Inductive Phase1SurfaceRefinementTupleNonreferenceTypeSpine : Type :=
| Phase1RefinementTuplePriorNonreferenceType
    (value : Phase1SurfaceShallowCompoundNonreferenceTypeSpine)
| Phase1RefinementTupleRefinementType
    (value : Phase1SurfaceRefinementTypeSpine)
| Phase1RefinementTupleTupleType
    (value : Phase1SurfaceTupleTypeSpine)
| Phase1RefinementTupleOpaqueNonreferenceType
    (tag : Phase1SurfaceNonreferenceTypeTag)
    (selected_tree : ParseTree).

Definition phase1_surface_refinement_tuple_nonreference_type_spine_tree
  (type_value : Phase1SurfaceRefinementTupleNonreferenceTypeSpine) : ParseTree :=
  match type_value with
  | Phase1RefinementTuplePriorNonreferenceType prior =>
      phase1_surface_shallow_compound_nonreference_type_spine_tree prior
  | Phase1RefinementTupleRefinementType refinement =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 11
          (phase1_surface_refinement_type_spine_tree refinement))
  | Phase1RefinementTupleTupleType tuple_type =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 12
          (phase1_surface_tuple_type_spine_tree tuple_type))
  | Phase1RefinementTupleOpaqueNonreferenceType tag selected_tree =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative
          (phase1_surface_nonreference_type_tag_index tag)
          selected_tree)
  end.

Definition phase1_surface_normalize_refinement_tuple_nonreference_type_spine
  (type_value : Phase1SurfaceShallowCompoundNonreferenceTypeSpine)
  : option Phase1SurfaceRefinementTupleNonreferenceTypeSpine :=
  match type_value with
  | Phase1ShallowOpaqueNonreferenceType tag selected =>
      match tag with
      | Phase1RefinementType =>
          match phase1_surface_normalize_refinement_type_spine selected with
          | Some refinement =>
              Some (Phase1RefinementTupleRefinementType refinement)
          | None => None
          end
      | Phase1TupleType =>
          match phase1_surface_normalize_tuple_type_spine selected with
          | Some tuple_type =>
              Some (Phase1RefinementTupleTupleType tuple_type)
          | None => None
          end
      | _ =>
          Some (Phase1RefinementTupleOpaqueNonreferenceType tag selected)
      end
  | _ => Some (Phase1RefinementTuplePriorNonreferenceType type_value)
  end.

Theorem
  phase1_surface_normalize_refinement_tuple_nonreference_type_spine_round_trip :
  forall type_value refined,
    phase1_surface_normalize_refinement_tuple_nonreference_type_spine
      type_value = Some refined ->
    phase1_surface_refinement_tuple_nonreference_type_spine_tree refined =
      phase1_surface_shallow_compound_nonreference_type_spine_tree type_value.
Proof.
  intros type_value refined Hnormalize.
  destruct type_value as
    [prior |index_expression |reference_tree |proposition_tree |payload
    |tag selected];
    cbn in Hnormalize.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct tag; cbn in Hnormalize.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + destruct (phase1_surface_normalize_refinement_type_spine selected)
        as [refinement |] eqn:Hselected; try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (phase1_surface_normalize_refinement_type_spine_round_trip
        selected refinement Hselected).
      reflexivity.
    + destruct (phase1_surface_normalize_tuple_type_spine selected)
        as [tuple_type |] eqn:Hselected; try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (phase1_surface_normalize_tuple_type_spine_round_trip
        selected tuple_type Hselected).
      reflexivity.
Qed.

Inductive Phase1SurfaceRefinementTupleTypeSpine : Type :=
| Phase1RefinementTupleNonreferenceTypeSpine
    (type_value : Phase1SurfaceRefinementTupleNonreferenceTypeSpine)
| Phase1RefinementTupleNamedTypeSpine
    (named_tree : ParseTree).

Definition phase1_surface_refinement_tuple_type_spine_tree
  (type_value : Phase1SurfaceRefinementTupleTypeSpine) : ParseTree :=
  match type_value with
  | Phase1RefinementTupleNonreferenceTypeSpine nonreference =>
      PTNonterminal "type_expression"
        (PTAlternative 0
          (phase1_surface_refinement_tuple_nonreference_type_spine_tree
            nonreference))
  | Phase1RefinementTupleNamedTypeSpine named_tree =>
      PTNonterminal "type_expression"
        (PTAlternative 1 named_tree)
  end.

Definition phase1_surface_normalize_refinement_tuple_type_spine
  (type_value : Phase1SurfaceShallowCompoundTypeSpine)
  : option Phase1SurfaceRefinementTupleTypeSpine :=
  match type_value with
  | Phase1ShallowCompoundNonreferenceTypeSpine nonreference =>
      match
        phase1_surface_normalize_refinement_tuple_nonreference_type_spine
          nonreference
      with
      | Some refined =>
          Some (Phase1RefinementTupleNonreferenceTypeSpine refined)
      | None => None
      end
  | Phase1ShallowCompoundNamedTypeSpine named_tree =>
      Some (Phase1RefinementTupleNamedTypeSpine named_tree)
  end.

Theorem phase1_surface_normalize_refinement_tuple_type_spine_round_trip :
  forall type_value refined,
    phase1_surface_normalize_refinement_tuple_type_spine type_value =
      Some refined ->
    phase1_surface_refinement_tuple_type_spine_tree refined =
      phase1_surface_shallow_compound_type_spine_tree type_value.
Proof.
  intros type_value refined Hnormalize.
  destruct type_value as [nonreference | named_tree].
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_refinement_tuple_nonreference_type_spine
        nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_refinement_tuple_nonreference_type_spine_round_trip
        nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_refinement_tuple_type_tree
  (tree : ParseTree) : option Phase1SurfaceRefinementTupleTypeSpine :=
  match phase1_surface_normalize_shallow_compound_type_tree tree with
  | Some type_value =>
      phase1_surface_normalize_refinement_tuple_type_spine type_value
  | None => None
  end.

Theorem phase1_surface_normalize_refinement_tuple_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_refinement_tuple_type_tree tree = Some refined ->
    phase1_surface_refinement_tuple_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_refinement_tuple_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_shallow_compound_type_tree tree)
    as [type_value |] eqn:Htype; try discriminate Hnormalize.
  transitivity (phase1_surface_shallow_compound_type_spine_tree type_value).
  - eapply phase1_surface_normalize_refinement_tuple_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_shallow_compound_type_tree_round_trip.
    exact Htype.
Qed.
