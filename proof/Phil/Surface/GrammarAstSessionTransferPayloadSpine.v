From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionSpine
  GrammarAstRecordSpine
  GrammarAstGenericRequirementsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the shared send/receive session payload shell.

  The immediate syntax is normalized here, while term_param, static_reference,
  proposition, and recursive session_expression children remain exact named
  ParseTree values for successor recursive correspondence slices.
*)

Definition phase1_surface_optional_named_annotation_tree
  (keyword : string) (value : option ParseTree) : ParseTree :=
  match value with
  | None => PTOptionalNone
  | Some value_tree =>
      PTOptionalSome
        (PTSequence
          [ PTLiteral keyword;
            value_tree
          ])
  end.

Definition phase1_surface_normalize_optional_named_annotation
  (keyword name : string) (tree : ParseTree) : option (option ParseTree) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some annotation_tree) =>
      match phase1_surface_expect_sequence annotation_tree with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (keyword_tree, value_tree) =>
              match phase1_surface_expect_literal keyword keyword_tree,
                    phase1_surface_validate_named_node name value_tree with
              | Some tt, Some tt => Some (Some value_tree)
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_named_annotation_round_trip :
  forall keyword name tree value,
    phase1_surface_normalize_optional_named_annotation keyword name tree =
      Some value ->
    phase1_surface_optional_named_annotation_tree keyword value = tree.
Proof.
  intros keyword name tree value Hnormalize.
  unfold phase1_surface_normalize_optional_named_annotation in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[annotation_tree |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_expect_sequence annotation_tree)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact2 items)
      as [[keyword_tree value_tree] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal keyword keyword_tree)
      as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
    destruct (phase1_surface_validate_named_node name value_tree)
      as [[] |] eqn:Hvalue; try discriminate Hnormalize.
    inversion Hnormalize; subst value.
    unfold phase1_surface_optional_named_annotation_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some annotation_tree) Hoptional).
    rewrite (phase1_surface_expect_sequence_round_trip
      annotation_tree items Hsequence).
    rewrite (phase1_surface_exact2_round_trip
      items keyword_tree value_tree Hitems).
    rewrite (phase1_surface_expect_literal_round_trip
      keyword keyword_tree Hkeyword).
    reflexivity.
  - inversion Hnormalize; subst value.
    unfold phase1_surface_optional_named_annotation_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Inductive Phase1SurfaceSessionTransferDirection : Type :=
| Phase1SessionSend
| Phase1SessionReceive.

Definition phase1_surface_session_transfer_keyword
  (direction : Phase1SurfaceSessionTransferDirection) : string :=
  match direction with
  | Phase1SessionSend => "send"
  | Phase1SessionReceive => "receive"
  end.

Definition phase1_surface_session_transfer_index
  (direction : Phase1SurfaceSessionTransferDirection) : nat :=
  match direction with
  | Phase1SessionSend => 0
  | Phase1SessionReceive => 1
  end.

Record Phase1SurfaceSessionTransferSpine : Type := {
  phase1_session_transfer_direction : Phase1SurfaceSessionTransferDirection;
  phase1_session_transfer_parameter_tree : ParseTree;
  phase1_session_transfer_boundary_tree : option ParseTree;
  phase1_session_transfer_guard_tree : option ParseTree;
  phase1_session_transfer_continuation_tree : ParseTree
}.

Definition phase1_surface_session_transfer_spine_tree
  (transfer : Phase1SurfaceSessionTransferSpine) : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_transfer_keyword
          (phase1_session_transfer_direction transfer));
      PTLiteral "(";
      phase1_session_transfer_parameter_tree transfer;
      PTLiteral ")";
      phase1_surface_optional_named_annotation_tree
        "using" (phase1_session_transfer_boundary_tree transfer);
      phase1_surface_optional_named_annotation_tree
        "when" (phase1_session_transfer_guard_tree transfer);
      PTLiteral "then";
      phase1_session_transfer_continuation_tree transfer
    ].

Definition phase1_surface_normalize_session_transfer_spine
  (direction : Phase1SurfaceSessionTransferDirection)
  (tree : ParseTree) : option Phase1SurfaceSessionTransferSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact8 items with
      | Some fields =>
          let keyword_tree := phase1_exact8_1 fields in
          let open_tree := phase1_exact8_2 fields in
          let parameter_tree := phase1_exact8_3 fields in
          let close_tree := phase1_exact8_4 fields in
          let boundary_tree := phase1_exact8_5 fields in
          let guard_tree := phase1_exact8_6 fields in
          let then_tree := phase1_exact8_7 fields in
          let continuation_tree := phase1_exact8_8 fields in
          match
            phase1_surface_expect_literal
              (phase1_surface_session_transfer_keyword direction)
              keyword_tree,
            phase1_surface_expect_literal "(" open_tree,
            phase1_surface_validate_named_node "term_param" parameter_tree,
            phase1_surface_expect_literal ")" close_tree,
            phase1_surface_normalize_optional_named_annotation
              "using" "static_reference" boundary_tree,
            phase1_surface_normalize_optional_named_annotation
              "when" "proposition" guard_tree,
            phase1_surface_expect_literal "then" then_tree,
            phase1_surface_validate_named_node
              "session_expression" continuation_tree
          with
          | Some tt, Some tt, Some tt, Some tt,
            Some boundary, Some guard, Some tt, Some tt =>
              Some
                {| phase1_session_transfer_direction := direction;
                   phase1_session_transfer_parameter_tree := parameter_tree;
                   phase1_session_transfer_boundary_tree := boundary;
                   phase1_session_transfer_guard_tree := guard;
                   phase1_session_transfer_continuation_tree :=
                     continuation_tree |}
          | _, _, _, _, _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_session_transfer_spine_round_trip :
  forall direction tree transfer,
    phase1_surface_normalize_session_transfer_spine direction tree =
      Some transfer ->
    phase1_surface_session_transfer_spine_tree transfer = tree.
Proof.
  intros direction tree transfer Hnormalize.
  unfold phase1_surface_normalize_session_transfer_spine in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact8 items)
    as [fields |] eqn:Hitems; try discriminate Hnormalize.
  destruct fields as
    [keyword_tree open_tree parameter_tree close_tree boundary_tree
     guard_tree then_tree continuation_tree].
  cbn in Hnormalize.
  destruct
    (phase1_surface_expect_literal
      (phase1_surface_session_transfer_keyword direction) keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "(" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "term_param" parameter_tree)
    as [[] |] eqn:Hparameter; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ")" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_optional_named_annotation
      "using" "static_reference" boundary_tree)
    as [boundary |] eqn:Hboundary; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_optional_named_annotation
      "when" "proposition" guard_tree)
    as [guard |] eqn:Hguard; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "then" then_tree)
    as [[] |] eqn:Hthen; try discriminate Hnormalize.
  destruct
    (phase1_surface_validate_named_node
      "session_expression" continuation_tree)
    as [[] |] eqn:Hcontinuation; try discriminate Hnormalize.
  inversion Hnormalize; subst transfer.
  unfold phase1_surface_session_transfer_spine_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact8_round_trip
    items
    {| phase1_exact8_1 := keyword_tree;
       phase1_exact8_2 := open_tree;
       phase1_exact8_3 := parameter_tree;
       phase1_exact8_4 := close_tree;
       phase1_exact8_5 := boundary_tree;
       phase1_exact8_6 := guard_tree;
       phase1_exact8_7 := then_tree;
       phase1_exact8_8 := continuation_tree |}
    Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    (phase1_surface_session_transfer_keyword direction)
    keyword_tree Hkeyword).
  rewrite (phase1_surface_expect_literal_round_trip "(" open_tree Hopen).
  rewrite (phase1_surface_expect_literal_round_trip ")" close_tree Hclose).
  rewrite
    (phase1_surface_normalize_optional_named_annotation_round_trip
      "using" "static_reference" boundary_tree boundary Hboundary).
  rewrite
    (phase1_surface_normalize_optional_named_annotation_round_trip
      "when" "proposition" guard_tree guard Hguard).
  rewrite (phase1_surface_expect_literal_round_trip "then" then_tree Hthen).
  reflexivity.
Qed.

Inductive Phase1SurfaceTransferRefinedNonreferenceSessionSpine : Type :=
| Phase1RefinedTransferSession
    (transfer : Phase1SurfaceSessionTransferSpine)
| Phase1OpaqueSelectSession (selected_tree : ParseTree)
| Phase1OpaqueOfferSession (selected_tree : ParseTree)
| Phase1OpaqueEndSession (selected_tree : ParseTree)
| Phase1OpaqueRecursiveSession (selected_tree : ParseTree)
| Phase1OpaqueContinueSession (selected_tree : ParseTree).

Definition phase1_surface_transfer_refined_nonreference_session_spine_tree
  (session : Phase1SurfaceTransferRefinedNonreferenceSessionSpine) : ParseTree :=
  match session with
  | Phase1RefinedTransferSession transfer =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative
          (phase1_surface_session_transfer_index
            (phase1_session_transfer_direction transfer))
          (phase1_surface_session_transfer_spine_tree transfer))
  | Phase1OpaqueSelectSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2 selected_tree)
  | Phase1OpaqueOfferSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3 selected_tree)
  | Phase1OpaqueEndSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 selected_tree)
  | Phase1OpaqueRecursiveSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5 selected_tree)
  | Phase1OpaqueContinueSession selected_tree =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6 selected_tree)
  end.

Definition phase1_surface_normalize_transfer_refined_nonreference_session_spine
  (session : Phase1SurfaceNonreferenceSessionSpine)
  : option Phase1SurfaceTransferRefinedNonreferenceSessionSpine :=
  let selected := phase1_nonreference_session_spine_selected_tree session in
  match phase1_nonreference_session_spine_tag session with
  | Phase1SendSession =>
      match
        phase1_surface_normalize_session_transfer_spine
          Phase1SessionSend selected
      with
      | Some transfer => Some (Phase1RefinedTransferSession transfer)
      | None => None
      end
  | Phase1ReceiveSession =>
      match
        phase1_surface_normalize_session_transfer_spine
          Phase1SessionReceive selected
      with
      | Some transfer => Some (Phase1RefinedTransferSession transfer)
      | None => None
      end
  | Phase1SelectSession => Some (Phase1OpaqueSelectSession selected)
  | Phase1OfferSession => Some (Phase1OpaqueOfferSession selected)
  | Phase1EndSession => Some (Phase1OpaqueEndSession selected)
  | Phase1RecursiveSession => Some (Phase1OpaqueRecursiveSession selected)
  | Phase1ContinueSession => Some (Phase1OpaqueContinueSession selected)
  end.

Theorem
  phase1_surface_normalize_transfer_refined_nonreference_session_spine_round_trip :
  forall session refined,
    phase1_surface_normalize_transfer_refined_nonreference_session_spine session =
      Some refined ->
    phase1_surface_transfer_refined_nonreference_session_spine_tree refined =
      phase1_surface_nonreference_session_spine_tree session.
Proof.
  intros [tag selected] refined Hnormalize.
  destruct tag; cbn in Hnormalize.
  - destruct
      (phase1_surface_normalize_session_transfer_spine
        Phase1SessionSend selected)
      as [transfer |] eqn:Htransfer; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_session_transfer_spine_round_trip
        Phase1SessionSend selected transfer Htransfer).
    reflexivity.
  - destruct
      (phase1_surface_normalize_session_transfer_spine
        Phase1SessionReceive selected)
      as [transfer |] eqn:Htransfer; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_session_transfer_spine_round_trip
        Phase1SessionReceive selected transfer Htransfer).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_transfer_refined_nonreference_session_tree
  (tree : ParseTree)
  : option Phase1SurfaceTransferRefinedNonreferenceSessionSpine :=
  match phase1_surface_normalize_nonreference_session_spine tree with
  | Some session =>
      phase1_surface_normalize_transfer_refined_nonreference_session_spine
        session
  | None => None
  end.

Theorem
  phase1_surface_normalize_transfer_refined_nonreference_session_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_transfer_refined_nonreference_session_tree tree =
      Some refined ->
    phase1_surface_transfer_refined_nonreference_session_spine_tree refined =
      tree.
Proof.
  intros tree refined Hnormalize.
  unfold
    phase1_surface_normalize_transfer_refined_nonreference_session_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_nonreference_session_spine tree)
    as [session |] eqn:Hsession; try discriminate Hnormalize.
  transitivity (phase1_surface_nonreference_session_spine_tree session).
  - eapply
      phase1_surface_normalize_transfer_refined_nonreference_session_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_nonreference_session_spine_round_trip.
    exact Hsession.
Qed.
