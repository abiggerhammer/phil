From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lists.List
  Strings.String Lia.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstSourceHeader
  GrammarAstGenericRequirementsSpine
  GrammarAstGenericRequirementsTotality
  GrammarAstExpressionOuterSpine
  GrammarAstParenthesizedExpressionSpine
  GrammarAstTupleExpressionSpine
  GrammarAstRecursiveGrouping
  GrammarAstRecursiveGroupingWellFormed.

Import ListNotations.
Open Scope string_scope.

(* A computable sufficient bound. No caller-supplied recursive success
   assumption and no existential choice of fuel is needed at the entry point. *)
Fixpoint phase1_surface_grouping_tree_size (tree : ParseTree) : nat :=
  match tree with
  | PTLiteral _ | PTLexical _ _ | PTOptionalNone => 1
  | PTNonterminal _ body | PTAlternative _ body | PTOptionalSome body =>
      S (phase1_surface_grouping_tree_size body)
  | PTSequence items | PTRepetition items =>
      S (fold_right
        (fun item total => phase1_surface_grouping_tree_size item + total)
        0 items)
  end.

Definition phase1_surface_normalize_recursive_grouping
  (tree : ParseTree) : option Phase1SurfaceRecursiveGroupingTree :=
  phase1_surface_normalize_recursive_grouping_fuel
    (phase1_surface_grouping_tree_size tree) tree.

Definition phase1_surface_normalize_recursive_grouping_expression
  (tree : ParseTree) : option Phase1SurfaceRecursiveGroupingExpression :=
  phase1_surface_normalize_recursive_grouping_expression_fuel
    (phase1_surface_grouping_tree_size tree) tree.

Inductive Phase1GroupingDirectChild : ParseTree -> ParseTree -> Prop :=
| grouping_child_nonterminal : forall name body,
    Phase1GroupingDirectChild body (PTNonterminal name body)
| grouping_child_sequence : forall item items,
    In item items -> Phase1GroupingDirectChild item (PTSequence items)
| grouping_child_alternative : forall index body,
    Phase1GroupingDirectChild body (PTAlternative index body)
| grouping_child_optional : forall body,
    Phase1GroupingDirectChild body (PTOptionalSome body)
| grouping_child_repetition : forall item items,
    In item items -> Phase1GroupingDirectChild item (PTRepetition items).

Inductive Phase1GroupingSubtree : ParseTree -> ParseTree -> Prop :=
| grouping_subtree_child : forall child parent,
    Phase1GroupingDirectChild child parent ->
    Phase1GroupingSubtree child parent
| grouping_subtree_below : forall child middle parent,
    Phase1GroupingSubtree child middle ->
    Phase1GroupingDirectChild middle parent ->
    Phase1GroupingSubtree child parent.

Lemma phase1_surface_grouping_tree_size_positive :
  forall tree, 0 < phase1_surface_grouping_tree_size tree.
Proof. intros tree. destruct tree; cbn; lia. Qed.

Lemma phase1_surface_grouping_list_size_member :
  forall tree items,
    In tree items ->
    phase1_surface_grouping_tree_size tree <=
      fold_right
        (fun item total => phase1_surface_grouping_tree_size item + total)
        0 items.
Proof.
  intros tree items.
  induction items as [|item rest IH]; intros Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst item. cbn. lia.
    + specialize (IH Hin). cbn. lia.
Qed.

Theorem phase1_surface_normalize_recursive_grouping_round_trip :
  forall tree converted,
    phase1_surface_normalize_recursive_grouping tree = Some converted ->
    phase1_surface_recursive_grouping_tree converted = tree.
Proof.
  intros tree converted Hnormalize.
  eapply phase1_surface_normalize_recursive_grouping_fuel_round_trip.
  exact Hnormalize.
Qed.

Lemma phase1_surface_grouping_direct_child_smaller :
  forall child parent,
    Phase1GroupingDirectChild child parent ->
    phase1_surface_grouping_tree_size child <
      phase1_surface_grouping_tree_size parent.
Proof.
  intros child parent Hchild.
  destruct Hchild; cbn; try lia;
    pose proof (phase1_surface_grouping_list_size_member _ _ H); lia.
Qed.

Lemma phase1_surface_grouping_subtree_smaller :
  forall child parent,
    Phase1GroupingSubtree child parent ->
    phase1_surface_grouping_tree_size child <
      phase1_surface_grouping_tree_size parent.
Proof.
  intros child parent Hchild.
  induction Hchild.
  - eapply phase1_surface_grouping_direct_child_smaller. exact H.
  - pose proof (phase1_surface_grouping_direct_child_smaller _ _ H).
    lia.
Qed.

Lemma phase1_surface_grouping_direct_child_well_formed :
  forall child parent,
    Phase1GroupingDirectChild child parent ->
    Phase1SurfaceGroupingWellFormed parent ->
    Phase1SurfaceGroupingWellFormed child.
Proof.
  intros child parent Hchild Hwell.
  destruct Hchild; inversion Hwell; subst; eauto;
    match goal with
    | Hall : Forall Phase1SurfaceGroupingWellFormed _,
      Hin : In _ _ |- _ =>
        rewrite Forall_forall in Hall; exact (Hall _ Hin)
    end.
Qed.

Lemma phase1_surface_grouping_subtree_well_formed :
  forall child parent,
    Phase1GroupingSubtree child parent ->
    Phase1SurfaceGroupingWellFormed parent ->
    Phase1SurfaceGroupingWellFormed child.
Proof.
  intros child parent Hchild.
  induction Hchild; intros Hwell.
  - eapply phase1_surface_grouping_direct_child_well_formed; eauto.
  - apply IHHchild.
    eapply phase1_surface_grouping_direct_child_well_formed; eauto.
Qed.

Lemma phase1_surface_grouping_outer_base_subtree :
  forall tree outer,
    phase1_surface_normalize_expression_outer_spine tree = Some outer ->
    Phase1GroupingSubtree (phase1_expression_outer_spine_base outer) tree.
Proof.
  intros tree [base fallback] Houter.
  rewrite <-
    (phase1_surface_normalize_expression_outer_spine_round_trip _ _ Houter).
  unfold phase1_surface_expression_outer_spine_tree. cbn.
  eapply grouping_subtree_below; [|apply grouping_child_nonterminal].
  apply grouping_subtree_child. apply grouping_child_sequence.
  left. reflexivity.
Qed.

Lemma phase1_surface_grouping_parenthesized_subtree :
  forall tree grouped,
    phase1_surface_normalize_parenthesized_expression_spine tree = Some grouped ->
    Phase1GroupingSubtree
      (phase1_parenthesized_expression_spine_expression grouped) tree.
Proof.
  intros tree [nested] Hgrouped.
  rewrite <-
    (phase1_surface_normalize_parenthesized_expression_spine_round_trip
      _ _ Hgrouped).
  unfold phase1_surface_parenthesized_expression_spine_tree. cbn.
  eapply grouping_subtree_below; [|apply grouping_child_nonterminal].
  apply grouping_subtree_child. apply grouping_child_sequence.
  right. left. reflexivity.
Qed.

Lemma phase1_surface_grouping_tuple_subtrees :
  forall tree tuple child,
    phase1_surface_normalize_tuple_expression_spine tree = Some tuple ->
    In child
      (phase1_tuple_expression_spine_first tuple ::
       phase1_tuple_expression_spine_second tuple ::
       phase1_tuple_expression_spine_rest tuple) ->
    Phase1GroupingSubtree child tree.
Proof.
  intros tree [first second rest] child Htuple Hin.
  rewrite <-
    (phase1_surface_normalize_tuple_expression_spine_round_trip _ _ Htuple).
  unfold phase1_surface_tuple_expression_spine_tree. cbn in Hin |- *.
  eapply grouping_subtree_below; [|apply grouping_child_nonterminal].
  destruct Hin as [Heq | [Heq | Hin]].
    + subst child. apply grouping_subtree_child.
      apply grouping_child_sequence. cbn. auto.
    + subst child. apply grouping_subtree_child.
      apply grouping_child_sequence. cbn. auto.
    + eapply grouping_subtree_below with
        (middle := PTRepetition
          (map phase1_surface_tuple_expression_suffix_tree rest)).
      * eapply grouping_subtree_below with
          (middle := phase1_surface_tuple_expression_suffix_tree child).
        -- apply grouping_subtree_child. apply grouping_child_sequence.
           right. left. reflexivity.
        -- apply grouping_child_repetition.
           apply in_map. exact Hin.
      * apply grouping_child_sequence. cbn.
        right. right. right. right. left. reflexivity.
Qed.

Lemma phase1_surface_grouping_validated_expression_shape :
  forall tree,
    phase1_surface_validate_named_node "expression" tree = Some tt ->
    exists body, tree = PTNonterminal "expression" body.
Proof.
  intros tree Hvalidate.
  unfold phase1_surface_validate_named_node in Hvalidate.
  destruct (phase1_surface_expect_nonterminal "expression" tree)
    as [body |] eqn:Hbody; try discriminate Hvalidate.
  exists body.
  eapply phase1_surface_expect_nonterminal_round_trip. exact Hbody.
Qed.

Lemma phase1_surface_grouping_parenthesized_child_named :
  forall tree grouped,
    phase1_surface_normalize_parenthesized_expression_spine tree = Some grouped ->
    phase1_surface_validate_named_node "expression"
      (phase1_parenthesized_expression_spine_expression grouped) = Some tt.
Proof.
  intros tree grouped Hnormalize.
  unfold phase1_surface_normalize_parenthesized_expression_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "parenthesized_expression" tree)
    as [body |]; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body) as [items |];
    try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[open_tree nested] close_tree] |]; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "(" open_tree) as [[] |];
    try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "expression" nested)
    as [[] |] eqn:Hnested; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ")" close_tree) as [[] |];
    try discriminate Hnormalize.
  inversion Hnormalize; subst grouped. exact Hnested.
Qed.

Lemma phase1_surface_grouping_tuple_suffix_child_named :
  forall tree child,
    phase1_surface_normalize_tuple_expression_suffix tree = Some child ->
    phase1_surface_validate_named_node "expression" child = Some tt.
Proof.
  intros tree child Hnormalize.
  unfold phase1_surface_normalize_tuple_expression_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree) as [items |];
    try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items) as [[comma nested] |];
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma) as [[] |];
    try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "expression" nested)
    as [[] |] eqn:Hnested; try discriminate Hnormalize.
  inversion Hnormalize; subst child. exact Hnested.
Qed.

Lemma phase1_surface_grouping_tuple_suffix_children_named :
  forall trees children,
    phase1_surface_normalize_tuple_expression_suffixes trees = Some children ->
    Forall
      (fun child =>
        phase1_surface_validate_named_node "expression" child = Some tt)
      children.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros children Hnormalize.
  - inversion Hnormalize; constructor.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_tuple_expression_suffix tree)
      as [child |] eqn:Hchild; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_tuple_expression_suffixes rest)
      as [children_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst children.
    constructor.
    + eapply phase1_surface_grouping_tuple_suffix_child_named. exact Hchild.
    + eapply IH. reflexivity.
Qed.

Lemma phase1_surface_grouping_tuple_children_named :
  forall tree tuple,
    phase1_surface_normalize_tuple_expression_spine tree = Some tuple ->
    Forall
      (fun child =>
        phase1_surface_validate_named_node "expression" child = Some tt)
      (phase1_tuple_expression_spine_first tuple ::
       phase1_tuple_expression_spine_second tuple ::
       phase1_tuple_expression_spine_rest tuple).
Proof.
  intros tree tuple Hnormalize.
  unfold phase1_surface_normalize_tuple_expression_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "tuple_expression" tree)
    as [body |]; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body) as [items |];
    try discriminate Hnormalize.
  destruct (phase1_surface_exact6 items)
    as [[[[[[open_tree first] comma_tree] second] rest_tree] close_tree] |];
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "(" open_tree) as [[] |];
    try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "expression" first)
    as [[] |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma_tree) as [[] |];
    try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "expression" second)
    as [[] |] eqn:Hsecond; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition rest_tree) as [rest_trees |];
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ")" close_tree) as [[] |];
    try discriminate Hnormalize.
  destruct (phase1_surface_normalize_tuple_expression_suffixes rest_trees)
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst tuple. cbn.
  constructor; [exact Hfirst |].
  constructor; [exact Hsecond |].
  eapply phase1_surface_grouping_tuple_suffix_children_named. exact Hrest.
Qed.

Lemma phase1_surface_grouping_traverse_total {A B : Type} :
  forall (convert : A -> option B) items,
    (forall item, In item items -> exists value, convert item = Some value) ->
    exists values, phase1_surface_grouping_traverse convert items = Some values.
Proof.
  intros convert items.
  induction items as [|item rest IH]; intros Htotal.
  - exists []. reflexivity.
  - destruct (Htotal item (or_introl eq_refl)) as [value Hvalue].
    destruct (IH (fun child Hin => Htotal child (or_intror Hin)))
      as [values Hvalues].
    exists (value :: values). cbn. rewrite Hvalue, Hvalues. reflexivity.
Qed.

Lemma phase1_surface_grouping_expression_with_total :
  forall fuel tree,
    phase1_surface_validate_named_node "expression" tree = Some tt ->
    (exists converted,
      phase1_surface_normalize_recursive_grouping_fuel fuel tree =
        Some converted) ->
    exists expression,
      phase1_surface_grouping_expression_with
        (phase1_surface_normalize_recursive_grouping_fuel fuel) tree =
        Some expression.
Proof.
  intros fuel tree Hnamed [converted Hconverted].
  destruct (phase1_surface_grouping_validated_expression_shape _ Hnamed)
    as [body Htree]. subst tree.
  destruct
    (phase1_surface_recursive_grouping_expression_result
      _ _ _ Hconverted) as [expression Heq].
  subst converted. exists expression.
  unfold phase1_surface_grouping_expression_with.
  rewrite Hconverted. reflexivity.
Qed.

Theorem phase1_surface_recursive_grouping_sufficient_fuel :
  forall tree,
    Phase1SurfaceGroupingWellFormed tree ->
    forall fuel,
      phase1_surface_grouping_tree_size tree <= fuel ->
      exists converted,
        phase1_surface_normalize_recursive_grouping_fuel fuel tree =
          Some converted.
Proof.
  assert (Htotal :
    forall size tree,
      phase1_surface_grouping_tree_size tree = size ->
      Phase1SurfaceGroupingWellFormed tree ->
      forall fuel, size <= fuel ->
        exists converted,
          phase1_surface_normalize_recursive_grouping_fuel fuel tree =
            Some converted).
  {
    induction size using lt_wf_ind.
    intros tree Hsize Hwell [|fuel] Hfuel.
    - pose proof (phase1_surface_grouping_tree_size_positive tree). lia.
    - assert (Hchild_total :
        forall child,
          Phase1GroupingSubtree child tree ->
          exists converted,
            phase1_surface_normalize_recursive_grouping_fuel fuel child =
              Some converted).
      {
        intros child Hsubtree.
        pose proof
          (phase1_surface_grouping_subtree_smaller _ _ Hsubtree) as Hsmaller.
        eapply (H (phase1_surface_grouping_tree_size child)).
        - lia.
        - reflexivity.
        - eapply phase1_surface_grouping_subtree_well_formed; eauto.
        - lia.
      }
      destruct tree as
        [literal |class lexeme |name body |items |index body
        | |body |items].
      + exists (Phase1GroupingLiteral literal). reflexivity.
      + exists (Phase1GroupingLexical class lexeme). reflexivity.
      + assert (Hshallow :
          phase1_surface_grouping_shallow_valid name (PTNonterminal name body)).
        { inversion Hwell; assumption. }
        destruct (String.eqb name "command_expression") eqn:Hcommand.
        * exists (Phase1GroupingCommandBoundary body).
          cbn. rewrite Hcommand. reflexivity.
        * destruct (String.eqb name "fallback") eqn:Hfallback.
          -- exists (Phase1GroupingFallbackBoundary body).
             cbn. rewrite Hcommand, Hfallback. reflexivity.
          -- destruct (String.eqb name "expression") eqn:Hexpression.
             ++ apply String.eqb_eq in Hexpression. subst name.
                change (exists outer,
                  phase1_surface_normalize_expression_outer_spine
                    (PTNonterminal "expression" body) = Some outer) in Hshallow.
                destruct Hshallow as [outer Houter].
                destruct
                  (Hchild_total _
                    (phase1_surface_grouping_outer_base_subtree _ _ Houter))
                  as [base Hbase].
                exists
                  (Phase1GroupingExpression
                    (Phase1GroupingExpressionValue base
                      (phase1_expression_outer_spine_fallback outer))).
                cbn -[phase1_surface_normalize_expression_outer_spine].
                rewrite Houter, Hbase. reflexivity.
             ++ destruct (String.eqb name "parenthesized_expression") eqn:Hparen.
                ** apply String.eqb_eq in Hparen. subst name.
                   change (exists grouped,
                     phase1_surface_normalize_parenthesized_expression_spine
                       (PTNonterminal "parenthesized_expression" body) =
                       Some grouped) in Hshallow.
                   destruct Hshallow as [grouped Hgrouped].
                   destruct
                     (phase1_surface_grouping_expression_with_total fuel _
                       (phase1_surface_grouping_parenthesized_child_named
                         _ _ Hgrouped)
                       (Hchild_total _
                         (phase1_surface_grouping_parenthesized_subtree
                           _ _ Hgrouped)))
                     as [expression Hnested].
                   exists (Phase1GroupingParenthesized expression).
                   cbn -[phase1_surface_normalize_parenthesized_expression_spine
                     phase1_surface_grouping_expression_with].
                   rewrite Hgrouped, Hnested. reflexivity.
                ** destruct (String.eqb name "tuple_expression") eqn:Htuple.
                   --- apply String.eqb_eq in Htuple. subst name.
                       change (exists tuple,
                         phase1_surface_normalize_tuple_expression_spine
                           (PTNonterminal "tuple_expression" body) =
                           Some tuple) in Hshallow.
                       destruct Hshallow as [tuple Htuple_shape].
                       assert (Hexpressions :
                         forall child,
                           In child
                             (phase1_tuple_expression_spine_first tuple ::
                              phase1_tuple_expression_spine_second tuple ::
                              phase1_tuple_expression_spine_rest tuple) ->
                           exists expression,
                             phase1_surface_grouping_expression_with
                               (phase1_surface_normalize_recursive_grouping_fuel
                                 fuel) child = Some expression).
                       {
                         intros child Hin.
                         eapply phase1_surface_grouping_expression_with_total.
                         - pose proof
                             (phase1_surface_grouping_tuple_children_named
                               _ _ Htuple_shape) as Hnamed.
                           rewrite Forall_forall in Hnamed.
                           exact (Hnamed child Hin).
                         - apply Hchild_total.
                           eapply phase1_surface_grouping_tuple_subtrees; eauto.
                       }
                       destruct
                         (Hexpressions _ (or_introl eq_refl)) as [first Hfirst].
                       destruct
                         (Hexpressions _ (or_intror (or_introl eq_refl)))
                         as [second Hsecond].
                       destruct
                         (phase1_surface_grouping_traverse_total
                           (phase1_surface_grouping_expression_with
                             (phase1_surface_normalize_recursive_grouping_fuel
                               fuel))
                           (phase1_tuple_expression_spine_rest tuple)
                           (fun child Hin =>
                             Hexpressions child (or_intror (or_intror Hin))))
                         as [rest Hrest].
                       exists (Phase1GroupingTuple first second rest).
                       cbn -[phase1_surface_normalize_tuple_expression_spine
                         phase1_surface_grouping_expression_with].
                       rewrite Htuple_shape, Hfirst, Hsecond, Hrest.
                       reflexivity.
                   --- destruct
                         (Hchild_total body
                           (grouping_subtree_child _ _
                             (grouping_child_nonterminal name body)))
                         as [converted Hbody].
                       exists (Phase1GroupingNonterminal name converted).
                       cbn.
                       rewrite Hcommand, Hfallback, Hexpression, Hparen, Htuple,
                         Hbody.
                       reflexivity.
      + destruct
          (phase1_surface_grouping_traverse_total
            (phase1_surface_normalize_recursive_grouping_fuel fuel) items
            (fun child Hin =>
              Hchild_total child
                (grouping_subtree_child _ _
                  (grouping_child_sequence child items Hin))))
          as [converted Hitems].
        exists (Phase1GroupingSequence converted).
        cbn. rewrite Hitems. reflexivity.
      + destruct
          (Hchild_total body
            (grouping_subtree_child _ _ (grouping_child_alternative index body)))
          as [converted Hbody].
        exists (Phase1GroupingAlternative index converted).
        cbn. rewrite Hbody. reflexivity.
      + exists Phase1GroupingOptionalNone. reflexivity.
      + destruct
          (Hchild_total body
            (grouping_subtree_child _ _ (grouping_child_optional body)))
          as [converted Hbody].
        exists (Phase1GroupingOptionalSome converted).
        cbn. rewrite Hbody. reflexivity.
      + destruct
          (phase1_surface_grouping_traverse_total
            (phase1_surface_normalize_recursive_grouping_fuel fuel) items
            (fun child Hin =>
              Hchild_total child
                (grouping_subtree_child _ _
                  (grouping_child_repetition child items Hin))))
          as [converted Hitems].
        exists (Phase1GroupingRepetition converted).
        cbn. rewrite Hitems. reflexivity.
  }
  intros tree Hwell fuel Hfuel.
  eapply (Htotal _ tree eq_refl Hwell fuel Hfuel).
Qed.

Theorem phase1_surface_recursive_grouping_total_from_derivation :
  forall path syntax input rest tree,
    Derives phase1_surface_rules path syntax input rest tree ->
    exists converted,
      phase1_surface_normalize_recursive_grouping tree = Some converted /\
      phase1_surface_recursive_grouping_tree converted = tree.
Proof.
  intros path syntax input rest tree Hderive.
  destruct
    (phase1_surface_recursive_grouping_sufficient_fuel tree
      (phase1_surface_grouping_well_formed_from_derivation
        _ _ _ _ _ Hderive)
      (phase1_surface_grouping_tree_size tree) (Nat.le_refl _))
    as [converted Hconverted].
  exists converted. split.
  - exact Hconverted.
  - eapply phase1_surface_normalize_recursive_grouping_fuel_round_trip.
    exact Hconverted.
Qed.

Theorem phase1_surface_recursive_grouping_expression_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "expression")
      input rest tree ->
    exists expression,
      phase1_surface_normalize_recursive_grouping_expression tree =
        Some expression /\
      phase1_surface_recursive_grouping_expression_tree expression = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_recursive_grouping_total_from_derivation
      _ _ _ _ _ Hderive) as [converted [Hconverted Htree]].
  destruct
    (phase1_surface_grouping_expression_with_total _ _
      (phase1_surface_validate_named_node_total_from_derivation
        "expression" _ _ _ _ Hderive)
      (ex_intro _ converted Hconverted)) as [expression Hexpression].
  exists expression. split.
  - exact Hexpression.
  - eapply phase1_surface_grouping_expression_with_round_trip.
    + apply phase1_surface_normalize_recursive_grouping_fuel_round_trip.
    + exact Hexpression.
Qed.
