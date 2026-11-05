From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstRecordTotality
  GrammarAstSourceHeaderTotality
  GrammarAstEffectSetSpine
  GrammarAstEffectSetTotality
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstEffectExpressionRecursiveGroupingSpine
  GrammarAstEffectExpressionRecursiveGroupingSpineTotality
  GrammarAstEffectSetRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  The literal derivation supplies an effect_expression derivation for every
  member, including every repeated comma suffix. Raw and legacy list adapters
  consume those derivations separately, preserving order and multiplicity.
  The enclosing choice supplies the literal derivation or retains its existing
  static-reference carrier directly.

  Public literal and choice totality require only canonical Derives judgments.
  There is no caller-supplied fuel or child-normalization-success premise and
  no dependency on the legacy shared-fuel totality chain. The effect carrier's
  boundaries remain inherited.
*)

Lemma phase1_surface_effect_set_recursive_grouping_suffix_derivation :
  forall path input rest effect,
    Derives phase1_surface_rules path
      (ESequence [ELiteral ","; ENonterminal "effect_expression"])
      input rest (phase1_surface_effect_set_suffix_tree effect) ->
    exists effect_path before_effect after_effect,
      Derives phase1_surface_rules effect_path (ENonterminal "effect_expression")
        before_effect after_effect effect.
Proof.
  intros path input rest effect Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ELiteral ","; ENonterminal "effect_expression"]
      input rest _ Hderive)
    as [trees [Htree Hitems]].
  cbn [phase1_surface_effect_set_suffix_tree
    phase1_surface_effect_expression_tree] in Htree.
  inversion Htree; subst trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0 (ELiteral ",")
      [ENonterminal "effect_expression"] input rest _ Hitems)
    as [after_comma [comma_tree [tail_trees
      [Htrees [Hcomma Htail]]]]].
  inversion Htrees; subst comma_tree tail_trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1 (ENonterminal "effect_expression") []
      after_comma rest _ Htail)
    as [after_effect [effect_tree [nil_trees
      [Htail_trees [Heffect Hnil]]]]].
  inversion Htail_trees; subst effect_tree nil_trees.
  do 3 eexists.
  exact Heffect.
Qed.

Lemma phase1_surface_effect_set_recursive_grouping_repetition_derives_members :
  forall effects path input rest,
    DerivesRepetition phase1_surface_rules path
      (ESequence [ELiteral ","; ENonterminal "effect_expression"])
      input rest (map phase1_surface_effect_set_suffix_tree effects) ->
    Forall
      (fun effect => exists effect_path before_effect after_effect,
        Derives phase1_surface_rules effect_path (ENonterminal "effect_expression")
          before_effect after_effect effect)
      effects.
Proof.
  induction effects as [|effect effects IH]; intros path input rest Hderive.
  - constructor.
  - cbn [map] in Hderive.
    inversion Hderive as
      [|path' body' input' middle rest' tree trees Hitem Hprogress Htail]; subst.
    constructor.
    + eapply phase1_surface_effect_set_recursive_grouping_suffix_derivation.
      exact Hitem.
    + eapply IH.
      exact Htail.
Qed.

Lemma phase1_surface_effect_set_recursive_grouping_entries_derive_members :
  forall path input rest effects,
    Derives phase1_surface_rules path
      (EOptional
        (ESequence
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence [ELiteral ","; ENonterminal "effect_expression"]) ]))
      input rest (phase1_surface_effect_set_entries_tree effects) ->
    Forall
      (fun effect => exists effect_path before_effect after_effect,
        Derives phase1_surface_rules effect_path (ENonterminal "effect_expression")
          before_effect after_effect effect)
      effects.
Proof.
  intros path input rest [|first effects] Hderive.
  - constructor.
  - destruct
      (optional_derivation_exposes_presence
        phase1_surface_rules path
        (ESequence
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence [ELiteral ","; ENonterminal "effect_expression"]) ])
        input rest _ Hderive)
      as [[_ Hnone] | [body [Hsome Hbody]]].
    + cbn [phase1_surface_effect_set_entries_tree] in Hnone.
      discriminate Hnone.
    + cbn [phase1_surface_effect_set_entries_tree
        phase1_surface_effect_expression_tree] in Hsome.
      inversion Hsome; subst body.
      destruct
        (derives_sequence_expression_exposes_items
          phase1_surface_rules _
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence [ELiteral ","; ENonterminal "effect_expression"]) ]
          input rest _ Hbody)
        as [trees [Hsequence Hitems]].
      inversion Hsequence; subst trees.
      destruct
        (derives_sequence_cons_exposes_head_exact
          phase1_surface_rules _ 0 (ENonterminal "effect_expression")
          [ ERepetition
              (ESequence [ELiteral ","; ENonterminal "effect_expression"]) ]
          input rest _ Hitems)
        as [after_first [first_tree [tail_trees
          [Htrees [Hfirst Htail]]]]].
      inversion Htrees; subst first_tree tail_trees.
      destruct
        (derives_sequence_cons_exposes_head_exact
          phase1_surface_rules _ 1
          (ERepetition
            (ESequence [ELiteral ","; ENonterminal "effect_expression"])) []
          after_first rest _ Htail)
        as [after_suffixes [suffixes_tree [nil_trees
          [Htail_trees [Hsuffixes Hnil]]]]].
      inversion Htail_trees; subst suffixes_tree nil_trees.
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ (ESequence [ELiteral ","; ENonterminal "effect_expression"])
          _ _ _ Hsuffixes)
        as [suffix_trees [Hsuffix_trees Hrepetition]].
      inversion Hsuffix_trees; subst suffix_trees.
      constructor.
      * do 3 eexists. exact Hfirst.
      * eapply phase1_surface_effect_set_recursive_grouping_repetition_derives_members.
        exact Hrepetition.
Qed.

Lemma phase1_surface_effect_set_literal_recursive_grouping_derives_members :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "effect_set_literal") input rest
      (phase1_surface_effect_set_literal_spine_tree previous) ->
    Forall
      (fun effect => exists effect_path before_effect after_effect,
        Derives phase1_surface_rules effect_path (ENonterminal "effect_expression")
          before_effect after_effect effect)
      (phase1_effect_set_literal_spine_effects previous).
Proof.
  intros path input rest [effects] Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_set_literal" input rest _ Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_effect_set_literal_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  cbn [phase1_surface_effect_set_literal_spine_tree
    phase1_effect_set_literal_spine_effects] in Htree.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules _
      [ ELiteral "{";
        EOptional
          (ESequence
            [ ENonterminal "effect_expression";
              ERepetition
                (ESequence [ELiteral ","; ENonterminal "effect_expression"]) ]);
        ELiteral "}" ]
      input rest _ Hbody)
    as [trees [Hsequence Hitems]].
  inversion Hsequence; subst trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 0 (ELiteral "{")
      [ EOptional
          (ESequence
            [ ENonterminal "effect_expression";
              ERepetition
                (ESequence [ELiteral ","; ENonterminal "effect_expression"]) ]);
        ELiteral "}" ]
      input rest _ Hitems)
    as [after_open [open_tree [tail_trees
      [Htrees [Hopen Htail]]]]].
  inversion Htrees; subst open_tree tail_trees.
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 1
      (EOptional
        (ESequence
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence [ELiteral ","; ENonterminal "effect_expression"]) ]))
      [ELiteral "}"] after_open rest _ Htail)
    as [after_entries [entries_tree [close_trees
      [Htail_trees [Hentries Hclose]]]]].
  inversion Htail_trees; subst entries_tree close_trees.
  eapply phase1_surface_effect_set_recursive_grouping_entries_derive_members.
  exact Hentries.
Qed.

Lemma
  phase1_surface_normalize_effect_set_recursive_grouping_values_total_from_member_derivations :
  forall effects,
    Forall
      (fun effect => exists effect_path before_effect after_effect,
        Derives phase1_surface_rules effect_path (ENonterminal "effect_expression")
          before_effect after_effect effect)
      effects ->
    exists refined,
      phase1_surface_normalize_effect_set_recursive_grouping_values effects =
        Some refined /\
      map phase1_surface_effect_expression_recursive_grouping_spine_tree refined =
        effects.
Proof.
  intros effects Hmembers.
  induction Hmembers as [|effect effects Heffect Hmembers IH].
  - exists []. split; reflexivity.
  - destruct Heffect as [path [input [rest Hderive]]].
    destruct
      (phase1_surface_normalize_effect_expression_recursive_grouping_tree_total_from_derivation
        path input rest effect Hderive)
      as [actual [Hactual Hactual_tree]].
    destruct IH as [actual_rest [Hactual_rest Hactual_rest_tree]].
    exists (actual :: actual_rest).
    split.
    + cbn [phase1_surface_normalize_effect_set_recursive_grouping_values].
      rewrite Hactual, Hactual_rest.
      reflexivity.
    + cbn [map].
      rewrite Hactual_tree, Hactual_rest_tree.
      reflexivity.
Qed.

Lemma
  phase1_surface_refine_effect_set_recursive_grouping_values_total_from_member_derivations :
  forall effects,
    Forall
      (fun effect => exists effect_path before_effect after_effect,
        Derives phase1_surface_rules effect_path (ENonterminal "effect_expression")
          before_effect after_effect effect)
      (map
        phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
        effects) ->
    exists refined,
      phase1_surface_refine_effect_set_recursive_grouping_values effects =
        Some refined /\
      map phase1_surface_effect_expression_recursive_grouping_spine_tree refined =
        map
          phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
          effects.
Proof.
  induction effects as [|effect effects IH]; intros Hmembers.
  - exists []. split; reflexivity.
  - cbn [map] in Hmembers.
    inversion Hmembers as [|tree trees Heffect Htail]; subst.
    destruct Heffect as [path [input [rest Hderive]]].
    destruct
      (phase1_surface_refine_effect_expression_recursive_grouping_total_from_derivation
        path input rest effect Hderive)
      as [actual [Hactual Hactual_tree]].
    destruct (IH Htail) as [actual_rest [Hactual_rest Hactual_rest_tree]].
    exists (actual :: actual_rest).
    split.
    + cbn [phase1_surface_refine_effect_set_recursive_grouping_values].
      rewrite Hactual, Hactual_rest.
      reflexivity.
    + cbn [map].
      rewrite Hactual_tree, Hactual_rest_tree.
      reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_set_literal_recursive_grouping_spine_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "effect_set_literal") input rest
      (phase1_surface_effect_set_literal_spine_tree previous) ->
    exists refined,
      phase1_surface_normalize_effect_set_literal_recursive_grouping_spine previous =
        Some refined /\
      phase1_surface_effect_set_literal_recursive_grouping_spine_base refined =
        previous.
Proof.
  intros path input rest [effects] Hderive.
  pose proof
    (phase1_surface_effect_set_literal_recursive_grouping_derives_members
      path input rest {| phase1_effect_set_literal_spine_effects := effects |}
      Hderive) as Hmembers.
  cbn [phase1_effect_set_literal_spine_effects] in Hmembers.
  destruct
    (phase1_surface_normalize_effect_set_recursive_grouping_values_total_from_member_derivations
      effects Hmembers)
    as [actual [Hnormalize Hmap]].
  exists {| phase1_effect_set_literal_recursive_grouping_spine_effects := actual |}.
  split.
  - unfold phase1_surface_normalize_effect_set_literal_recursive_grouping_spine.
    cbn [phase1_effect_set_literal_spine_effects].
    rewrite Hnormalize.
    reflexivity.
  - unfold phase1_surface_effect_set_literal_recursive_grouping_spine_base.
    cbn [phase1_effect_set_literal_recursive_grouping_spine_effects].
    rewrite Hmap.
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_set_literal_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "effect_set_literal")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_effect_set_literal_recursive_grouping_tree tree =
        Some refined /\
      phase1_surface_effect_set_literal_recursive_grouping_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_effect_set_literal_spine_total_from_derivation
      path input rest tree Hderive)
    as [previous [Hprevious Hprevious_tree]].
  rewrite <- Hprevious_tree in Hderive.
  destruct
    (phase1_surface_normalize_effect_set_literal_recursive_grouping_spine_total_from_derivation
      path input rest previous Hderive)
    as [refined [Hnormalize Hbase]].
  exists refined.
  split.
  - unfold phase1_surface_normalize_effect_set_literal_recursive_grouping_tree.
    rewrite Hprevious.
    exact Hnormalize.
  - unfold phase1_surface_effect_set_literal_recursive_grouping_spine_tree.
    rewrite Hbase.
    exact Hprevious_tree.
Qed.

Theorem
  phase1_surface_refine_effect_set_literal_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "effect_set_literal") input rest
      (phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_tree
        previous) ->
    exists refined,
      phase1_surface_refine_effect_set_literal_recursive_grouping previous =
        Some refined /\
      phase1_surface_effect_set_literal_recursive_grouping_spine_tree refined =
        phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_tree
          previous.
Proof.
  intros path input rest [effects] Hderive.
  rewrite <- phase1_surface_effect_set_recursive_grouping_legacy_literal_tree
    in Hderive.
  destruct
    (phase1_surface_refine_effect_set_recursive_grouping_values_total_from_member_derivations
      effects
      (phase1_surface_effect_set_literal_recursive_grouping_derives_members
        path input rest _ Hderive))
    as [actual [Hnormalize Hmap]].
  assert (Hliteral :
    phase1_surface_refine_effect_set_literal_recursive_grouping
      {| phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects :=
           effects |} =
    Some {| phase1_effect_set_literal_recursive_grouping_spine_effects := actual |}).
  {
    unfold phase1_surface_refine_effect_set_literal_recursive_grouping.
    cbn [phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects].
    rewrite Hnormalize.
    reflexivity.
  }
  eexists. split.
  - exact Hliteral.
  - eapply phase1_surface_refine_effect_set_literal_recursive_grouping_round_trip.
    exact Hliteral.
Qed.

Lemma phase1_surface_effect_set_recursive_grouping_literal_derivation :
  forall path input rest literal_tree,
    Derives phase1_surface_rules path (ENonterminal "effect_set_expression")
      input rest
      (PTNonterminal "effect_set_expression" (PTAlternative 0 literal_tree)) ->
    exists literal_path,
      Derives phase1_surface_rules literal_path (ENonterminal "effect_set_literal")
        input rest literal_tree.
Proof.
  intros path input rest literal_tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_set_expression" input rest _ Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_effect_set_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules _
      [ENonterminal "effect_set_literal"; ENonterminal "static_reference"]
      input rest _ Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  inversion Hsubtree; subst index selected.
  cbn in Hnth. inversion Hnth; subst item.
  eexists. exact Hselected.
Qed.

Theorem
  phase1_surface_normalize_effect_set_recursive_grouping_spine_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "effect_set_expression")
      input rest (phase1_surface_effect_set_spine_tree previous) ->
    exists refined,
      phase1_surface_normalize_effect_set_recursive_grouping_spine previous =
        Some refined /\
      phase1_surface_effect_set_recursive_grouping_spine_base refined = previous.
Proof.
  intros path input rest [literal |reference] Hderive.
  - destruct
      (phase1_surface_effect_set_recursive_grouping_literal_derivation
        path input rest _ Hderive)
      as [literal_path Hliteral].
    destruct
      (phase1_surface_normalize_effect_set_literal_recursive_grouping_spine_total_from_derivation
        literal_path input rest literal Hliteral)
      as [actual [Hnormalize Hbase]].
    exists (Phase1EffectSetGroupingLiteral actual).
    split.
    + cbn [phase1_surface_normalize_effect_set_recursive_grouping_spine].
      rewrite Hnormalize.
      reflexivity.
    + cbn [phase1_surface_effect_set_recursive_grouping_spine_base].
      rewrite Hbase.
      reflexivity.
  - exists (Phase1EffectSetGroupingReference reference). split; reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_set_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "effect_set_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_effect_set_recursive_grouping_tree tree =
        Some refined /\
      phase1_surface_effect_set_recursive_grouping_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_effect_set_spine_total_from_derivation
      path input rest tree Hderive)
    as [previous [Hprevious Hprevious_tree]].
  rewrite <- Hprevious_tree in Hderive.
  destruct
    (phase1_surface_normalize_effect_set_recursive_grouping_spine_total_from_derivation
      path input rest previous Hderive)
    as [refined [Hnormalize Hbase]].
  exists refined.
  split.
  - unfold phase1_surface_normalize_effect_set_recursive_grouping_tree.
    rewrite Hprevious.
    exact Hnormalize.
  - unfold phase1_surface_effect_set_recursive_grouping_spine_tree.
    rewrite Hbase.
    exact Hprevious_tree.
Qed.

Theorem phase1_surface_refine_effect_set_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "effect_set_expression")
      input rest
      (phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_spine_tree
        previous) ->
    exists refined,
      phase1_surface_refine_effect_set_recursive_grouping previous = Some refined /\
      phase1_surface_effect_set_recursive_grouping_spine_tree refined =
        phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_spine_tree
          previous.
Proof.
  intros path input rest [literal |reference] Hderive.
  - destruct
      (phase1_surface_effect_set_recursive_grouping_literal_derivation
        path input rest _ Hderive)
      as [literal_path Hliteral].
    destruct
      (phase1_surface_refine_effect_set_literal_recursive_grouping_total_from_derivation
        literal_path input rest literal Hliteral)
      as [actual [Hnormalize Htree]].
    exists (Phase1EffectSetGroupingLiteral actual).
    split.
    + cbn [phase1_surface_refine_effect_set_recursive_grouping].
      rewrite Hnormalize.
      reflexivity.
    + change
        (PTNonterminal "effect_set_expression"
          (PTAlternative 0
            (phase1_surface_effect_set_literal_recursive_grouping_spine_tree actual)) =
         PTNonterminal "effect_set_expression"
          (PTAlternative 0
            (phase1_surface_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_tree
              literal))).
      rewrite Htree.
      reflexivity.
  - exists (Phase1EffectSetGroupingReference reference). split; reflexivity.
Qed.
