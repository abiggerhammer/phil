from pathlib import Path


script21 = Path("scripts/debug_phase1_surface_witness_soundness_21.py").read_text()
exec(compile(script21, "<debug21>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()
block_start = source.index("Lemma computed_first_sem_sound_step :")
theorem_start = source.index("Theorem computed_first_sem_sound :", block_start)
theorem_end = source.index("\nLemma computed_first_sem_sound_at_expression_fuel :", theorem_start)

replacement = r'''Definition ComputedFirstFuelProperty
  (token : OverlapToken) (expression : EbnfExpression)
  (_ : ComputedFirstSem token expression) : Prop :=
  forall fuel,
    choice_bodies_nonnullable_fuel fuel expression = true ->
    exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression = Some tokens /\
      token_mem token tokens = true.

Definition ComputedFirstSequenceFuelProperty
  (token : OverlapToken) (items : list EbnfExpression)
  (_ : ComputedFirstSequenceSem token items) : Prop :=
  forall fuel,
    forallb (choice_bodies_nonnullable_fuel fuel) items = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ESequence items) = Some tokens /\
      token_mem token tokens = true.

Definition ComputedFirstAlternativeFuelProperty
  (token : OverlapToken) (items : list EbnfExpression)
  (_ : ComputedFirstAlternativeSem token items) : Prop :=
  forall fuel,
    forallb
      (fun item =>
        andb
          (negb
            (nullable_expression phase1_surface_nullable_facts item))
          (choice_bodies_nonnullable_fuel fuel item))
      items = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EAlternative items) = Some tokens /\
      token_mem token tokens = true.

Scheme ComputedFirstSem_ind' := Induction for ComputedFirstSem Sort Prop
with ComputedFirstSequenceSem_ind' := Induction for ComputedFirstSequenceSem Sort Prop
with ComputedFirstAlternativeSem_ind' := Induction for ComputedFirstAlternativeSem Sort Prop.

Combined Scheme ComputedFirst_mutind
  from ComputedFirstSem_ind', ComputedFirstSequenceSem_ind',
       ComputedFirstAlternativeSem_ind'.

Theorem computed_first_sem_sound_mutual :
  (forall token expression witness,
    ComputedFirstFuelProperty token expression witness) /\
  (forall token items witness,
    ComputedFirstSequenceFuelProperty token items witness) /\
  (forall token items witness,
    ComputedFirstAlternativeFuelProperty token items witness).
Proof.
  apply ComputedFirst_mutind.
  - intros token literal Htoken.
    unfold ComputedFirstFuelProperty.
    intros fuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + subst token.
      exists [OverlapLiteral literal]. split.
      * reflexivity.
      * unfold token_mem.
        rewrite overlap_token_eqb_refl.
        reflexivity.
  - intros token class_name Htoken.
    unfold ComputedFirstFuelProperty.
    intros fuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + subst token.
      exists [OverlapLexicalClass class_name]. split.
      * reflexivity.
      * unfold token_mem.
        rewrite overlap_token_eqb_refl.
        reflexivity.
  - intros token name Hmem.
    unfold ComputedFirstFuelProperty.
    intros fuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + exists (lookup_tokens name phase1_surface_first_facts). split.
      * reflexivity.
      * exact Hmem.
  - intros token items Hitems IHitems.
    unfold ComputedFirstFuelProperty, ComputedFirstSequenceFuelProperty in *.
    intros fuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + simpl in Hsafe.
      exact (IHitems fuel Hsafe).
  - intros token items Hitems IHitems.
    unfold ComputedFirstFuelProperty, ComputedFirstAlternativeFuelProperty in *.
    intros fuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + simpl in Hsafe.
      exact (IHitems fuel Hsafe).
  - intros token body Hbody IHbody.
    unfold ComputedFirstFuelProperty in *.
    intros fuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + simpl in Hsafe.
      apply andb_true_iff in Hsafe as [_ Hbody_safe].
      exact
        (computed_first_optional_result_lift
          token fuel body (IHbody fuel Hbody_safe)).
  - intros token body Hbody IHbody.
    unfold ComputedFirstFuelProperty in *.
    intros fuel Hsafe.
    destruct fuel as [| fuel].
    + simpl in Hsafe. discriminate.
    + simpl in Hsafe.
      apply andb_true_iff in Hsafe as [_ Hbody_safe].
      exact
        (computed_first_repetition_result_lift
          token fuel body (IHbody fuel Hbody_safe)).
  - intros token item rest Hitem IHitem.
    unfold ComputedFirstSequenceFuelProperty in *.
    intros fuel Hsafe.
    simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    destruct (IHitem fuel Hitem_safe)
      as [item_first [Hitem_first Hitem_mem]].
    destruct (choice_safe_nullable_defined fuel item Hitem_safe)
      as [item_nullable Hitem_nullable].
    assert (Hrest_expr_safe :
      choice_bodies_nonnullable_fuel (S fuel) (ESequence rest) = true).
    { simpl. exact Hrest_safe. }
    destruct (choice_safe_first_defined
      (S fuel) (ESequence rest) Hrest_expr_safe)
      as [rest_first Hrest_first].
    simpl in Hrest_first.
    simpl.
    rewrite Hitem_first, Hitem_nullable.
    destruct item_nullable.
    + rewrite Hrest_first.
      exists (token_union item_first rest_first). split.
      * reflexivity.
      * apply token_mem_union_left. exact Hitem_mem.
    + exists item_first. split; [reflexivity | exact Hitem_mem].
  - intros token item rest Hnullable Hrest IHrest.
    unfold ComputedFirstSequenceFuelProperty in *.
    intros fuel Hsafe.
    simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hitem_safe Hrest_safe].
    pose proof
      (choice_safe_implies_nullable_depth_safe
        fuel item Hitem_safe)
      as Hitem_depth_safe.
    pose proof
      (computed_nullable_sem_sound
        fuel item Hnullable Hitem_depth_safe)
      as Hitem_nullable.
    destruct (choice_safe_first_defined fuel item Hitem_safe)
      as [item_first Hitem_first].
    destruct (IHrest fuel Hrest_safe)
      as [rest_first [Hrest_first Hrest_mem]].
    simpl in Hrest_first.
    simpl.
    rewrite Hitem_first, Hitem_nullable, Hrest_first.
    exists (token_union item_first rest_first). split.
    + reflexivity.
    + apply token_mem_union_right. exact Hrest_mem.
  - intros token item rest Hitem IHitem.
    unfold ComputedFirstAlternativeFuelProperty in *.
    intros fuel Hsafe.
    simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
    apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
    destruct (IHitem fuel Hitem_safe)
      as [item_first [Hitem_first Hitem_mem]].
    assert (Hrest_expr_safe :
      choice_bodies_nonnullable_fuel (S fuel) (EAlternative rest) = true).
    { simpl. exact Hrest_safe. }
    destruct (choice_safe_first_defined
      (S fuel) (EAlternative rest) Hrest_expr_safe)
      as [rest_first Hrest_first].
    simpl in Hrest_first.
    simpl.
    rewrite Hitem_first, Hrest_first.
    exists (token_union item_first rest_first). split.
    + reflexivity.
    + apply token_mem_union_left. exact Hitem_mem.
  - intros token item rest Hrest IHrest.
    unfold ComputedFirstAlternativeFuelProperty in *.
    intros fuel Hsafe.
    simpl in Hsafe.
    apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
    apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
    destruct (choice_safe_first_defined fuel item Hitem_safe)
      as [item_first Hitem_first].
    destruct (IHrest fuel Hrest_safe)
      as [rest_first [Hrest_first Hrest_mem]].
    simpl in Hrest_first.
    simpl.
    rewrite Hitem_first, Hrest_first.
    exists (token_union item_first rest_first). split.
    + reflexivity.
    + apply token_mem_union_right. exact Hrest_mem.
Qed.

Theorem computed_first_sem_sound :
  forall token fuel expression,
    ComputedFirstSem token expression ->
    choice_bodies_nonnullable_fuel fuel expression = true ->
    exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel expression Hsem Hsafe.
  exact
    (proj1 computed_first_sem_sound_mutual
      token expression Hsem fuel Hsafe).
Qed.
'''

source = source[:block_start] + replacement + source[theorem_end:]
path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
