from pathlib import Path


script24 = Path("scripts/debug_phase1_surface_witness_soundness_24.py").read_text()
exec(compile(script24, "<debug24>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()
mutual_start = source.index("Theorem computed_first_sem_sound_mutual :")
mutual_end = source.index("\nTheorem computed_first_sem_sound :", mutual_start)

helpers = r'''Lemma computed_first_literal_fuel_case :
  forall token literal
    (witness : ComputedFirstSem token (ELiteral literal)),
    token = OverlapLiteral literal ->
    ComputedFirstFuelProperty token (ELiteral literal) witness.
Proof.
  intros token literal witness Htoken.
  unfold ComputedFirstFuelProperty.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - subst token.
    exists [OverlapLiteral literal]. split.
    + reflexivity.
    + unfold token_mem.
      rewrite overlap_token_eqb_refl.
      reflexivity.
Qed.

Lemma computed_first_lexical_fuel_case :
  forall token class_name
    (witness : ComputedFirstSem token (ELexicalClass class_name)),
    token = OverlapLexicalClass class_name ->
    ComputedFirstFuelProperty token (ELexicalClass class_name) witness.
Proof.
  intros token class_name witness Htoken.
  unfold ComputedFirstFuelProperty.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - subst token.
    exists [OverlapLexicalClass class_name]. split.
    + reflexivity.
    + unfold token_mem.
      rewrite overlap_token_eqb_refl.
      reflexivity.
Qed.

Lemma computed_first_nonterminal_fuel_case :
  forall token name
    (witness : ComputedFirstSem token (ENonterminal name)),
    token_mem token
      (lookup_tokens name phase1_surface_first_facts) = true ->
    ComputedFirstFuelProperty token (ENonterminal name) witness.
Proof.
  intros token name witness Hmem.
  unfold ComputedFirstFuelProperty.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - exists (lookup_tokens name phase1_surface_first_facts). split.
    + reflexivity.
    + exact Hmem.
Qed.

Lemma computed_first_sequence_expression_fuel_case :
  forall token items
    (expression_witness : ComputedFirstSem token (ESequence items))
    (items_witness : ComputedFirstSequenceSem token items),
    ComputedFirstSequenceFuelProperty token items items_witness ->
    ComputedFirstFuelProperty token (ESequence items) expression_witness.
Proof.
  intros token items expression_witness items_witness IHitems.
  unfold ComputedFirstFuelProperty, ComputedFirstSequenceFuelProperty in *.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - simpl in Hsafe.
    exact (IHitems fuel Hsafe).
Qed.

Lemma computed_first_alternative_expression_fuel_case :
  forall token items
    (expression_witness : ComputedFirstSem token (EAlternative items))
    (items_witness : ComputedFirstAlternativeSem token items),
    ComputedFirstAlternativeFuelProperty token items items_witness ->
    ComputedFirstFuelProperty token (EAlternative items) expression_witness.
Proof.
  intros token items expression_witness items_witness IHitems.
  unfold ComputedFirstFuelProperty, ComputedFirstAlternativeFuelProperty in *.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - simpl in Hsafe.
    exact (IHitems fuel Hsafe).
Qed.

Lemma computed_first_optional_fuel_case :
  forall token body
    (expression_witness : ComputedFirstSem token (EOptional body))
    (body_witness : ComputedFirstSem token body),
    ComputedFirstFuelProperty token body body_witness ->
    ComputedFirstFuelProperty token (EOptional body) expression_witness.
Proof.
  intros token body expression_witness body_witness IHbody.
  unfold ComputedFirstFuelProperty in *.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [_ Hbody_safe].
    exact
      (computed_first_optional_result_lift
        token fuel body (IHbody fuel Hbody_safe)).
Qed.

Lemma computed_first_repetition_fuel_case :
  forall token body
    (expression_witness : ComputedFirstSem token (ERepetition body))
    (body_witness : ComputedFirstSem token body),
    ComputedFirstFuelProperty token body body_witness ->
    ComputedFirstFuelProperty token (ERepetition body) expression_witness.
Proof.
  intros token body expression_witness body_witness IHbody.
  unfold ComputedFirstFuelProperty in *.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [_ Hbody_safe].
    exact
      (computed_first_repetition_result_lift
        token fuel body (IHbody fuel Hbody_safe)).
Qed.

Lemma computed_first_sequence_here_fuel_case :
  forall token item rest
    (sequence_witness : ComputedFirstSequenceSem token (item :: rest))
    (item_witness : ComputedFirstSem token item),
    ComputedFirstFuelProperty token item item_witness ->
    ComputedFirstSequenceFuelProperty token (item :: rest) sequence_witness.
Proof.
  intros token item rest sequence_witness item_witness IHitem.
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
  - rewrite Hrest_first.
    exists (token_union item_first rest_first). split.
    + reflexivity.
    + apply token_mem_union_left. exact Hitem_mem.
  - exists item_first. split; [reflexivity | exact Hitem_mem].
Qed.

Lemma computed_first_sequence_later_fuel_case :
  forall token item rest
    (sequence_witness : ComputedFirstSequenceSem token (item :: rest))
    (Hnullable : ComputedNullableSem item)
    (rest_witness : ComputedFirstSequenceSem token rest),
    ComputedFirstSequenceFuelProperty token rest rest_witness ->
    ComputedFirstSequenceFuelProperty token (item :: rest) sequence_witness.
Proof.
  intros token item rest sequence_witness Hnullable rest_witness IHrest.
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
  - reflexivity.
  - apply token_mem_union_right. exact Hrest_mem.
Qed.

Lemma computed_first_alternative_here_fuel_case :
  forall token item rest
    (alternative_witness : ComputedFirstAlternativeSem token (item :: rest))
    (item_witness : ComputedFirstSem token item),
    ComputedFirstFuelProperty token item item_witness ->
    ComputedFirstAlternativeFuelProperty
      token (item :: rest) alternative_witness.
Proof.
  intros token item rest alternative_witness item_witness IHitem.
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
  - reflexivity.
  - apply token_mem_union_left. exact Hitem_mem.
Qed.

Lemma computed_first_alternative_later_fuel_case :
  forall token item rest
    (alternative_witness : ComputedFirstAlternativeSem token (item :: rest))
    (rest_witness : ComputedFirstAlternativeSem token rest),
    ComputedFirstAlternativeFuelProperty token rest rest_witness ->
    ComputedFirstAlternativeFuelProperty
      token (item :: rest) alternative_witness.
Proof.
  intros token item rest alternative_witness rest_witness IHrest.
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
  - reflexivity.
  - apply token_mem_union_right. exact Hrest_mem.
Qed.

'''

theorem = r'''Theorem computed_first_sem_sound_mutual :
  forall token,
    (forall expression witness,
      ComputedFirstFuelProperty token expression witness) /\
    (forall items witness,
      ComputedFirstSequenceFuelProperty token items witness) /\
    (forall items witness,
      ComputedFirstAlternativeFuelProperty token items witness).
Proof.
  intro token.
  apply ComputedFirst_mutind.
  - intros literal Htoken.
    eapply computed_first_literal_fuel_case.
    exact Htoken.
  - intros class_name Htoken.
    eapply computed_first_lexical_fuel_case.
    exact Htoken.
  - intros name Hmem.
    eapply computed_first_nonterminal_fuel_case.
    exact Hmem.
  - intros items Hitems IHitems.
    eapply computed_first_sequence_expression_fuel_case.
    exact IHitems.
  - intros items Hitems IHitems.
    eapply computed_first_alternative_expression_fuel_case.
    exact IHitems.
  - intros body Hbody IHbody.
    eapply computed_first_optional_fuel_case.
    exact IHbody.
  - intros body Hbody IHbody.
    eapply computed_first_repetition_fuel_case.
    exact IHbody.
  - intros item rest Hitem IHitem.
    eapply computed_first_sequence_here_fuel_case.
    exact IHitem.
  - intros item rest Hnullable Hrest IHrest.
    eapply computed_first_sequence_later_fuel_case.
    + exact Hnullable.
    + exact IHrest.
  - intros item rest Hitem IHitem.
    eapply computed_first_alternative_here_fuel_case.
    exact IHitem.
  - intros item rest Hrest IHrest.
    eapply computed_first_alternative_later_fuel_case.
    exact IHrest.
Qed.
'''

source = source[:mutual_start] + helpers + theorem + source[mutual_end:]
path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
