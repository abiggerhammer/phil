from pathlib import Path


script21 = Path("scripts/debug_phase1_surface_witness_soundness_21.py").read_text()
exec(compile(script21, "<debug21>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()
step_start = source.index("Lemma computed_first_sem_sound_step :")
step_end = source.index("\nTheorem computed_first_sem_sound :", step_start)

replacement = r'''Lemma computed_first_literal_sem_sound_case :
  forall token fuel literal,
    token = OverlapLiteral literal ->
    choice_bodies_nonnullable_fuel (S fuel) (ELiteral literal) = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ELiteral literal) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel literal Htoken Hsafe.
  subst token.
  exists [OverlapLiteral literal]. split.
  - reflexivity.
  - unfold token_mem.
    rewrite overlap_token_eqb_refl.
    reflexivity.
Qed.

Lemma computed_first_lexical_sem_sound_case :
  forall token fuel class_name,
    token = OverlapLexicalClass class_name ->
    choice_bodies_nonnullable_fuel (S fuel) (ELexicalClass class_name) = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ELexicalClass class_name) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel class_name Htoken Hsafe.
  subst token.
  exists [OverlapLexicalClass class_name]. split.
  - reflexivity.
  - unfold token_mem.
    rewrite overlap_token_eqb_refl.
    reflexivity.
Qed.

Lemma computed_first_nonterminal_sem_sound_case :
  forall token fuel name,
    token_mem token
      (lookup_tokens name phase1_surface_first_facts) = true ->
    choice_bodies_nonnullable_fuel (S fuel) (ENonterminal name) = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ENonterminal name) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel name Hmem Hsafe.
  exists (lookup_tokens name phase1_surface_first_facts). split.
  - reflexivity.
  - exact Hmem.
Qed.

Lemma computed_first_sequence_sem_sound_case :
  forall token fuel items,
    (forall expression,
      ComputedFirstSem token expression ->
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens /\
        token_mem token tokens = true) ->
    ComputedFirstSequenceSem token items ->
    choice_bodies_nonnullable_fuel (S fuel) (ESequence items) = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ESequence items) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel items IH Hitems Hsafe.
  simpl in Hsafe.
  exact
    (computed_first_sequence_sem_sound
      token fuel items IH Hitems Hsafe).
Qed.

Lemma computed_first_alternative_sem_sound_case :
  forall token fuel items,
    (forall expression,
      ComputedFirstSem token expression ->
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens /\
        token_mem token tokens = true) ->
    ComputedFirstAlternativeSem token items ->
    choice_bodies_nonnullable_fuel (S fuel) (EAlternative items) = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EAlternative items) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel items IH Hitems Hsafe.
  simpl in Hsafe.
  exact
    (computed_first_alternative_sem_sound
      token fuel items IH Hitems Hsafe).
Qed.

Lemma computed_first_optional_sem_sound_case :
  forall token fuel body,
    (forall expression,
      ComputedFirstSem token expression ->
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens /\
        token_mem token tokens = true) ->
    ComputedFirstSem token body ->
    choice_bodies_nonnullable_fuel (S fuel) (EOptional body) = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EOptional body) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel body IH Hbody Hsafe.
  simpl in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  exact
    (computed_first_optional_result_lift
      token fuel body (IH body Hbody Hbody_safe)).
Qed.

Lemma computed_first_repetition_sem_sound_case :
  forall token fuel body,
    (forall expression,
      ComputedFirstSem token expression ->
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens /\
        token_mem token tokens = true) ->
    ComputedFirstSem token body ->
    choice_bodies_nonnullable_fuel (S fuel) (ERepetition body) = true ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ERepetition body) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel body IH Hbody Hsafe.
  simpl in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  exact
    (computed_first_repetition_result_lift
      token fuel body (IH body Hbody Hbody_safe)).
Qed.

Lemma computed_first_sem_sound_step :
  forall token fuel,
    (forall expression,
      ComputedFirstSem token expression ->
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens /\
        token_mem token tokens = true) ->
    forall expression,
      ComputedFirstSem token expression ->
      choice_bodies_nonnullable_fuel (S fuel) expression = true ->
      exists tokens,
        first_expression_fuel
          (S fuel)
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens /\
        token_mem token tokens = true.
Proof.
  intros token fuel IH expression Hsem Hsafe.
  destruct Hsem as
    [literal Htoken
    | class_name Htoken
    | name Hmem
    | items Hitems
    | items Hitems
    | body Hbody
    | body Hbody].
  - exact
      (computed_first_literal_sem_sound_case
        token fuel literal Htoken Hsafe).
  - exact
      (computed_first_lexical_sem_sound_case
        token fuel class_name Htoken Hsafe).
  - exact
      (computed_first_nonterminal_sem_sound_case
        token fuel name Hmem Hsafe).
  - exact
      (computed_first_sequence_sem_sound_case
        token fuel items IH Hitems Hsafe).
  - exact
      (computed_first_alternative_sem_sound_case
        token fuel items IH Hitems Hsafe).
  - exact
      (computed_first_optional_sem_sound_case
        token fuel body IH Hbody Hsafe).
  - exact
      (computed_first_repetition_sem_sound_case
        token fuel body IH Hbody Hsafe).
Qed.
'''

source = source[:step_start] + replacement + source[step_end:]
path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
