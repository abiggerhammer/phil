from pathlib import Path


script25 = Path("scripts/debug_phase1_surface_witness_soundness_25.py").read_text()
exec(compile(script25, "<debug25>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()

optional_start = source.index("Lemma computed_first_optional_fuel_case :")
repetition_start = source.index("Lemma computed_first_repetition_fuel_case :", optional_start)
sequence_here_start = source.index("Lemma computed_first_sequence_here_fuel_case :", repetition_start)

accessor_and_optional = r'''Lemma computed_first_fuel_property_result :
  forall token expression
    (witness : ComputedFirstSem token expression) fuel,
    ComputedFirstFuelProperty token expression witness ->
    choice_bodies_nonnullable_fuel fuel expression = true ->
    exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token expression witness fuel Hproperty Hsafe.
  unfold ComputedFirstFuelProperty in Hproperty.
  exact (Hproperty fuel Hsafe).
Qed.

Lemma computed_first_optional_fuel_case :
  forall token body
    (expression_witness : ComputedFirstSem token (EOptional body))
    (body_witness : ComputedFirstSem token body),
    ComputedFirstFuelProperty token body body_witness ->
    ComputedFirstFuelProperty token (EOptional body) expression_witness.
Proof.
  intros token body expression_witness body_witness IHbody.
  unfold ComputedFirstFuelProperty.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [_ Hbody_safe].
    pose proof
      (computed_first_fuel_property_result
        token body body_witness fuel IHbody Hbody_safe)
      as Hbody_result.
    exact
      (computed_first_optional_result_lift
        token fuel body Hbody_result).
Qed.

'''

repetition = r'''Lemma computed_first_repetition_fuel_case :
  forall token body
    (expression_witness : ComputedFirstSem token (ERepetition body))
    (body_witness : ComputedFirstSem token body),
    ComputedFirstFuelProperty token body body_witness ->
    ComputedFirstFuelProperty token (ERepetition body) expression_witness.
Proof.
  intros token body expression_witness body_witness IHbody.
  unfold ComputedFirstFuelProperty.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - simpl in Hsafe. discriminate.
  - simpl in Hsafe.
    apply andb_true_iff in Hsafe as [_ Hbody_safe].
    pose proof
      (computed_first_fuel_property_result
        token body body_witness fuel IHbody Hbody_safe)
      as Hbody_result.
    exact
      (computed_first_repetition_result_lift
        token fuel body Hbody_result).
Qed.

'''

source = source[:optional_start] + accessor_and_optional + repetition + source[sequence_here_start:]

theorem_start = source.index("Theorem computed_first_sem_sound_mutual :")
source = (
    source[:theorem_start]
    + "Opaque ComputedFirstFuelProperty\n"
      "  ComputedFirstSequenceFuelProperty\n"
      "  ComputedFirstAlternativeFuelProperty.\n\n"
    + source[theorem_start:]
)

old_projection = '''  exact
    (proj1 (computed_first_sem_sound_mutual token)
      expression Hsem fuel Hsafe).'''
new_projection = '''  exact
    (computed_first_fuel_property_result
      token expression Hsem fuel
      (proj1 (computed_first_sem_sound_mutual token)
        expression Hsem)
      Hsafe).'''
if old_projection not in source:
    raise SystemExit("final semantic soundness projection did not match Debug 25 output")
source = source.replace(old_projection, new_projection, 1)

path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
