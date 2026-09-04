from pathlib import Path


script27 = Path("scripts/debug_phase1_surface_witness_soundness_27.py").read_text()
exec(compile(script27, "<debug27>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()

optional_start = source.index("Lemma computed_first_optional_fuel_case :")
repetition_start = source.index("Lemma computed_first_repetition_fuel_case :", optional_start)
sequence_here_start = source.index("Lemma computed_first_sequence_here_fuel_case :", repetition_start)

adapters_and_optional = r'''Lemma computed_first_fuel_property_intro :
  forall token expression,
    (forall fuel,
      choice_bodies_nonnullable_fuel fuel expression = true ->
      exists tokens,
        first_expression_fuel
          fuel
          phase1_surface_nullable_facts
          phase1_surface_first_facts
          expression = Some tokens /\
        token_mem token tokens = true) ->
    ComputedFirstFuelProperty token expression.
Proof.
  intros token expression Hproperty.
  unfold ComputedFirstFuelProperty.
  exact Hproperty.
Qed.

Lemma computed_first_fuel_property_result :
  forall token expression fuel,
    ComputedFirstFuelProperty token expression ->
    choice_bodies_nonnullable_fuel fuel expression = true ->
    exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token expression fuel Hproperty Hsafe.
  unfold ComputedFirstFuelProperty in Hproperty.
  exact (Hproperty fuel Hsafe).
Qed.

Lemma computed_first_optional_zero_not_safe :
  forall body,
    choice_bodies_nonnullable_fuel 0 (EOptional body) = true -> False.
Proof.
  intros body Hsafe.
  simpl in Hsafe.
  discriminate.
Qed.

Lemma computed_first_optional_body_safe :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (EOptional body) = true ->
    choice_bodies_nonnullable_fuel fuel body = true.
Proof.
  intros fuel body Hsafe.
  simpl in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  exact Hbody_safe.
Qed.

Opaque ComputedFirstFuelProperty.

Lemma computed_first_optional_fuel_case :
  forall token body,
    ComputedFirstFuelProperty token body ->
    ComputedFirstFuelProperty token (EOptional body).
Proof.
  intros token body IHbody.
  apply computed_first_fuel_property_intro.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - exfalso.
    exact (computed_first_optional_zero_not_safe body Hsafe).
  - exact
      (computed_first_optional_result_lift
        token fuel body
        (computed_first_fuel_property_result
          token body fuel IHbody
          (computed_first_optional_body_safe fuel body Hsafe))).
Qed.

'''

repetition = r'''Lemma computed_first_repetition_zero_not_safe :
  forall body,
    choice_bodies_nonnullable_fuel 0 (ERepetition body) = true -> False.
Proof.
  intros body Hsafe.
  simpl in Hsafe.
  discriminate.
Qed.

Lemma computed_first_repetition_body_safe :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (ERepetition body) = true ->
    choice_bodies_nonnullable_fuel fuel body = true.
Proof.
  intros fuel body Hsafe.
  simpl in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  exact Hbody_safe.
Qed.

Lemma computed_first_repetition_fuel_case :
  forall token body,
    ComputedFirstFuelProperty token body ->
    ComputedFirstFuelProperty token (ERepetition body).
Proof.
  intros token body IHbody.
  apply computed_first_fuel_property_intro.
  intros fuel Hsafe.
  destruct fuel as [| fuel].
  - exfalso.
    exact (computed_first_repetition_zero_not_safe body Hsafe).
  - exact
      (computed_first_repetition_result_lift
        token fuel body
        (computed_first_fuel_property_result
          token body fuel IHbody
          (computed_first_repetition_body_safe fuel body Hsafe))).
Qed.

Transparent ComputedFirstFuelProperty.

'''

source = (
    source[:optional_start]
    + adapters_and_optional
    + repetition
    + source[sequence_here_start:]
)

path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
