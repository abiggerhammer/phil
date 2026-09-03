from pathlib import Path


script28 = Path("scripts/debug_phase1_surface_witness_soundness_28.py").read_text()
exec(compile(script28, "<debug28>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()

old_optional = r'''Lemma computed_first_optional_body_safe :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (EOptional body) = true ->
    choice_bodies_nonnullable_fuel fuel body = true.
Proof.
  intros fuel body Hsafe.
  simpl in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  exact Hbody_safe.
Qed.
'''
new_optional = r'''Lemma choice_bodies_nonnullable_optional_step :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (EOptional body) =
    andb
      (negb (nullable_expression phase1_surface_nullable_facts body))
      (choice_bodies_nonnullable_fuel fuel body).
Proof.
  reflexivity.
Qed.

Lemma computed_first_optional_body_safe :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (EOptional body) = true ->
    choice_bodies_nonnullable_fuel fuel body = true.
Proof.
  intros fuel body Hsafe.
  rewrite choice_bodies_nonnullable_optional_step in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  exact Hbody_safe.
Qed.
'''
if old_optional not in source:
    raise SystemExit("Debug 29 optional body-safe block did not match Debug 28 output")
source = source.replace(old_optional, new_optional, 1)

old_repetition = r'''Lemma computed_first_repetition_body_safe :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (ERepetition body) = true ->
    choice_bodies_nonnullable_fuel fuel body = true.
Proof.
  intros fuel body Hsafe.
  simpl in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  exact Hbody_safe.
Qed.
'''
new_repetition = r'''Lemma choice_bodies_nonnullable_repetition_step :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (ERepetition body) =
    andb
      (negb (nullable_expression phase1_surface_nullable_facts body))
      (choice_bodies_nonnullable_fuel fuel body).
Proof.
  reflexivity.
Qed.

Lemma computed_first_repetition_body_safe :
  forall fuel body,
    choice_bodies_nonnullable_fuel (S fuel) (ERepetition body) = true ->
    choice_bodies_nonnullable_fuel fuel body = true.
Proof.
  intros fuel body Hsafe.
  rewrite choice_bodies_nonnullable_repetition_step in Hsafe.
  apply andb_true_iff in Hsafe as [_ Hbody_safe].
  exact Hbody_safe.
Qed.
'''
if old_repetition not in source:
    raise SystemExit("Debug 29 repetition body-safe block did not match Debug 28 output")
source = source.replace(old_repetition, new_repetition, 1)

path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
