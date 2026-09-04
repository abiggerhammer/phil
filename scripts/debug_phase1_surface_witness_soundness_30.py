from pathlib import Path


script29 = Path("scripts/debug_phase1_surface_witness_soundness_29.py").read_text()
exec(compile(script29, "<debug29>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()

alternative_here_start = source.index("Lemma computed_first_alternative_here_fuel_case :")
mutual_start = source.index("Theorem computed_first_sem_sound_mutual :", alternative_here_start)

replacement = r'''Lemma computed_first_forallb_cons_step :
  forall (A : Type) (predicate : A -> bool) item rest,
    forallb predicate (item :: rest) =
    andb (predicate item) (forallb predicate rest).
Proof.
  reflexivity.
Qed.

Lemma choice_bodies_nonnullable_alternative_step :
  forall fuel items,
    choice_bodies_nonnullable_fuel (S fuel) (EAlternative items) =
    forallb
      (fun item =>
        andb
          (negb
            (nullable_expression phase1_surface_nullable_facts item))
          (choice_bodies_nonnullable_fuel fuel item))
      items.
Proof.
  reflexivity.
Qed.

Lemma computed_first_alternative_here_fuel_case :
  forall token item rest,
    ComputedFirstFuelProperty token item ->
    ComputedFirstAlternativeFuelProperty token (item :: rest).
Proof.
  intros token item rest IHitem.
  unfold ComputedFirstAlternativeFuelProperty.
  intros fuel Hsafe.
  rewrite computed_first_forallb_cons_step in Hsafe.
  apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
  apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
  destruct (IHitem fuel Hitem_safe)
    as [item_first [Hitem_first Hitem_mem]].
  assert (Hrest_expr_safe :
    choice_bodies_nonnullable_fuel (S fuel) (EAlternative rest) = true).
  {
    rewrite choice_bodies_nonnullable_alternative_step.
    exact Hrest_safe.
  }
  destruct
    (choice_safe_first_defined
      (S fuel) (EAlternative rest) Hrest_expr_safe)
    as [rest_first Hrest_first].
  exact
    (computed_first_alternative_here_from_results
      token fuel item rest item_first rest_first
      Hitem_first Hitem_mem Hrest_first).
Qed.

Lemma computed_first_alternative_later_fuel_case :
  forall token item rest,
    ComputedFirstAlternativeFuelProperty token rest ->
    ComputedFirstAlternativeFuelProperty token (item :: rest).
Proof.
  intros token item rest IHrest.
  unfold ComputedFirstAlternativeFuelProperty.
  intros fuel Hsafe.
  rewrite computed_first_forallb_cons_step in Hsafe.
  apply andb_true_iff in Hsafe as [Hhead_safe Hrest_safe].
  apply andb_true_iff in Hhead_safe as [_ Hitem_safe].
  destruct (choice_safe_first_defined fuel item Hitem_safe)
    as [item_first Hitem_first].
  destruct (IHrest fuel Hrest_safe)
    as [rest_first [Hrest_first Hrest_mem]].
  exact
    (computed_first_alternative_later_from_results
      token fuel item rest item_first rest_first
      Hitem_first Hrest_first Hrest_mem).
Qed.

'''

source = source[:alternative_here_start] + replacement + source[mutual_start:]
path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
