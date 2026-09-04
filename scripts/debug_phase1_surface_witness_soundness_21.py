from pathlib import Path


history = Path(".github/debug-workflow-history")
workflow = (
    history / "phase1-surface-determinacy-witness-soundness-debug20.yml"
).read_text()

marker = workflow.index("- name: Apply abstracted FIRST step diagnostic")
start = workflow.index("          from pathlib import Path", marker)
end = workflow.index("\n          PY", start)
raw_code = workflow[start:end]
prefix = "          "
code = "\n".join(
    line[len(prefix) :] if line.startswith(prefix) else line
    for line in raw_code.splitlines()
)
exec(compile(code, "<existing-debug20-diagnostics>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()
step_start = source.index("Lemma computed_first_sem_sound_step :")

helpers = r'''Lemma computed_first_optional_result_lift :
  forall token fuel body,
    (exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        body = Some tokens /\
      token_mem token tokens = true) ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (EOptional body) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel body [tokens [Hfirst Hmem]].
  exists tokens. split.
  - simpl. exact Hfirst.
  - exact Hmem.
Qed.

Lemma computed_first_repetition_result_lift :
  forall token fuel body,
    (exists tokens,
      first_expression_fuel
        fuel
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        body = Some tokens /\
      token_mem token tokens = true) ->
    exists tokens,
      first_expression_fuel
        (S fuel)
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        (ERepetition body) = Some tokens /\
      token_mem token tokens = true.
Proof.
  intros token fuel body [tokens [Hfirst Hmem]].
  exists tokens. split.
  - simpl. exact Hfirst.
  - exact Hmem.
Qed.

'''
source = source[:step_start] + helpers + source[step_start:]

old = '''  - abstract (
      simpl in Hsafe;
      apply andb_true_iff in Hsafe as [_ Hbody_safe];
      exact (IH body Hbody Hbody_safe)).'''
optional = '''  - abstract (
      simpl in Hsafe;
      apply andb_true_iff in Hsafe as [_ Hbody_safe];
      exact
        (computed_first_optional_result_lift
          token fuel body (IH body Hbody Hbody_safe))).'''
repetition = '''  - abstract (
      simpl in Hsafe;
      apply andb_true_iff in Hsafe as [_ Hbody_safe];
      exact
        (computed_first_repetition_result_lift
          token fuel body (IH body Hbody Hbody_safe))).'''

if source.count(old) < 2:
    raise SystemExit("expected two unary FIRST branches")
source = source.replace(old, optional, 1)
source = source.replace(old, repetition, 1)
path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
