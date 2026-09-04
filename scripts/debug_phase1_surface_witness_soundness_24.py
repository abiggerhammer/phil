from pathlib import Path


script23 = Path("scripts/debug_phase1_surface_witness_soundness_23.py").read_text()
exec(compile(script23, "<debug23>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()
mutual_start = source.index("Theorem computed_first_sem_sound_mutual :")
mutual_end = source.index("\nTheorem computed_first_sem_sound :", mutual_start)
block = source[mutual_start:mutual_end]

old_header = '''Theorem computed_first_sem_sound_mutual :
  (forall token expression witness,
    ComputedFirstFuelProperty token expression witness) /\\
  (forall token items witness,
    ComputedFirstSequenceFuelProperty token items witness) /\\
  (forall token items witness,
    ComputedFirstAlternativeFuelProperty token items witness).
Proof.
  apply ComputedFirst_mutind.
'''
new_header = '''Theorem computed_first_sem_sound_mutual :
  forall token,
    (forall expression witness,
      ComputedFirstFuelProperty token expression witness) /\\
    (forall items witness,
      ComputedFirstSequenceFuelProperty token items witness) /\\
    (forall items witness,
      ComputedFirstAlternativeFuelProperty token items witness).
Proof.
  intro token.
  apply ComputedFirst_mutind.
'''

if old_header not in block:
    raise SystemExit("mutual theorem header did not match Debug 23 output")
block = block.replace(old_header, new_header, 1)
block = block.replace("  - intros token ", "  - intros ")
source = source[:mutual_start] + block + source[mutual_end:]

old_projection = '''  exact
    (proj1 computed_first_sem_sound_mutual
      token expression Hsem fuel Hsafe).'''
new_projection = '''  exact
    (proj1 (computed_first_sem_sound_mutual token)
      expression Hsem fuel Hsafe).'''
if old_projection not in source:
    raise SystemExit("final semantic soundness projection did not match")
source = source.replace(old_projection, new_projection, 1)

path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
