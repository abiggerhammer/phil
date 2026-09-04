from pathlib import Path


script25 = Path("scripts/debug_phase1_surface_witness_soundness_25.py").read_text()
exec(compile(script25, "<debug25>", "exec"), {})

path = Path("proof/Phil/Surface/GrammarDeterminacyWitnessSoundness.v")
source = path.read_text()

replacements = [
    ('''Definition ComputedFirstFuelProperty
  (token : OverlapToken) (expression : EbnfExpression)
  (_ : ComputedFirstSem token expression) : Prop :=''',
     '''Definition ComputedFirstFuelProperty
  (token : OverlapToken) (expression : EbnfExpression) : Prop :='''),
    ('''Definition ComputedFirstSequenceFuelProperty
  (token : OverlapToken) (items : list EbnfExpression)
  (_ : ComputedFirstSequenceSem token items) : Prop :=''',
     '''Definition ComputedFirstSequenceFuelProperty
  (token : OverlapToken) (items : list EbnfExpression) : Prop :='''),
    ('''Definition ComputedFirstAlternativeFuelProperty
  (token : OverlapToken) (items : list EbnfExpression)
  (_ : ComputedFirstAlternativeSem token items) : Prop :=''',
     '''Definition ComputedFirstAlternativeFuelProperty
  (token : OverlapToken) (items : list EbnfExpression) : Prop :='''),

    ('''Lemma computed_first_literal_fuel_case :
  forall token literal
    (witness : ComputedFirstSem token (ELiteral literal)),
    token = OverlapLiteral literal ->
    ComputedFirstFuelProperty token (ELiteral literal) witness.
Proof.
  intros token literal witness Htoken.''',
     '''Lemma computed_first_literal_fuel_case :
  forall token literal,
    token = OverlapLiteral literal ->
    ComputedFirstFuelProperty token (ELiteral literal).
Proof.
  intros token literal Htoken.'''),
    ('''Lemma computed_first_lexical_fuel_case :
  forall token class_name
    (witness : ComputedFirstSem token (ELexicalClass class_name)),
    token = OverlapLexicalClass class_name ->
    ComputedFirstFuelProperty token (ELexicalClass class_name) witness.
Proof.
  intros token class_name witness Htoken.''',
     '''Lemma computed_first_lexical_fuel_case :
  forall token class_name,
    token = OverlapLexicalClass class_name ->
    ComputedFirstFuelProperty token (ELexicalClass class_name).
Proof.
  intros token class_name Htoken.'''),
    ('''Lemma computed_first_nonterminal_fuel_case :
  forall token name
    (witness : ComputedFirstSem token (ENonterminal name)),
    token_mem token
      (lookup_tokens name phase1_surface_first_facts) = true ->
    ComputedFirstFuelProperty token (ENonterminal name) witness.
Proof.
  intros token name witness Hmem.''',
     '''Lemma computed_first_nonterminal_fuel_case :
  forall token name,
    token_mem token
      (lookup_tokens name phase1_surface_first_facts) = true ->
    ComputedFirstFuelProperty token (ENonterminal name).
Proof.
  intros token name Hmem.'''),
    ('''Lemma computed_first_sequence_expression_fuel_case :
  forall token items
    (expression_witness : ComputedFirstSem token (ESequence items))
    (items_witness : ComputedFirstSequenceSem token items),
    ComputedFirstSequenceFuelProperty token items items_witness ->
    ComputedFirstFuelProperty token (ESequence items) expression_witness.
Proof.
  intros token items expression_witness items_witness IHitems.''',
     '''Lemma computed_first_sequence_expression_fuel_case :
  forall token items,
    ComputedFirstSequenceFuelProperty token items ->
    ComputedFirstFuelProperty token (ESequence items).
Proof.
  intros token items IHitems.'''),
    ('''Lemma computed_first_alternative_expression_fuel_case :
  forall token items
    (expression_witness : ComputedFirstSem token (EAlternative items))
    (items_witness : ComputedFirstAlternativeSem token items),
    ComputedFirstAlternativeFuelProperty token items items_witness ->
    ComputedFirstFuelProperty token (EAlternative items) expression_witness.
Proof.
  intros token items expression_witness items_witness IHitems.''',
     '''Lemma computed_first_alternative_expression_fuel_case :
  forall token items,
    ComputedFirstAlternativeFuelProperty token items ->
    ComputedFirstFuelProperty token (EAlternative items).
Proof.
  intros token items IHitems.'''),
    ('''Lemma computed_first_optional_fuel_case :
  forall token body
    (expression_witness : ComputedFirstSem token (EOptional body))
    (body_witness : ComputedFirstSem token body),
    ComputedFirstFuelProperty token body body_witness ->
    ComputedFirstFuelProperty token (EOptional body) expression_witness.
Proof.
  intros token body expression_witness body_witness IHbody.''',
     '''Lemma computed_first_optional_fuel_case :
  forall token body,
    ComputedFirstFuelProperty token body ->
    ComputedFirstFuelProperty token (EOptional body).
Proof.
  intros token body IHbody.'''),
    ('''Lemma computed_first_repetition_fuel_case :
  forall token body
    (expression_witness : ComputedFirstSem token (ERepetition body))
    (body_witness : ComputedFirstSem token body),
    ComputedFirstFuelProperty token body body_witness ->
    ComputedFirstFuelProperty token (ERepetition body) expression_witness.
Proof.
  intros token body expression_witness body_witness IHbody.''',
     '''Lemma computed_first_repetition_fuel_case :
  forall token body,
    ComputedFirstFuelProperty token body ->
    ComputedFirstFuelProperty token (ERepetition body).
Proof.
  intros token body IHbody.'''),
    ('''Lemma computed_first_sequence_here_fuel_case :
  forall token item rest
    (sequence_witness : ComputedFirstSequenceSem token (item :: rest))
    (item_witness : ComputedFirstSem token item),
    ComputedFirstFuelProperty token item item_witness ->
    ComputedFirstSequenceFuelProperty token (item :: rest) sequence_witness.
Proof.
  intros token item rest sequence_witness item_witness IHitem.''',
     '''Lemma computed_first_sequence_here_fuel_case :
  forall token item rest,
    ComputedFirstFuelProperty token item ->
    ComputedFirstSequenceFuelProperty token (item :: rest).
Proof.
  intros token item rest IHitem.'''),
    ('''Lemma computed_first_sequence_later_fuel_case :
  forall token item rest
    (sequence_witness : ComputedFirstSequenceSem token (item :: rest))
    (Hnullable : ComputedNullableSem item)
    (rest_witness : ComputedFirstSequenceSem token rest),
    ComputedFirstSequenceFuelProperty token rest rest_witness ->
    ComputedFirstSequenceFuelProperty token (item :: rest) sequence_witness.
Proof.
  intros token item rest sequence_witness Hnullable rest_witness IHrest.''',
     '''Lemma computed_first_sequence_later_fuel_case :
  forall token item rest,
    ComputedNullableSem item ->
    ComputedFirstSequenceFuelProperty token rest ->
    ComputedFirstSequenceFuelProperty token (item :: rest).
Proof.
  intros token item rest Hnullable IHrest.'''),
    ('''Lemma computed_first_alternative_here_fuel_case :
  forall token item rest
    (alternative_witness : ComputedFirstAlternativeSem token (item :: rest))
    (item_witness : ComputedFirstSem token item),
    ComputedFirstFuelProperty token item item_witness ->
    ComputedFirstAlternativeFuelProperty
      token (item :: rest) alternative_witness.
Proof.
  intros token item rest alternative_witness item_witness IHitem.''',
     '''Lemma computed_first_alternative_here_fuel_case :
  forall token item rest,
    ComputedFirstFuelProperty token item ->
    ComputedFirstAlternativeFuelProperty token (item :: rest).
Proof.
  intros token item rest IHitem.'''),
    ('''Lemma computed_first_alternative_later_fuel_case :
  forall token item rest
    (alternative_witness : ComputedFirstAlternativeSem token (item :: rest))
    (rest_witness : ComputedFirstAlternativeSem token rest),
    ComputedFirstAlternativeFuelProperty token rest rest_witness ->
    ComputedFirstAlternativeFuelProperty
      token (item :: rest) alternative_witness.
Proof.
  intros token item rest alternative_witness rest_witness IHrest.''',
     '''Lemma computed_first_alternative_later_fuel_case :
  forall token item rest,
    ComputedFirstAlternativeFuelProperty token rest ->
    ComputedFirstAlternativeFuelProperty token (item :: rest).
Proof.
  intros token item rest IHrest.'''),

    ("ComputedFirstFuelProperty token expression witness", "ComputedFirstFuelProperty token expression"),
    ("ComputedFirstSequenceFuelProperty token items witness", "ComputedFirstSequenceFuelProperty token items"),
    ("ComputedFirstAlternativeFuelProperty token items witness", "ComputedFirstAlternativeFuelProperty token items"),
]

for old, new in replacements:
    if old not in source:
        raise SystemExit(f"Debug 27 replacement did not match:\n{old[:120]}")
    source = source.replace(old, new)

# All remaining proof-indexed applications should now be gone. These catches cover
# any signature occurrence not already consumed by the larger replacements.
for old, new in [
    ("ComputedFirstFuelProperty token body body_witness", "ComputedFirstFuelProperty token body"),
    ("ComputedFirstFuelProperty token (EOptional body) expression_witness", "ComputedFirstFuelProperty token (EOptional body)"),
    ("ComputedFirstFuelProperty token (ERepetition body) expression_witness", "ComputedFirstFuelProperty token (ERepetition body)"),
    ("ComputedFirstFuelProperty token item item_witness", "ComputedFirstFuelProperty token item"),
    ("ComputedFirstSequenceFuelProperty token items items_witness", "ComputedFirstSequenceFuelProperty token items"),
    ("ComputedFirstSequenceFuelProperty token (item :: rest) sequence_witness", "ComputedFirstSequenceFuelProperty token (item :: rest)"),
    ("ComputedFirstSequenceFuelProperty token rest rest_witness", "ComputedFirstSequenceFuelProperty token rest"),
    ("ComputedFirstAlternativeFuelProperty token items items_witness", "ComputedFirstAlternativeFuelProperty token items"),
    ("ComputedFirstAlternativeFuelProperty token (item :: rest) alternative_witness", "ComputedFirstAlternativeFuelProperty token (item :: rest)"),
    ("ComputedFirstAlternativeFuelProperty token rest rest_witness", "ComputedFirstAlternativeFuelProperty token rest"),
    ("ComputedFirstFuelProperty token (ESequence items) expression_witness", "ComputedFirstFuelProperty token (ESequence items)"),
    ("ComputedFirstFuelProperty token (EAlternative items) expression_witness", "ComputedFirstFuelProperty token (EAlternative items)"),
    ("ComputedFirstFuelProperty token (ELiteral literal) witness", "ComputedFirstFuelProperty token (ELiteral literal)"),
    ("ComputedFirstFuelProperty token (ELexicalClass class_name) witness", "ComputedFirstFuelProperty token (ELexicalClass class_name)"),
    ("ComputedFirstFuelProperty token (ENonterminal name) witness", "ComputedFirstFuelProperty token (ENonterminal name)"),
]:
    source = source.replace(old, new)

# Keep the branch lemmas sealed before building the combined induction theorem.
theorem_start = source.index("Theorem computed_first_sem_sound_mutual :")
source = (
    source[:theorem_start]
    + "Opaque ComputedFirstFuelProperty\n"
      "  ComputedFirstSequenceFuelProperty\n"
      "  ComputedFirstAlternativeFuelProperty.\n\n"
    + source[theorem_start:]
)

path.write_text(source)
print(f"generated witness proof characters: {len(source)}")
