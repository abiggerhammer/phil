From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDeterminacyCertificate.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic lookahead bridge for PHIL-SURFACE-DETERM-001.

  The predictive oracle from #582 consumes nullable/FIRST facts.  Before the
  final ordinary-derivation -> oracle-resolved theorem can use those facts, we
  need a proof that an actual ordinary derivation exposes the corresponding
  implementation-independent nullability/FIRST witness.

  This file deliberately stops one layer short of the computed fixed points:
  it proves (1) every derivation consumes a prefix, (2) a derivation that
  consumes nothing has a structural nullable witness, and (3) a derivation
  that consumes at least one token has a structural FIRST witness for its first
  concrete-token shape.  The successor lemma connects these witnesses to the
  checked #569 fixed points.
*)

Definition concrete_token_shape (token : ConcreteToken) : OverlapToken :=
  match token with
  | TLiteral literal => OverlapLiteral literal
  | TLexical class_name _ => OverlapLexicalClass class_name
  end.

Definition concrete_token_eq_dec :
  forall first second : ConcreteToken, {first = second} + {first <> second}.
Proof.
  decide equality; apply string_dec.
Defined.

Lemma prefix_compose :
  forall (input middle rest : list ConcreteToken) first second,
    input = List.app first middle ->
    middle = List.app second rest ->
    input = List.app (List.app first second) rest.
Proof.
  intros input middle rest first second Hfirst Hsecond.
  rewrite Hfirst, Hsecond.
  now rewrite List.app_assoc.
Qed.

Lemma prefix_antisymmetric :
  forall (first second : list ConcreteToken),
    (exists prefix, first = List.app prefix second) ->
    (exists prefix, second = List.app prefix first) ->
    first = second.
Proof.
  intros first second [left Hleft] [right Hright].
  assert (Hleft_length :
    List.length first = List.length left + List.length second).
  { rewrite Hleft, List.length_app. lia. }
  assert (Hright_length :
    List.length second = List.length right + List.length first).
  { rewrite Hright, List.length_app. lia. }
  assert (List.length left = 0) by lia.
  assert (List.length right = 0) by lia.
  apply List.length_zero_iff_nil in H.
  apply List.length_zero_iff_nil in H0.
  subst left right.
  simpl in Hleft.
  exact Hleft.
Qed.

Theorem derivation_consumes_prefix :
  forall rules,
    (forall path expression input rest tree,
      Derives rules path expression input rest tree ->
      exists consumed, input = List.app consumed rest) /\
    (forall path index items input rest trees,
      DerivesSequence rules path index items input rest trees ->
      exists consumed, input = List.app consumed rest) /\
    (forall path body input rest trees,
      DerivesRepetition rules path body input rest trees ->
      exists consumed, input = List.app consumed rest).
Proof.
  intros rules.
  apply Derivation_mutind.
  - intros path literal tail.
    exists [TLiteral literal]. reflexivity.
  - intros path class lexeme tail.
    exists [TLexical class lexeme]. reflexivity.
  - intros path name body input rest tree Hlookup Hderive IH.
    exact IH.
  - intros path items input rest trees Hderive IH.
    exact IH.
  - intros path items index item input rest tree Hnth Hderive IH.
    exact IH.
  - intros path body input.
    exists []. reflexivity.
  - intros path body input rest tree Hderive IH.
    exact IH.
  - intros path body input rest trees Hderive IH.
    exact IH.
  - intros path index input.
    exists []. reflexivity.
  - intros path index item items input middle rest tree trees
      Hitem IHitem Hitems IHitems.
    destruct IHitem as [first Hfirst].
    destruct IHitems as [second Hsecond].
    exists (List.app first second).
    eapply prefix_compose; eauto.
  - intros path body input.
    exists []. reflexivity.
  - intros path body input middle rest tree trees
      Hbody IHbody Hprogress Hrest IHrest.
    destruct IHbody as [first Hfirst].
    destruct IHrest as [second Hsecond].
    exists (List.app first second).
    eapply prefix_compose; eauto.
Qed.

Corollary derives_consumes_prefix :
  forall rules path expression input rest tree,
    Derives rules path expression input rest tree ->
    exists consumed, input = List.app consumed rest.
Proof.
  intros rules.
  exact (proj1 (derivation_consumes_prefix rules)).
Qed.

Corollary derives_sequence_consumes_prefix :
  forall rules path index items input rest trees,
    DerivesSequence rules path index items input rest trees ->
    exists consumed, input = List.app consumed rest.
Proof.
  intros rules.
  exact (proj1 (proj2 (derivation_consumes_prefix rules))).
Qed.

Corollary derives_repetition_consumes_prefix :
  forall rules path body input rest trees,
    DerivesRepetition rules path body input rest trees ->
    exists consumed, input = List.app consumed rest.
Proof.
  intros rules.
  exact (proj2 (proj2 (derivation_consumes_prefix rules))).
Qed.

Inductive NullableWitness (rules : list GrammarRule)
  : EbnfExpression -> Prop :=
| nullable_nonterminal_witness :
    forall name body,
      lookupRule name rules = Some body ->
      NullableWitness rules body ->
      NullableWitness rules (ENonterminal name)
| nullable_sequence_witness :
    forall items,
      NullableSequenceWitness rules items ->
      NullableWitness rules (ESequence items)
| nullable_alternative_witness :
    forall items,
      NullableAlternativeWitness rules items ->
      NullableWitness rules (EAlternative items)
| nullable_optional_witness :
    forall body,
      NullableWitness rules (EOptional body)
| nullable_repetition_witness :
    forall body,
      NullableWitness rules (ERepetition body)

with NullableSequenceWitness (rules : list GrammarRule)
  : list EbnfExpression -> Prop :=
| nullable_sequence_nil_witness :
    NullableSequenceWitness rules []
| nullable_sequence_cons_witness :
    forall item rest,
      NullableWitness rules item ->
      NullableSequenceWitness rules rest ->
      NullableSequenceWitness rules (item :: rest)

with NullableAlternativeWitness (rules : list GrammarRule)
  : list EbnfExpression -> Prop :=
| nullable_alternative_here_witness :
    forall item rest,
      NullableWitness rules item ->
      NullableAlternativeWitness rules (item :: rest)
| nullable_alternative_later_witness :
    forall item rest,
      NullableAlternativeWitness rules rest ->
      NullableAlternativeWitness rules (item :: rest).

Scheme NullableWitness_ind' := Induction for NullableWitness Sort Prop
with NullableSequenceWitness_ind' := Induction for NullableSequenceWitness Sort Prop
with NullableAlternativeWitness_ind' := Induction for NullableAlternativeWitness Sort Prop.

Combined Scheme NullableWitness_mutind
  from NullableWitness_ind', NullableSequenceWitness_ind',
       NullableAlternativeWitness_ind'.

Lemma nullable_alternative_from_nth :
  forall rules items index item,
    nth_error items index = Some item ->
    NullableWitness rules item ->
    NullableAlternativeWitness rules items.
Proof.
  intros rules items index.
  revert items.
  induction index as [|index IH]; intros items item Hnth Hnullable;
    destruct items as [|head tail]; simpl in Hnth; try discriminate.
  - inversion Hnth; subst.
    now constructor.
  - apply nullable_alternative_later_witness.
    eapply IH; eauto.
Qed.

Theorem no_consume_derivation_has_nullable_witness :
  forall rules,
    (forall path expression input rest tree,
      Derives rules path expression input rest tree ->
      input = rest -> NullableWitness rules expression) /\
    (forall path index items input rest trees,
      DerivesSequence rules path index items input rest trees ->
      input = rest -> NullableSequenceWitness rules items) /\
    (forall path body input rest trees,
      DerivesRepetition rules path body input rest trees ->
      input = rest -> True).
Proof.
  intros rules.
  apply Derivation_mutind.
  - intros path literal tail Hequal.
    apply (f_equal (@List.length ConcreteToken)) in Hequal.
    simpl in Hequal. lia.
  - intros path class lexeme tail Hequal.
    apply (f_equal (@List.length ConcreteToken)) in Hequal.
    simpl in Hequal. lia.
  - intros path name body input rest tree Hlookup Hderive IH Hequal.
    apply nullable_nonterminal_witness with body; auto.
  - intros path items input rest trees Hderive IH Hequal.
    now apply nullable_sequence_witness, IH.
  - intros path items index item input rest tree Hnth Hderive IH Hequal.
    apply nullable_alternative_witness.
    eapply nullable_alternative_from_nth; eauto.
  - intros path body input Hequal.
    constructor.
  - intros path body input rest tree Hderive IH Hequal.
    constructor.
  - intros path body input rest trees Hderive IH Hequal.
    constructor.
  - intros path index input Hequal.
    constructor.
  - intros path index item items input middle rest tree trees
      Hitem IHitem Hitems IHitems Hequal.
    assert (Hinput_middle : input = middle).
    {
      eapply prefix_antisymmetric.
      - eapply derives_consumes_prefix; eauto.
      - destruct (derives_sequence_consumes_prefix
          rules path (S index) items middle rest trees Hitems)
          as [suffix Hsuffix].
        exists suffix. now rewrite <- Hequal in Hsuffix.
    }
    constructor.
    + apply IHitem. exact Hinput_middle.
    + apply IHitems. now rewrite <- Hinput_middle.
  - intros path body input Hequal.
    exact I.
  - intros path body input middle rest tree trees
      Hbody IHbody Hprogress Hrest IHrest Hequal.
    exact I.
Qed.

Corollary derives_no_consume_nullable_witness :
  forall rules path expression input tree,
    Derives rules path expression input input tree ->
    NullableWitness rules expression.
Proof.
  intros rules path expression input tree Hderive.
  eapply (proj1 (no_consume_derivation_has_nullable_witness rules));
    eauto.
Qed.

Inductive FirstWitness (rules : list GrammarRule) (token : OverlapToken)
  : EbnfExpression -> Prop :=
| first_literal_witness :
    forall literal,
      token = OverlapLiteral literal ->
      FirstWitness rules token (ELiteral literal)
| first_lexical_witness :
    forall class_name,
      token = OverlapLexicalClass class_name ->
      FirstWitness rules token (ELexicalClass class_name)
| first_nonterminal_witness :
    forall name body,
      lookupRule name rules = Some body ->
      FirstWitness rules token body ->
      FirstWitness rules token (ENonterminal name)
| first_sequence_witness :
    forall items,
      FirstSequenceWitness rules token items ->
      FirstWitness rules token (ESequence items)
| first_alternative_witness :
    forall items,
      FirstAlternativeWitness rules token items ->
      FirstWitness rules token (EAlternative items)
| first_optional_witness :
    forall body,
      FirstWitness rules token body ->
      FirstWitness rules token (EOptional body)
| first_repetition_witness :
    forall body,
      FirstWitness rules token body ->
      FirstWitness rules token (ERepetition body)

with FirstSequenceWitness
  (rules : list GrammarRule) (token : OverlapToken)
  : list EbnfExpression -> Prop :=
| first_sequence_here_witness :
    forall item rest,
      FirstWitness rules token item ->
      FirstSequenceWitness rules token (item :: rest)
| first_sequence_later_witness :
    forall item rest,
      NullableWitness rules item ->
      FirstSequenceWitness rules token rest ->
      FirstSequenceWitness rules token (item :: rest)

with FirstAlternativeWitness
  (rules : list GrammarRule) (token : OverlapToken)
  : list EbnfExpression -> Prop :=
| first_alternative_here_witness :
    forall item rest,
      FirstWitness rules token item ->
      FirstAlternativeWitness rules token (item :: rest)
| first_alternative_later_witness :
    forall item rest,
      FirstAlternativeWitness rules token rest ->
      FirstAlternativeWitness rules token (item :: rest).

Scheme FirstWitness_ind' := Induction for FirstWitness Sort Prop
with FirstSequenceWitness_ind' := Induction for FirstSequenceWitness Sort Prop
with FirstAlternativeWitness_ind' := Induction for FirstAlternativeWitness Sort Prop.

Combined Scheme FirstWitness_mutind
  from FirstWitness_ind', FirstSequenceWitness_ind',
       FirstAlternativeWitness_ind'.

Lemma first_alternative_from_nth :
  forall rules token items index item,
    nth_error items index = Some item ->
    FirstWitness rules token item ->
    FirstAlternativeWitness rules token items.
Proof.
  intros rules token items index.
  revert items.
  induction index as [|index IH]; intros items item Hnth Hfirst;
    destruct items as [|head tail]; simpl in Hnth; try discriminate.
  - inversion Hnth; subst.
    now constructor.
  - apply first_alternative_later_witness.
    eapply IH; eauto.
Qed.

Definition DerivesFirstProperty
  (rules : list GrammarRule)
  (expression : EbnfExpression)
  (input rest : list ConcreteToken) : Prop :=
  match input with
  | [] => True
  | first_token :: _ =>
      input <> rest ->
      FirstWitness rules (concrete_token_shape first_token) expression
  end.

Definition DerivesSequenceFirstProperty
  (rules : list GrammarRule)
  (items : list EbnfExpression)
  (input rest : list ConcreteToken) : Prop :=
  match input with
  | [] => True
  | first_token :: _ =>
      input <> rest ->
      FirstSequenceWitness rules (concrete_token_shape first_token) items
  end.

Definition DerivesRepetitionFirstProperty
  (rules : list GrammarRule)
  (body : EbnfExpression)
  (input rest : list ConcreteToken) : Prop :=
  match input with
  | [] => True
  | first_token :: _ =>
      input <> rest ->
      FirstWitness rules (concrete_token_shape first_token) body
  end.

Theorem consuming_derivation_has_first_witness :
  forall rules,
    (forall path expression input rest tree,
      Derives rules path expression input rest tree ->
      DerivesFirstProperty rules expression input rest) /\
    (forall path index items input rest trees,
      DerivesSequence rules path index items input rest trees ->
      DerivesSequenceFirstProperty rules items input rest) /\
    (forall path body input rest trees,
      DerivesRepetition rules path body input rest trees ->
      DerivesRepetitionFirstProperty rules body input rest).
Proof.
  intros rules.
  apply Derivation_mutind.
  - intros path literal tail.
    simpl. intros Hneq.
    constructor. reflexivity.
  - intros path class lexeme tail.
    simpl. intros Hneq.
    constructor. reflexivity.
  - intros path name body input rest tree Hlookup Hderive IH.
    unfold DerivesFirstProperty in *.
    destruct input as [|first_token tail]; auto.
    intros Hneq.
    apply first_nonterminal_witness with body; auto.
  - intros path items input rest trees Hderive IH.
    unfold DerivesFirstProperty, DerivesSequenceFirstProperty in *.
    destruct input as [|first_token tail]; auto.
    intros Hneq.
    apply first_sequence_witness.
    exact (IH Hneq).
  - intros path items index item input rest tree Hnth Hderive IH.
    unfold DerivesFirstProperty in *.
    destruct input as [|first_token tail]; auto.
    intros Hneq.
    apply first_alternative_witness.
    eapply first_alternative_from_nth; eauto.
  - intros path body input.
    unfold DerivesFirstProperty.
    destruct input as [|first_token tail]; auto.
    contradiction.
  - intros path body input rest tree Hderive IH.
    unfold DerivesFirstProperty in *.
    destruct input as [|first_token tail]; auto.
    intros Hneq.
    apply first_optional_witness.
    exact (IH Hneq).
  - intros path body input rest trees Hderive IH.
    unfold DerivesFirstProperty, DerivesRepetitionFirstProperty in *.
    destruct input as [|first_token tail]; auto.
    intros Hneq.
    apply first_repetition_witness.
    exact (IH Hneq).
  - intros path index input.
    unfold DerivesSequenceFirstProperty.
    destruct input as [|first_token tail]; auto.
    contradiction.
  - intros path index item items input middle rest tree trees
      Hitem IHitem Hitems IHitems.
    unfold DerivesSequenceFirstProperty in *.
    destruct input as [|first_token tail]; auto.
    intros Hneq.
    destruct (List.list_eq_dec concrete_token_eq_dec
      (first_token :: tail) middle) as [Hequal|Hdifferent].
    + subst middle.
      apply first_sequence_later_witness.
      * eapply derives_no_consume_nullable_witness; eauto.
      * apply IHitems.
        exact Hneq.
    + apply first_sequence_here_witness.
      apply IHitem.
      exact Hdifferent.
  - intros path body input.
    unfold DerivesRepetitionFirstProperty.
    destruct input as [|first_token tail]; auto.
    contradiction.
  - intros path body input middle rest tree trees
      Hbody IHbody Hprogress Hrest IHrest.
    unfold DerivesRepetitionFirstProperty.
    destruct input as [|first_token tail].
    + exact I.
    + unfold DerivesFirstProperty in IHbody.
      exact (IHbody Hprogress).
Qed.

Corollary derives_consuming_first_witness :
  forall rules path expression first_token tail rest tree,
    Derives rules path expression (first_token :: tail) rest tree ->
    first_token :: tail <> rest ->
    FirstWitness rules (concrete_token_shape first_token) expression.
Proof.
  intros rules path expression first_token tail rest tree Hderive Hprogress.
  pose proof (proj1 (consuming_derivation_has_first_witness rules)
    path expression (first_token :: tail) rest tree Hderive) as Hfirst.
  exact (Hfirst Hprogress).
Qed.