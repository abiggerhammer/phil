From Stdlib Require Import Lists.List.
Import ListNotations.

(*
  D-RECOGNIZED-OCCURRENCE-ENCODING-01 — the native recognition path currently
  renders four supplied identity components into one opaque textual payload.
  Equality of that payload may be used as a stable occurrence identity only
  when the rendering is injective on the admitted component domain.

  This proof-correspondence model deliberately distinguishes that authority
  premise from the local equality check itself.  It also records a concrete
  collision for an unrestricted delimiter-concatenated domain and a structural
  framing that is injective without an additional textual-domain assumption.
*)

Definition OccurrenceAtom := nat.
Definition OccurrenceField := list OccurrenceAtom.
Definition occurrenceSeparator : OccurrenceAtom := 58.

Record OccurrenceComponents : Type := mkOccurrenceComponents {
  occurrencePending : OccurrenceField;
  occurrenceGrammar : OccurrenceField;
  occurrenceFrame : OccurrenceField;
  occurrenceValue : OccurrenceField
}.

Definition colonRender (components : OccurrenceComponents) : OccurrenceField :=
  occurrencePending components ++ [occurrenceSeparator] ++
  occurrenceGrammar components ++ [occurrenceSeparator] ++
  occurrenceFrame components ++ [occurrenceSeparator] ++
  occurrenceValue components.

Definition AdmittedOccurrenceDomain := OccurrenceComponents -> Prop.

Definition EncodingInjectiveOn
  {Encoded : Type}
  (domain : AdmittedOccurrenceDomain)
  (encode : OccurrenceComponents -> Encoded) : Prop :=
  forall left right,
    domain left ->
    domain right ->
    encode left = encode right ->
    left = right.

Definition unrestrictedOccurrenceDomain : AdmittedOccurrenceDomain :=
  fun _ => True.

Definition ambiguousOccurrenceLeft : OccurrenceComponents :=
  mkOccurrenceComponents
    [1]
    [2; occurrenceSeparator; 3]
    [4]
    [5].

Definition ambiguousOccurrenceRight : OccurrenceComponents :=
  mkOccurrenceComponents
    [1; occurrenceSeparator; 2]
    [3]
    [4]
    [5].

Lemma ambiguous_occurrence_components_are_distinct :
  ambiguousOccurrenceLeft <> ambiguousOccurrenceRight.
Proof.
  intro Hequal.
  pose proof (f_equal occurrencePending Hequal) as Hpending.
  cbn in Hpending.
  discriminate Hpending.
Qed.

Lemma ambiguous_occurrence_components_render_equally :
  colonRender ambiguousOccurrenceLeft =
  colonRender ambiguousOccurrenceRight.
Proof.
  reflexivity.
Qed.

Theorem unrestricted_colon_render_is_not_injective :
  ~ EncodingInjectiveOn unrestrictedOccurrenceDomain colonRender.
Proof.
  intro Hinjective.
  apply ambiguous_occurrence_components_are_distinct.
  apply (Hinjective ambiguousOccurrenceLeft ambiguousOccurrenceRight).
  - exact I.
  - exact I.
  - exact ambiguous_occurrence_components_render_equally.
Qed.

Inductive FramedOccurrence : Type :=
| frameOccurrence :
    OccurrenceField ->
    OccurrenceField ->
    OccurrenceField ->
    OccurrenceField ->
    FramedOccurrence.

Definition structuralRender
  (components : OccurrenceComponents) : FramedOccurrence :=
  frameOccurrence
    (occurrencePending components)
    (occurrenceGrammar components)
    (occurrenceFrame components)
    (occurrenceValue components).

Theorem structural_render_is_injective :
  EncodingInjectiveOn unrestrictedOccurrenceDomain structuralRender.
Proof.
  intros [leftPending leftGrammar leftFrame leftValue]
         [rightPending rightGrammar rightFrame rightValue]
         _ _ Hequal.
  cbn in Hequal.
  inversion Hequal.
  reflexivity.
Qed.

Theorem exact_occurrence_identity_from_admitted_encoding :
  forall
    (Encoded : Type)
    (domain : AdmittedOccurrenceDomain)
    (encode : OccurrenceComponents -> Encoded)
    left right,
    EncodingInjectiveOn domain encode ->
    domain left ->
    domain right ->
    encode left = encode right ->
    left = right.
Proof.
  intros Encoded domain encode left right
    Hinjective Hleft Hright Hequal.
  eapply Hinjective; eauto.
Qed.

Corollary structural_render_recovers_exact_components :
  forall left right,
    structuralRender left = structuralRender right ->
    left = right.
Proof.
  intros left right Hequal.
  eapply exact_occurrence_identity_from_admitted_encoding.
  - exact structural_render_is_injective.
  - exact I.
  - exact I.
  - exact Hequal.
Qed.
