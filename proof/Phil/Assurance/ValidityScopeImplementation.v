From Stdlib Require Import Bool.Bool Lists.List.

Import ListNotations.

From Phil.Assurance Require Import ValidityScope.

(*
  PHIL-ASSURE-VALIDITY-IMPL-001 — executable validity-scope decision seam.

  PHIL-ASSURE-VALIDITY-001 certifies dimension-exact validity authority over a
  normalized partial map.  Production represents one finite scope as a
  Data.Map Text Text and decides applicability by enumerating every bound entry
  and requiring the effective context lookup to return the exact expected
  value.

  This implementation-refinement layer deliberately does not serialize Text or
  Map through Rocq.  Instead, production will later supply one primitive native
  lookup/equality fact per bound scope entry.  The executable kernel owns the
  finite conjunction of those facts.  The correspondence theorem below proves
  that this decision is sound and complete for the Certified ScopeMatches
  proposition when the enumerated entries are complete for the scope and the
  supplied booleans faithfully reflect effective-context lookup equality.
*)

Definition ScopeEntry := (ValidityDimension * ValidityValue)%type.

Fixpoint validityScopeFactsb (facts : list bool) : bool :=
  match facts with
  | [] => true
  | fact :: rest => andb fact (validityScopeFactsb rest)
  end.

Inductive ValidityScopeDecision : Type :=
| ValidityScopeAccepted
| ValidityScopeRejected.

Definition decideValidityScope (facts : list bool) : ValidityScopeDecision :=
  if validityScopeFactsb facts
  then ValidityScopeAccepted
  else ValidityScopeRejected.

(* Every list entry corresponds to one bound dimension/value pair, and each
   Boolean exactly reflects whether the effective context carries that pair. *)
Inductive ScopeFactReflection (effective : ValidityMap)
  : list ScopeEntry -> list bool -> Prop :=
| ScopeFactReflectionNil :
    ScopeFactReflection effective [] []
| ScopeFactReflectionCons :
    forall dimension expected fact entries facts,
      (fact = true <-> effective dimension = Some expected) ->
      ScopeFactReflection effective entries facts ->
      ScopeFactReflection effective
        ((dimension, expected) :: entries)
        (fact :: facts).

(* The finite entry list is exactly the graph of every binding carried by the
   normalized scope.  Ordering and duplicate elimination are representation
   concerns of the later concrete Map bridge. *)
Definition ScopeEntriesComplete
  (scope : ValidityMap)
  (entries : list ScopeEntry) : Prop :=
  forall dimension expected,
    scope dimension = Some expected <->
    In (dimension, expected) entries.

Theorem reflected_facts_true_iff_entries_match :
  forall effective entries facts,
    ScopeFactReflection effective entries facts ->
    (validityScopeFactsb facts = true <->
      forall dimension expected,
        In (dimension, expected) entries ->
        effective dimension = Some expected).
Proof.
  intros effective entries facts Hreflection.
  induction Hreflection as
    [|dimension expected fact entries facts Hfact Hrest IH].
  - cbn.
    split.
    + intros _ dimension expected Hin.
      contradiction.
    + intros _.
      reflexivity.
  - cbn.
    split.
    + intros Hfacts dimension' expected' Hin.
      apply andb_true_iff in Hfacts.
      destruct Hfacts as [Hhead Htail].
      destruct Hin as [Heq | Hin].
      * pose proof (f_equal fst Heq) as Hdimension.
        pose proof (f_equal snd Heq) as Hexpected.
        cbn in Hdimension, Hexpected.
        rewrite <- Hdimension, <- Hexpected.
        exact (proj1 Hfact Hhead).
      * apply (proj1 IH Htail).
        exact Hin.
    + intros Hall.
      apply andb_true_iff.
      split.
      * apply (proj2 Hfact).
        apply Hall.
        left.
        reflexivity.
      * apply (proj2 IH).
        intros dimension' expected' Hin.
        apply Hall.
        right.
        exact Hin.
Qed.

Theorem validity_scope_factsb_true_iff_scope_matches :
  forall scope effective entries facts,
    ScopeEntriesComplete scope entries ->
    ScopeFactReflection effective entries facts ->
    (validityScopeFactsb facts = true <-> ScopeMatches scope effective).
Proof.
  intros scope effective entries facts Hcomplete Hreflection.
  pose proof
    (reflected_facts_true_iff_entries_match
      effective entries facts Hreflection) as Hentries.
  split.
  - intros Hfacts.
    unfold ScopeMatches.
    intros dimension expected Hbound.
    apply (proj1 Hentries Hfacts).
    apply (proj1 (Hcomplete dimension expected)).
    exact Hbound.
  - intros Hmatches.
    apply (proj2 Hentries).
    intros dimension expected Hin.
    unfold ScopeMatches in Hmatches.
    apply Hmatches.
    apply (proj2 (Hcomplete dimension expected)).
    exact Hin.
Qed.

Theorem validity_scope_decision_accept_iff_facts_true :
  forall facts,
    decideValidityScope facts = ValidityScopeAccepted <->
    validityScopeFactsb facts = true.
Proof.
  intros facts.
  unfold decideValidityScope.
  destruct (validityScopeFactsb facts) eqn:Hfacts; cbn;
    split; intro H; try reflexivity; try discriminate.
Qed.

Theorem validity_scope_decision_accept_iff_certified_match :
  forall scope effective entries facts,
    ScopeEntriesComplete scope entries ->
    ScopeFactReflection effective entries facts ->
    (decideValidityScope facts = ValidityScopeAccepted <->
      ScopeMatches scope effective).
Proof.
  intros scope effective entries facts Hcomplete Hreflection.
  split.
  - intros Hdecision.
    apply (proj1
      (validity_scope_factsb_true_iff_scope_matches
        scope effective entries facts Hcomplete Hreflection)).
    apply (proj1 (validity_scope_decision_accept_iff_facts_true facts)).
    exact Hdecision.
  - intros Hmatches.
    apply (proj2 (validity_scope_decision_accept_iff_facts_true facts)).
    apply (proj2
      (validity_scope_factsb_true_iff_scope_matches
        scope effective entries facts Hcomplete Hreflection)).
    exact Hmatches.
Qed.

Theorem empty_validity_scope_facts_accept :
  decideValidityScope [] = ValidityScopeAccepted.
Proof.
  reflexivity.
Qed.

Theorem matching_single_validity_scope_fact_accepts :
  decideValidityScope [true] = ValidityScopeAccepted.
Proof.
  reflexivity.
Qed.

Theorem mismatching_single_validity_scope_fact_rejects :
  decideValidityScope [false] = ValidityScopeRejected.
Proof.
  reflexivity.
Qed.
