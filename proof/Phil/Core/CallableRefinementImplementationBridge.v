From Stdlib Require Import Bool.Bool Lists.List.

From Phil.Core Require Import CallableRefinementImplementation.

(*
  PHIL-ASSURE-IMPL-CORR-001 — generic finite incidence bridge.

  The production adapter supplies a finite domain covering every element that is
  present in the actual set. The extracted encoder applies the concrete
  membership predicate to that domain. Under the coverage premise, vectorSubset
  is equivalent to extensional predicate subset.

  This theorem is parametric in the element type: it assumes no equality,
  ordering, hashing, or representation operation. Concrete Data.Set operations
  used to establish/check the coverage premise remain a named primitive TCB
  component of the Haskell instantiation rather than part of this theorem.
*)

Section IncidenceBridge.

Context {Element : Type}.
Variable actualMember expectedMember : Element -> bool.

Fixpoint incidenceVector
  (domain : list Element)
  (member : Element -> bool) : BoolVector :=
  match domain with
  | nil => nil
  | element :: rest => member element :: incidenceVector rest member
  end.

Definition predicateSubset
  (actual expected : Element -> bool) : Prop :=
  forall element, actual element = true -> expected element = true.

Definition domainCovers
  (domain : list Element)
  (member : Element -> bool) : Prop :=
  forall element, member element = true -> In element domain.

Lemma vector_subset_incidence_on_domain :
  forall domain,
    vectorSubset
      (incidenceVector domain actualMember)
      (incidenceVector domain expectedMember) ->
    forall element,
      In element domain ->
      actualMember element = true ->
      expectedMember element = true.
Proof.
  induction domain as [| head tail IH]; intros Hsubset element Hin Hactual.
  - contradiction.
  - cbn in Hsubset.
    destruct Hin as [Hequal | Hin].
    + subst element.
      destruct (actualMember head) eqn:HactualHead.
      * destruct (expectedMember head) eqn:HexpectedHead.
        -- reflexivity.
        -- contradiction.
      * discriminate Hactual.
    + destruct (actualMember head) eqn:HactualHead;
        destruct (expectedMember head) eqn:HexpectedHead;
        cbn in Hsubset.
      * eapply IH; eauto.
      * contradiction.
      * eapply IH; eauto.
      * eapply IH; eauto.
Qed.

Lemma predicate_subset_implies_incidence_subset :
  forall domain,
    predicateSubset actualMember expectedMember ->
    vectorSubset
      (incidenceVector domain actualMember)
      (incidenceVector domain expectedMember).
Proof.
  induction domain as [| head tail IH]; intro Hsubset.
  - exact I.
  - cbn.
    destruct (actualMember head) eqn:HactualHead;
      destruct (expectedMember head) eqn:HexpectedHead.
    + apply IH. exact Hsubset.
    + pose proof (Hsubset head HactualHead) as Hallowed.
      rewrite HexpectedHead in Hallowed.
      discriminate.
    + apply IH. exact Hsubset.
    + apply IH. exact Hsubset.
Qed.

Theorem incidence_vector_subset_iff :
  forall domain,
    domainCovers domain actualMember ->
    (vectorSubset
        (incidenceVector domain actualMember)
        (incidenceVector domain expectedMember) <->
      predicateSubset actualMember expectedMember).
Proof.
  intros domain Hcovers.
  split.
  - intros Hvector element Hpresent.
    eapply vector_subset_incidence_on_domain.
    + exact Hvector.
    + apply Hcovers. exact Hpresent.
    + exact Hpresent.
  - apply predicate_subset_implies_incidence_subset.
Qed.

End IncidenceBridge.
