From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import DataProduct.

(*
  PHIL-DATA-PRODUCT-001 — executable implementation-refinement staging.

  Product mode and formation uniqueness are already production-bound by
  PHIL-DATA-MODE-001. This layer owns only the product-specific exact
  elimination-plan admission and a fail-closed postcondition over the actual
  native consume/restoration operation.
*)

Inductive ProductEliminationDecision : Type :=
| ProductEliminationAcceptedDecision
| ProductEliminationArityDecision
| ProductEliminationDuplicateSuccessorDecision.

Definition decideProductEliminationByFacts
  (exactArity successorsDistinct : bool) : ProductEliminationDecision :=
  if exactArity then
    if successorsDistinct then
      ProductEliminationAcceptedDecision
    else
      ProductEliminationDuplicateSuccessorDecision
  else
    ProductEliminationArityDecision.

Theorem product_elimination_decision_accepts_iff_facts :
  forall exactArity successorsDistinct,
    decideProductEliminationByFacts exactArity successorsDistinct =
      ProductEliminationAcceptedDecision <->
    exactArity = true /\ successorsDistinct = true.
Proof.
  intros exactArity successorsDistinct.
  destruct exactArity, successorsDistinct; cbn; intuition discriminate.
Qed.

Lemma restoration_plan_exists_for_equal_lengths :
  forall elements successors,
    length successors = length elements ->
    exists plan,
      productRestorationPlan elements successors = Some plan.
Proof.
  induction elements as [| element elementRest IH];
    intros successors Hlength.
  - destruct successors as [| successor successorRest].
    + exists []. reflexivity.
    + discriminate.
  - destruct successors as [| successor successorRest].
    + discriminate.
    + simpl in Hlength.
      injection Hlength as HrestLength.
      destruct (IH successorRest HrestLength) as [tailPlan Htail].
      exists
        (mkRestoredProductBinding
          successor
          (productElementMode element)
          (productElementType element) :: tailPlan).
      simpl.
      rewrite Htail.
      reflexivity.
Qed.

Theorem product_elimination_accepted_iff_facts :
  forall elements successors,
    ProductEliminationAccepted elements successors <->
    length successors = length elements /\ NoDup successors.
Proof.
  intros elements successors.
  split.
  - intro Haccepted.
    split.
    + apply accepted_product_elimination_has_exact_arity.
      exact Haccepted.
    + apply accepted_product_elimination_has_unique_successors.
      exact Haccepted.
  - intros [Hlength Hdistinct].
    destruct (restoration_plan_exists_for_equal_lengths
      elements successors Hlength) as [plan Hplan].
    exists plan.
    split; assumption.
Qed.

Theorem product_elimination_decision_reflects_certified :
  forall elements successors exactArity successorsDistinct,
    (exactArity = true <-> length successors = length elements) ->
    (successorsDistinct = true <-> NoDup successors) ->
    (decideProductEliminationByFacts exactArity successorsDistinct =
       ProductEliminationAcceptedDecision <->
     ProductEliminationAccepted elements successors).
Proof.
  intros elements successors exactArity successorsDistinct
    Harity Hdistinct.
  split.
  - intro Hdecision.
    apply product_elimination_decision_accepts_iff_facts in Hdecision.
    destruct Hdecision as [Hexact Hunique].
    apply (proj2 (product_elimination_accepted_iff_facts elements successors)).
    split.
    + apply (proj1 Harity). exact Hexact.
    + apply (proj1 Hdistinct). exact Hunique.
  - intro Haccepted.
    apply product_elimination_decision_accepts_iff_facts.
    apply (proj1 (product_elimination_accepted_iff_facts elements successors))
      in Haccepted.
    destruct Haccepted as [Hlength Hnodup].
    split.
    + apply (proj2 Harity). exact Hlength.
    + apply (proj2 Hdistinct). exact Hnodup.
Qed.

Inductive ProductRestorationDecision : Type :=
| ProductRestorationAcceptedDecision
| ProductRestorationOwnerDecision
| ProductRestorationExactnessDecision.

Definition decideProductRestorationByFacts
  (ownerConsumed successorsInstalledExact : bool)
  : ProductRestorationDecision :=
  if ownerConsumed then
    if successorsInstalledExact then
      ProductRestorationAcceptedDecision
    else
      ProductRestorationExactnessDecision
  else
    ProductRestorationOwnerDecision.

Theorem product_restoration_decision_accepts_iff_facts :
  forall ownerConsumed successorsInstalledExact,
    decideProductRestorationByFacts ownerConsumed successorsInstalledExact =
      ProductRestorationAcceptedDecision <->
    ownerConsumed = true /\ successorsInstalledExact = true.
Proof.
  intros ownerConsumed successorsInstalledExact.
  destruct ownerConsumed, successorsInstalledExact;
    cbn; intuition discriminate.
Qed.

Theorem product_restoration_decision_reflects_properties :
  forall
    (OwnerConsumed SuccessorsInstalledExact : Prop)
    ownerConsumed successorsInstalledExact,
    (ownerConsumed = true <-> OwnerConsumed) ->
    (successorsInstalledExact = true <-> SuccessorsInstalledExact) ->
    (decideProductRestorationByFacts ownerConsumed successorsInstalledExact =
       ProductRestorationAcceptedDecision <->
     OwnerConsumed /\ SuccessorsInstalledExact).
Proof.
  intros OwnerConsumed SuccessorsInstalledExact
    ownerConsumed successorsInstalledExact Howner Hsuccessors.
  split.
  - intro Hdecision.
    apply product_restoration_decision_accepts_iff_facts in Hdecision.
    destruct Hdecision as [HownerBool HsuccessorBool].
    split.
    + apply (proj1 Howner). exact HownerBool.
    + apply (proj1 Hsuccessors). exact HsuccessorBool.
  - intros [HownerProp HsuccessorProp].
    apply product_restoration_decision_accepts_iff_facts.
    split.
    + apply (proj2 Howner). exact HownerProp.
    + apply (proj2 Hsuccessors). exact HsuccessorProp.
Qed.
