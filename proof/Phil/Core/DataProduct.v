From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

From Phil.Core Require Import Syntax Context DataMode.

(*
  PHIL-DATA-PRODUCT-001 — ordinary finite product ownership semantics.

  Products are structural in this Phase 1 slice.  Their mode is the strongest
  mode of their ordered element contracts.  Formation reuses DATA-MODE's
  restricted-occurrence discipline; elimination builds an exact positional
  restoration plan with one fresh successor name per element.  Concrete
  Haskell list representation and orchestration remain correspondence.
*)

Record ProductElementContract : Type := mkProductElementContract {
  productElementMode : Mode;
  productElementType : Ty
}.

Definition deriveProductMode
  (elements : list ProductElementContract) : Mode :=
  deriveRecordMode (map productElementMode elements).

Theorem product_mode_bounds_every_element :
  forall elements element,
    In element elements ->
    modeLe (productElementMode element) (deriveProductMode elements).
Proof.
  intros elements element Hin.
  unfold deriveProductMode.
  apply record_mode_bounds_every_field.
  apply in_map.
  exact Hin.
Qed.

Theorem linear_element_makes_product_linear :
  forall elements element,
    In element elements ->
    productElementMode element = Linear ->
    deriveProductMode elements = Linear.
Proof.
  intros elements element Hin Hlinear.
  pose proof (product_mode_bounds_every_element elements element Hin) as Hbound.
  rewrite Hlinear in Hbound.
  unfold modeLe, modeRank in Hbound.
  destruct (deriveProductMode elements); simpl in Hbound; try lia; reflexivity.
Qed.

(* Product formation is exactly the aggregate source-position discipline. *)
Definition ProductFormationAccepted : list AggregateSource -> Prop :=
  AggregateFormationAccepted.

Theorem product_formation_transfers_restricted_owner_once :
  forall sources index source,
    ProductFormationAccepted sources ->
    AtPosition index source sources ->
    RestrictedSource source ->
    forall otherIndex otherSource,
      AtPosition otherIndex otherSource sources ->
      RestrictedSource otherSource ->
      sourceOccurrence otherSource = sourceOccurrence source ->
      otherIndex = index.
Proof.
  intros sources index source Haccepted Hposition Hrestricted
    otherIndex otherSource Hother HotherRestricted Hsame.
  unfold ProductFormationAccepted in Haccepted.
  eapply accepted_formation_transfers_restricted_occurrence_once.
  - exact Haccepted.
  - exact Hposition.
  - exact Hrestricted.
  - exact Hother.
  - exact HotherRestricted.
  - exact Hsame.
Qed.

Theorem duplicate_restricted_product_source_rejects :
  forall source rest,
    RestrictedSource source ->
    ~ ProductFormationAccepted (source :: source :: rest).
Proof.
  intros source rest Hrestricted.
  unfold ProductFormationAccepted.
  apply duplicate_restricted_occurrence_rejects.
  exact Hrestricted.
Qed.

Record RestoredProductBinding : Type := mkRestoredProductBinding {
  restoredProductName : Name;
  restoredProductMode : Mode;
  restoredProductType : Ty
}.

Fixpoint productRestorationPlan
  (elements : list ProductElementContract)
  (successors : list Name) : option (list RestoredProductBinding) :=
  match elements, successors with
  | [], [] => Some []
  | element :: elementRest, successor :: successorRest =>
      match productRestorationPlan elementRest successorRest with
      | Some tail =>
          Some
            (mkRestoredProductBinding
              successor
              (productElementMode element)
              (productElementType element) :: tail)
      | None => None
      end
  | _, _ => None
  end.

Definition ProductEliminationAccepted
  (elements : list ProductElementContract)
  (successors : list Name) : Prop :=
  exists plan,
    productRestorationPlan elements successors = Some plan /\
    NoDup successors.

Lemma restoration_plan_success_has_exact_lengths :
  forall elements successors plan,
    productRestorationPlan elements successors = Some plan ->
    length elements = length successors /\
    length plan = length elements.
Proof.
  induction elements as [| element elementRest IH];
    intros successors plan Hplan.
  - destruct successors as [| successor successorRest].
    + simpl in Hplan.
      inversion Hplan; subst plan.
      split; reflexivity.
    + simpl in Hplan.
      discriminate.
  - destruct successors as [| successor successorRest].
    + simpl in Hplan.
      discriminate.
    + simpl in Hplan.
      destruct (productRestorationPlan elementRest successorRest)
        as [tailPlan |] eqn:Htail; try discriminate.
      inversion Hplan; subst plan; clear Hplan.
      specialize (IH successorRest tailPlan Htail).
      destruct IH as [Hlengths HplanLength].
      simpl.
      split.
      * now rewrite Hlengths.
      * now rewrite HplanLength.
Qed.

Theorem accepted_product_elimination_has_exact_arity :
  forall elements successors,
    ProductEliminationAccepted elements successors ->
    length successors = length elements.
Proof.
  intros elements successors Haccepted.
  destruct Haccepted as [plan [Hplan _]].
  pose proof
    (restoration_plan_success_has_exact_lengths
      elements successors plan Hplan) as [Hlength _].
  symmetry.
  exact Hlength.
Qed.

Theorem accepted_product_elimination_has_unique_successors :
  forall elements successors,
    ProductEliminationAccepted elements successors ->
    NoDup successors.
Proof.
  intros elements successors Haccepted.
  destruct Haccepted as [plan [_ Hnodup]].
  exact Hnodup.
Qed.

Theorem restoration_plan_preserves_exact_element_contract :
  forall elements successors plan,
    productRestorationPlan elements successors = Some plan ->
    forall index element successor,
      nth_error elements index = Some element ->
      nth_error successors index = Some successor ->
      nth_error plan index =
        Some
          (mkRestoredProductBinding
            successor
            (productElementMode element)
            (productElementType element)).
Proof.
  induction elements as [| head tail IH];
    intros successors plan Hplan index element successor Helement Hsuccessor.
  - destruct successors; simpl in Hplan.
    + destruct index; discriminate.
    + discriminate.
  - destruct successors as [| name names]; simpl in Hplan; try discriminate.
    destruct (productRestorationPlan tail names) as [tailPlan |] eqn:Htail;
      try discriminate.
    inversion Hplan; subst plan; clear Hplan.
    destruct index as [| index].
    + simpl in Helement, Hsuccessor.
      inversion Helement; subst element.
      inversion Hsuccessor; subst successor.
      reflexivity.
    + simpl in Helement, Hsuccessor.
      simpl.
      eapply IH.
      * exact Htail.
      * exact Helement.
      * exact Hsuccessor.
Qed.

Theorem accepted_product_elimination_loses_no_element :
  forall elements successors,
    ProductEliminationAccepted elements successors ->
    forall index element,
      nth_error elements index = Some element ->
      exists successor plan,
        productRestorationPlan elements successors = Some plan /\
        nth_error successors index = Some successor /\
        nth_error plan index =
          Some
            (mkRestoredProductBinding
              successor
              (productElementMode element)
              (productElementType element)).
Proof.
  intros elements successors Haccepted index element Helement.
  destruct Haccepted as [plan [Hplan Hnodup]].
  pose proof
    (restoration_plan_success_has_exact_lengths
      elements successors plan Hplan) as [Hlength _].
  assert (HelementPresent : nth_error elements index <> None).
  {
    rewrite Helement.
    discriminate.
  }
  pose proof
    (proj1 (nth_error_Some elements index) HelementPresent) as Hindex.
  assert (HsuccessorIndex : index < length successors).
  {
    rewrite <- Hlength.
    exact Hindex.
  }
  pose proof
    (proj2 (nth_error_Some successors index) HsuccessorIndex)
    as HsuccessorPresent.
  destruct (nth_error successors index) as [successor |] eqn:Hsuccessor.
  - exists successor, plan.
    split.
    + exact Hplan.
    + split.
      * exact Hsuccessor.
      * eapply restoration_plan_preserves_exact_element_contract.
        -- exact Hplan.
        -- exact Helement.
        -- exact Hsuccessor.
  - exfalso.
    apply HsuccessorPresent.
    reflexivity.
Qed.

Theorem accepted_product_elimination_fabricates_no_successor :
  forall elements successors,
    ProductEliminationAccepted elements successors ->
    forall index successor,
      nth_error successors index = Some successor ->
      exists element plan,
        productRestorationPlan elements successors = Some plan /\
        nth_error elements index = Some element /\
        nth_error plan index =
          Some
            (mkRestoredProductBinding
              successor
              (productElementMode element)
              (productElementType element)).
Proof.
  intros elements successors Haccepted index successor Hsuccessor.
  destruct Haccepted as [plan [Hplan Hnodup]].
  pose proof
    (restoration_plan_success_has_exact_lengths
      elements successors plan Hplan) as [Hlength _].
  assert (HsuccessorPresent : nth_error successors index <> None).
  {
    rewrite Hsuccessor.
    discriminate.
  }
  pose proof
    (proj1 (nth_error_Some successors index) HsuccessorPresent) as Hindex.
  assert (HelementIndex : index < length elements).
  {
    rewrite Hlength.
    exact Hindex.
  }
  pose proof
    (proj2 (nth_error_Some elements index) HelementIndex)
    as HelementPresent.
  destruct (nth_error elements index) as [element |] eqn:Helement.
  - exists element, plan.
    split.
    + exact Hplan.
    + split.
      * exact Helement.
      * eapply restoration_plan_preserves_exact_element_contract.
        -- exact Hplan.
        -- exact Helement.
        -- exact Hsuccessor.
  - exfalso.
    apply HelementPresent.
    reflexivity.
Qed.

(* Core one-shot ownership supplies the consuming linear-product step. *)
Theorem consuming_linear_product_removes_owner :
  forall productName context next productType,
    consumeLinear productName context = Consumed productType next ->
    linearBindings next productName = None.
Proof.
  intros productName context next productType Hconsume.
  eapply consumeLinear_success_consumes_owner.
  exact Hconsume.
Qed.

Theorem consuming_linear_product_is_one_shot :
  forall productName context next productType,
    consumeLinear productName context = Consumed productType next ->
    forall laterType later,
      consumeLinear productName next <> Consumed laterType later.
Proof.
  intros productName context next productType Hconsume laterType later.
  eapply core_linear_source_not_reusable_after_transfer.
  exact Hconsume.
Qed.

Definition LinearCompletionAllowed (context : ResourceContext) : Prop :=
  forall name, linearBindings context name = None.

Theorem inserted_linear_product_cannot_be_silently_dropped :
  forall productName productType context next,
    insertBinding Linear productName productType context = Inserted next ->
    ~ LinearCompletionAllowed next.
Proof.
  intros productName productType context next Hinsert Hcomplete.
  pose proof
    (insertBinding_success_exact
      Linear productName productType context next Hinsert) as Hexact.
  destruct Hexact as [_ [_ [_ [Hinstalled _]]]].
  simpl in Hinstalled.
  destruct Hinstalled as [_ [_ Hlinear]].
  specialize (Hcomplete productName).
  rewrite Hlinear in Hcomplete.
  discriminate.
Qed.
