From Stdlib Require Import Arith.PeanoNat.

(*
  PHIL-P1-REVIEW-R14 — independent provider-call inventory completeness.

  REVIEW-R13 establishes the semantic meaning of every represented provider
  call.  R14 adds the independent completeness condition: the set of required
  call sites supplied by the external expectation authority must be exactly the
  represented provider-call site domain.

  This closes the coordinated-deletion gap left intentionally open by the
  relative SYS-005/SYS-006 stage validators.  Removing a site, its link, and
  its authority/effect use can preserve internal relative consistency, but it
  cannot preserve equality with the independent required inventory.
*)

Definition ReviewR14Site := nat.
Definition ReviewR14Inventory := ReviewR14Site -> Prop.
Definition ReviewR14MeaningValidity := ReviewR14Site -> Prop.

Definition ReviewR14InventoryExact
  (required represented : ReviewR14Inventory) : Prop :=
  forall site, required site <-> represented site.

Definition ReviewR14RepresentedMeaningsValid
  (represented : ReviewR14Inventory)
  (meaningValid : ReviewR14MeaningValidity) : Prop :=
  forall site, represented site -> meaningValid site.

Definition ReviewR14ProviderStageComplete
  (required represented : ReviewR14Inventory)
  (meaningValid : ReviewR14MeaningValidity) : Prop :=
  ReviewR14InventoryExact required represented /\
  ReviewR14RepresentedMeaningsValid represented meaningValid.

Definition reviewR14RemoveSite
  (inventory : ReviewR14Inventory)
  (removed : ReviewR14Site) : ReviewR14Inventory :=
  fun site => inventory site /\ site <> removed.

Theorem review_r14_exact_inventory_accepts_identity :
  forall inventory,
    ReviewR14InventoryExact inventory inventory.
Proof.
  intros inventory site.
  split; intros H; exact H.
Qed.

Theorem review_r14_coordinated_required_site_deletion_breaks_completeness :
  forall required represented site,
    ReviewR14InventoryExact required represented ->
    required site ->
    ~ ReviewR14InventoryExact
        required (reviewR14RemoveSite represented site).
Proof.
  intros required represented site Hexact Hrequired Hdeleted.
  pose proof (proj1 (Hdeleted site) Hrequired) as Hafter.
  unfold reviewR14RemoveSite in Hafter.
  destruct Hafter as [_ Hneq].
  apply Hneq.
  reflexivity.
Qed.

Theorem review_r14_empty_relative_inventory_is_not_complete_when_required_nonempty :
  forall required,
    (exists site, required site) ->
    ~ ReviewR14InventoryExact required (fun _ => False).
Proof.
  intros required [site Hrequired] Hexact.
  pose proof (proj1 (Hexact site) Hrequired) as Hfalse.
  exact Hfalse.
Qed.

Theorem review_r14_unexpected_candidate_site_breaks_completeness :
  forall required represented site,
    represented site ->
    ~ required site ->
    ~ ReviewR14InventoryExact required represented.
Proof.
  intros required represented site Hrepresented Hnotrequired Hexact.
  pose proof (proj2 (Hexact site) Hrepresented) as Hrequired.
  apply Hnotrequired.
  exact Hrequired.
Qed.

Theorem review_r14_complete_stage_retains_per_site_semantics :
  forall required represented meaningValid,
    ReviewR14ProviderStageComplete required represented meaningValid ->
    ReviewR14RepresentedMeaningsValid represented meaningValid.
Proof.
  intros required represented meaningValid Hcomplete.
  exact (proj2 Hcomplete).
Qed.

Theorem review_r14_complete_stage_retains_independent_domain_equality :
  forall required represented meaningValid,
    ReviewR14ProviderStageComplete required represented meaningValid ->
    ReviewR14InventoryExact required represented.
Proof.
  intros required represented meaningValid Hcomplete.
  exact (proj1 Hcomplete).
Qed.

Theorem review_r14_relative_semantic_validity_alone_does_not_imply_completeness :
  exists required represented meaningValid,
    ReviewR14RepresentedMeaningsValid represented meaningValid /\
    ~ ReviewR14InventoryExact required represented.
Proof.
  exists (fun site => site = 0).
  exists (fun _ => False).
  exists (fun _ => True).
  split.
  - intros site Hrepresented.
    destruct Hrepresented.
  - intro Hexact.
    pose proof (proj1 (Hexact 0) eq_refl) as Hfalse.
    exact Hfalse.
Qed.

Definition ReviewR14AuthorityStageComplete
  (required represented : ReviewR14Inventory)
  (meaningValid : ReviewR14MeaningValidity)
  (relativeAuthorityEffectValid : Prop) : Prop :=
  ReviewR14ProviderStageComplete required represented meaningValid /\
  relativeAuthorityEffectValid.

Theorem review_r14_authority_stage_cannot_hide_provider_inventory_deletion :
  forall required represented meaningValid relativeAuthorityEffectValid site,
    ReviewR14AuthorityStageComplete
      required represented meaningValid relativeAuthorityEffectValid ->
    required site ->
    ~ ReviewR14AuthorityStageComplete
        required
        (reviewR14RemoveSite represented site)
        meaningValid
        relativeAuthorityEffectValid.
Proof.
  intros required represented meaningValid relativeAuthorityEffectValid site
    Hcomplete Hrequired Hdeleted.
  destruct Hcomplete as [[Hexact _] _].
  destruct Hdeleted as [[HdeletedExact _] _].
  eapply
    (review_r14_coordinated_required_site_deletion_breaks_completeness
      required represented site Hexact Hrequired).
  exact HdeletedExact.
Qed.

Theorem review_r14_authority_stage_preserves_independent_provider_inventory :
  forall required represented meaningValid relativeAuthorityEffectValid,
    ReviewR14AuthorityStageComplete
      required represented meaningValid relativeAuthorityEffectValid ->
    ReviewR14InventoryExact required represented.
Proof.
  intros required represented meaningValid relativeAuthorityEffectValid Hcomplete.
  exact (proj1 (proj1 Hcomplete)).
Qed.
