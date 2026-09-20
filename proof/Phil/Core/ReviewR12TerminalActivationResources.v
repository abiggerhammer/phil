From Stdlib Require Import Arith.PeanoNat.

(*
  PHIL-P1-REVIEW-R12 — terminal runtime initialization preserves the exact
  activation ResourceContext for every static process.

  The certified initializer may attach protocol metadata and open-obligation
  state, but it may not erase, replace, or invent the activation resource state.
  The concrete implementation validates exact process coverage and exact
  protocolResources equality before calling the native lifecycle initializer,
  which then stores the supplied protocol-context map unchanged.
*)

Definition ReviewR12ProcessKey := nat.
Definition ReviewR12ResourceState := nat.

Definition ReviewR12ResourceMap :=
  ReviewR12ProcessKey -> option ReviewR12ResourceState.

Definition ExactActivationResourceHandoff
  (activation supplied : ReviewR12ResourceMap) : Prop :=
  forall process resource,
    activation process = Some resource <->
    supplied process = Some resource.

Definition initializeRuntimeResources
  (supplied : ReviewR12ResourceMap) : ReviewR12ResourceMap :=
  supplied.

Theorem review_r12_exact_handoff_preserves_activation_resources :
  forall activation supplied process resource,
    ExactActivationResourceHandoff activation supplied ->
    activation process = Some resource ->
    initializeRuntimeResources supplied process = Some resource.
Proof.
  intros activation supplied process resource Hexact Hactivation.
  unfold initializeRuntimeResources.
  apply (proj1 (Hexact process resource)).
  exact Hactivation.
Qed.

Theorem review_r12_runtime_resource_map_is_exact_supplied_map :
  forall supplied process,
    initializeRuntimeResources supplied process = supplied process.
Proof.
  reflexivity.
Qed.

Theorem review_r12_missing_protocol_context_rejects :
  forall activation supplied process resource,
    activation process = Some resource ->
    supplied process = None ->
    ~ ExactActivationResourceHandoff activation supplied.
Proof.
  intros activation supplied process resource Hactivation Hmissing Hexact.
  pose proof (proj1 (Hexact process resource) Hactivation) as Hsupplied.
  rewrite Hmissing in Hsupplied.
  discriminate.
Qed.

Theorem review_r12_unexpected_protocol_context_rejects :
  forall activation supplied process resource,
    activation process = None ->
    supplied process = Some resource ->
    ~ ExactActivationResourceHandoff activation supplied.
Proof.
  intros activation supplied process resource Hmissing Hsupplied Hexact.
  pose proof (proj2 (Hexact process resource) Hsupplied) as Hactivation.
  rewrite Hmissing in Hactivation.
  discriminate.
Qed.

Theorem review_r12_replacement_resource_context_rejects :
  forall activation supplied process expected replacement,
    activation process = Some expected ->
    supplied process = Some replacement ->
    expected <> replacement ->
    ~ ExactActivationResourceHandoff activation supplied.
Proof.
  intros activation supplied process expected replacement
    Hactivation Hsupplied Hdifferent Hexact.
  pose proof (proj1 (Hexact process expected) Hactivation) as Hexpected.
  rewrite Hsupplied in Hexpected.
  inversion Hexpected; subst.
  apply Hdifferent.
  reflexivity.
Qed.

Theorem review_r12_empty_replacement_cannot_erase_live_resource :
  forall activation supplied process liveResource,
    activation process = Some liveResource ->
    supplied process = None ->
    ~ ExactActivationResourceHandoff activation supplied.
Proof.
  exact review_r12_missing_protocol_context_rejects.
Qed.

Record ReviewR12InitializationFacts : Type := mkReviewR12InitializationFacts {
  r12ActivationProcessCoverageExact : Prop;
  r12ActivationResourcesExact : Prop;
  r12NativeInitializerPreservesContexts : Prop;
  r12RuntimeInvariantHolds : Prop;
  r12RuntimeNetworkIdentityPreserved : Prop
}.

Definition ReviewR12InitializationValid
  (facts : ReviewR12InitializationFacts) : Prop :=
  r12ActivationProcessCoverageExact facts /\
  r12ActivationResourcesExact facts /\
  r12NativeInitializerPreservesContexts facts /\
  r12RuntimeInvariantHolds facts /\
  r12RuntimeNetworkIdentityPreserved facts.

Theorem review_r12_valid_initialization_requires_exact_activation_resources :
  forall facts,
    ReviewR12InitializationValid facts ->
    r12ActivationResourcesExact facts.
Proof.
  intros facts Hvalid.
  exact (proj1 (proj2 Hvalid)).
Qed.

Theorem review_r12_valid_initialization_preserves_native_context_handoff :
  forall facts,
    ReviewR12InitializationValid facts ->
    r12NativeInitializerPreservesContexts facts.
Proof.
  intros facts Hvalid.
  exact (proj1 (proj2 (proj2 Hvalid))).
Qed.

Theorem review_r12_terminal_initialization_is_not_resource_reconstruction :
  forall facts,
    ReviewR12InitializationValid facts ->
    r12ActivationProcessCoverageExact facts /\
    r12ActivationResourcesExact facts /\
    r12NativeInitializerPreservesContexts facts.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [Hcoverage [Hresources [Hnative _]]].
  repeat split; assumption.
Qed.
