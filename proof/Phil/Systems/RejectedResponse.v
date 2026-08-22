From Phil.Systems Require Import ScalarDataflow DigestValidation Storage AcceptedResponse.

(*
  PHIL-SYS-REJECTED-001 — normalized proof model for the Phase 0
  select rejected(reason) boundary materialized by PR #56.

  The exact DigestBoundary failure edge reaches the exact rejected block.  The
  exact payload owner is released before response emission, the exact component
  transport is used by the sole select rejected operation, and the block ends
  in the exact source failure outcome.

  The frozen Phase 0 program exposes exactly one peer-observable digest-failure
  equivalence class at this boundary: DigestMismatch.  This is deliberately an
  observational statement about this program, not a theorem that the abstract
  DigestFailure type has only one inhabitant.  The concrete i8 reason code and
  two-octet wire encoding are downstream target/runtime choices.
*)

Record SystemsRejectedResponseModel : Type := mkSystemsRejectedResponseModel {
  systemsRejectedAccepted : SystemsAcceptedResponseModel;

  systemsRejectedWitnessDigestBlock : DigestBlockId;
  systemsRejectedActualDigestBlock : DigestBlockId;
  systemsRejectedDigestBoundaryIsDigest : bool;

  systemsRejectedWitnessBlock : DigestBlockId;
  systemsRejectedActualBlock : DigestBlockId;

  systemsRejectedWitnessTransport : ValueId;
  systemsRejectedActualTransport : ValueId;
  systemsRejectedTransportIsHandle : bool;

  systemsRejectedWitnessPayloadOwner : ValueId;
  systemsRejectedActualReleasedOwner : ValueId;
  systemsRejectedReleasePrecedesSelect : bool;

  systemsRejectedOperationIsSelectRejected : bool;
  systemsRejectedOperationCount : nat;
  systemsRejectedInputArity : nat;
  systemsRejectedInput0 : ValueId;
  systemsRejectedOutputArity : nat;
  systemsRejectedRuntimeSiteAbsent : bool;

  systemsRejectedObservableClassIsDigestMismatch : bool;
  systemsRejectedObservableClassCount : nat;
  systemsRejectedTerminatesFailure : bool
}.

Record SystemsRejectedResponseVerificationSuccess
  (model : SystemsRejectedResponseModel) : Prop :=
  mkSystemsRejectedResponseVerificationSuccess {
    systems_rejected_success_accepted :
      SystemsAcceptedResponseVerificationSuccess (systemsRejectedAccepted model);

    systems_rejected_success_digest_block :
      systemsRejectedActualDigestBlock model =
        systemsRejectedWitnessDigestBlock model;
    systems_rejected_success_digest_boundary :
      systemsRejectedDigestBoundaryIsDigest model = true;
    systems_rejected_success_digest_failure_target :
      systemsDigestFailureBlock
        (systemsStorageDigest
          (systemsAcceptedStorage (systemsRejectedAccepted model))) =
        systemsRejectedWitnessBlock model;
    systems_rejected_success_block :
      systemsRejectedActualBlock model = systemsRejectedWitnessBlock model;

    systems_rejected_success_transport_from_accepted :
      systemsRejectedWitnessTransport model =
        systemsAcceptedWitnessTransport (systemsRejectedAccepted model);
    systems_rejected_success_transport :
      systemsRejectedActualTransport model = systemsRejectedWitnessTransport model;
    systems_rejected_success_transport_role :
      systemsRejectedTransportIsHandle model = true;

    systems_rejected_success_payload_from_storage :
      systemsRejectedWitnessPayloadOwner model =
        systemsStorageWitnessOwner
          (systemsAcceptedStorage (systemsRejectedAccepted model));
    systems_rejected_success_release_owner :
      systemsRejectedActualReleasedOwner model =
        systemsRejectedWitnessPayloadOwner model;
    systems_rejected_success_release_before_select :
      systemsRejectedReleasePrecedesSelect model = true;

    systems_rejected_success_operation :
      systemsRejectedOperationIsSelectRejected model = true;
    systems_rejected_success_single_operation :
      systemsRejectedOperationCount model = 1;
    systems_rejected_success_input_arity :
      systemsRejectedInputArity model = 1;
    systems_rejected_success_input0 :
      systemsRejectedInput0 model = systemsRejectedActualTransport model;
    systems_rejected_success_no_outputs :
      systemsRejectedOutputArity model = 0;
    systems_rejected_success_no_runtime_site :
      systemsRejectedRuntimeSiteAbsent model = true;

    systems_rejected_success_observable_digest_mismatch :
      systemsRejectedObservableClassIsDigestMismatch model = true;
    systems_rejected_success_single_observable_class :
      systemsRejectedObservableClassCount model = 1;
    systems_rejected_success_termination :
      systemsRejectedTerminatesFailure model = true
  }.

Theorem verified_systems_rejected_reuses_accepted_authority :
  forall model,
    SystemsRejectedResponseVerificationSuccess model ->
    SystemsAcceptedResponseVerificationSuccess (systemsRejectedAccepted model).
Proof.
  intros model H.
  exact (systems_rejected_success_accepted model H).
Qed.

Theorem verified_systems_rejected_uses_exact_digest_failure_edge :
  forall model,
    SystemsRejectedResponseVerificationSuccess model ->
    systemsRejectedActualDigestBlock model =
      systemsRejectedWitnessDigestBlock model /\
    systemsRejectedDigestBoundaryIsDigest model = true /\
    systemsDigestFailureBlock
      (systemsStorageDigest
        (systemsAcceptedStorage (systemsRejectedAccepted model))) =
      systemsRejectedActualBlock model.
Proof.
  intros model H.
  repeat split.
  - exact (systems_rejected_success_digest_block model H).
  - exact (systems_rejected_success_digest_boundary model H).
  - rewrite (systems_rejected_success_block model H).
    exact (systems_rejected_success_digest_failure_target model H).
Qed.

Theorem verified_systems_rejected_releases_exact_payload_before_select :
  forall model,
    SystemsRejectedResponseVerificationSuccess model ->
    systemsRejectedActualReleasedOwner model =
      systemsStorageWitnessOwner
        (systemsAcceptedStorage (systemsRejectedAccepted model)) /\
    systemsRejectedReleasePrecedesSelect model = true.
Proof.
  intros model H.
  split.
  - rewrite (systems_rejected_success_release_owner model H).
    exact (systems_rejected_success_payload_from_storage model H).
  - exact (systems_rejected_success_release_before_select model H).
Qed.

Theorem verified_systems_rejected_uses_exact_transport :
  forall model,
    SystemsRejectedResponseVerificationSuccess model ->
    systemsRejectedActualTransport model =
      systemsAcceptedWitnessTransport (systemsRejectedAccepted model) /\
    systemsRejectedTransportIsHandle model = true.
Proof.
  intros model H.
  split.
  - rewrite (systems_rejected_success_transport model H).
    exact (systems_rejected_success_transport_from_accepted model H).
  - exact (systems_rejected_success_transport_role model H).
Qed.

Theorem verified_systems_rejected_has_single_observable_digest_mismatch_class :
  forall model,
    SystemsRejectedResponseVerificationSuccess model ->
    systemsRejectedObservableClassIsDigestMismatch model = true /\
    systemsRejectedObservableClassCount model = 1.
Proof.
  intros model H.
  split.
  - exact (systems_rejected_success_observable_digest_mismatch model H).
  - exact (systems_rejected_success_single_observable_class model H).
Qed.

Theorem verified_systems_rejected_has_exact_selector_shape_and_failure_termination :
  forall model,
    SystemsRejectedResponseVerificationSuccess model ->
    systemsRejectedOperationIsSelectRejected model = true /\
    systemsRejectedOperationCount model = 1 /\
    systemsRejectedInputArity model = 1 /\
    systemsRejectedInput0 model = systemsRejectedWitnessTransport model /\
    systemsRejectedOutputArity model = 0 /\
    systemsRejectedRuntimeSiteAbsent model = true /\
    systemsRejectedTerminatesFailure model = true.
Proof.
  intros model H.
  repeat split.
  - exact (systems_rejected_success_operation model H).
  - exact (systems_rejected_success_single_operation model H).
  - exact (systems_rejected_success_input_arity model H).
  - rewrite (systems_rejected_success_input0 model H).
    exact (systems_rejected_success_transport model H).
  - exact (systems_rejected_success_no_outputs model H).
  - exact (systems_rejected_success_no_runtime_site model H).
  - exact (systems_rejected_success_termination model H).
Qed.

Theorem systems_rejected_digest_edge_drift_is_rejected :
  forall model,
    systemsRejectedActualDigestBlock model <>
      systemsRejectedWitnessDigestBlock model \/
    systemsRejectedDigestBoundaryIsDigest model = false \/
    systemsDigestFailureBlock
      (systemsStorageDigest
        (systemsAcceptedStorage (systemsRejectedAccepted model))) <>
      systemsRejectedWitnessBlock model \/
    systemsRejectedActualBlock model <> systemsRejectedWitnessBlock model ->
    ~ SystemsRejectedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hdigest | [Hboundary | [Htarget | Hblock]]].
  - apply Hdigest. exact (systems_rejected_success_digest_block model H).
  - rewrite (systems_rejected_success_digest_boundary model H) in Hboundary. discriminate.
  - apply Htarget. exact (systems_rejected_success_digest_failure_target model H).
  - apply Hblock. exact (systems_rejected_success_block model H).
Qed.

Theorem systems_rejected_release_drift_is_rejected :
  forall model,
    systemsRejectedActualReleasedOwner model <>
      systemsRejectedWitnessPayloadOwner model \/
    systemsRejectedWitnessPayloadOwner model <>
      systemsStorageWitnessOwner
        (systemsAcceptedStorage (systemsRejectedAccepted model)) \/
    systemsRejectedReleasePrecedesSelect model = false ->
    ~ SystemsRejectedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Howner | [Hsource | Horder]].
  - apply Howner. exact (systems_rejected_success_release_owner model H).
  - apply Hsource. exact (systems_rejected_success_payload_from_storage model H).
  - rewrite (systems_rejected_success_release_before_select model H) in Horder. discriminate.
Qed.

Theorem systems_rejected_transport_drift_is_rejected :
  forall model,
    systemsRejectedActualTransport model <> systemsRejectedWitnessTransport model \/
    systemsRejectedWitnessTransport model <>
      systemsAcceptedWitnessTransport (systemsRejectedAccepted model) \/
    systemsRejectedTransportIsHandle model = false ->
    ~ SystemsRejectedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Htransport | [Hsource | Hrole]].
  - apply Htransport. exact (systems_rejected_success_transport model H).
  - apply Hsource. exact (systems_rejected_success_transport_from_accepted model H).
  - rewrite (systems_rejected_success_transport_role model H) in Hrole. discriminate.
Qed.

Theorem systems_rejected_observable_class_drift_is_rejected :
  forall model,
    systemsRejectedObservableClassIsDigestMismatch model = false \/
    systemsRejectedObservableClassCount model <> 1 ->
    ~ SystemsRejectedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hclass | Hcount].
  - rewrite (systems_rejected_success_observable_digest_mismatch model H) in Hclass. discriminate.
  - apply Hcount. exact (systems_rejected_success_single_observable_class model H).
Qed.

Theorem systems_rejected_selector_or_termination_drift_is_rejected :
  forall model,
    systemsRejectedOperationIsSelectRejected model = false \/
    systemsRejectedOperationCount model <> 1 \/
    systemsRejectedInputArity model <> 1 \/
    systemsRejectedInput0 model <> systemsRejectedActualTransport model \/
    systemsRejectedOutputArity model <> 0 \/
    systemsRejectedRuntimeSiteAbsent model = false \/
    systemsRejectedTerminatesFailure model = false ->
    ~ SystemsRejectedResponseVerificationSuccess model.
Proof.
  intros model Hbad H.
  destruct Hbad as [Hop | [Hcount | [Harity | [Hinput | [Houtputs | [Hsite | Hend]]]]]].
  - rewrite (systems_rejected_success_operation model H) in Hop. discriminate.
  - apply Hcount. exact (systems_rejected_success_single_operation model H).
  - apply Harity. exact (systems_rejected_success_input_arity model H).
  - apply Hinput. exact (systems_rejected_success_input0 model H).
  - apply Houtputs. exact (systems_rejected_success_no_outputs model H).
  - rewrite (systems_rejected_success_no_runtime_site model H) in Hsite. discriminate.
  - rewrite (systems_rejected_success_termination model H) in Hend. discriminate.
Qed.
