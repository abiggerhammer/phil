(*
  PHIL-LLVM-SERVER-FRAMED-INGRESS-001 — normalized proof model for the
  server-framed-ingress-v1 physical lowering introduced by #104.

  The theorem is deliberately scoped to the recognition-failure-detail-v1
  Systems source. Concrete Hello/Begin frame encoding, provider handle
  lifetime semantics, physical I/O, and storage-failure detail remain outside
  this target's authority.
*)

Record LLVMServerFramedIngressModel : Type :=
  mkLLVMServerFramedIngressModel {
    sfiSourceRecognitionFailureAuthority : bool;
    sfiPredecessorClientControlSendAuthority : bool;
    sfiTranslationVerifies : bool;
    sfiGrammarCount : nat;

    sfiHelloReceiveCount : nat;
    sfiHelloTransportExact : bool;
    sfiHelloPendingOutputExact : bool;
    sfiHelloFrameOutputExact : bool;
    sfiHelloBorrowCount : nat;
    sfiHelloBorrowFrameExact : bool;
    sfiHelloBorrowNoCopy : bool;
    sfiHelloRecognizeCount : nat;
    sfiHelloRecognizePendingExact : bool;
    sfiHelloRecognizeRawExact : bool;
    sfiHelloRecognizeRecordExact : bool;
    sfiHelloRecognizeReasonExact : bool;
    sfiHelloBranchesExact : bool;
    sfiHelloCommitCount : nat;
    sfiHelloCommitTransportExact : bool;
    sfiHelloCommitPendingExact : bool;
    sfiHelloFailCount : nat;
    sfiHelloFailPendingExact : bool;
    sfiHelloFailReasonExact : bool;
    sfiHelloDestroyCount : nat;
    sfiHelloDestroyPendingExact : bool;
    sfiHelloDestroyFrameExact : bool;
    sfiHelloFailBeforeDestroy : bool;

    sfiBeginReceiveCount : nat;
    sfiBeginTransportExact : bool;
    sfiBeginPendingOutputExact : bool;
    sfiBeginFrameOutputExact : bool;
    sfiBeginBorrowCount : nat;
    sfiBeginBorrowFrameExact : bool;
    sfiBeginBorrowNoCopy : bool;
    sfiBeginRecognizeCount : nat;
    sfiBeginRecognizePendingExact : bool;
    sfiBeginRecognizeRawExact : bool;
    sfiBeginRecognizeRecordExact : bool;
    sfiBeginRecognizeReasonExact : bool;
    sfiBeginBranchesExact : bool;
    sfiBeginCommitCount : nat;
    sfiBeginCommitTransportExact : bool;
    sfiBeginCommitPendingExact : bool;
    sfiBeginFailCount : nat;
    sfiBeginFailPendingExact : bool;
    sfiBeginFailReasonExact : bool;
    sfiBeginDestroyCount : nat;
    sfiBeginDestroyPendingExact : bool;
    sfiBeginDestroyFrameExact : bool;
    sfiBeginFailBeforeDestroy : bool;

    sfiRecognitionReasonsDistinct : bool;
    sfiLegacyNullaryIngressCount : nat;
    sfiAmbientIngressStateCount : nat;
    sfiUnresolvedIngressControlCount : nat;
    sfiClaimsConcreteFrameCodec : bool;
    sfiClaimsProviderHandleLifetime : bool;
    sfiClaimsStorageFailureDetail : bool
  }.

Definition verified_llvm_server_framed_ingress
  (m : LLVMServerFramedIngressModel) : Prop :=
  sfiSourceRecognitionFailureAuthority m = true /\
  sfiPredecessorClientControlSendAuthority m = true /\
  sfiTranslationVerifies m = true /\
  sfiGrammarCount m = 2 /\

  sfiHelloReceiveCount m = 1 /\
  sfiHelloTransportExact m = true /\
  sfiHelloPendingOutputExact m = true /\
  sfiHelloFrameOutputExact m = true /\
  sfiHelloBorrowCount m = 1 /\
  sfiHelloBorrowFrameExact m = true /\
  sfiHelloBorrowNoCopy m = true /\
  sfiHelloRecognizeCount m = 1 /\
  sfiHelloRecognizePendingExact m = true /\
  sfiHelloRecognizeRawExact m = true /\
  sfiHelloRecognizeRecordExact m = true /\
  sfiHelloRecognizeReasonExact m = true /\
  sfiHelloBranchesExact m = true /\
  sfiHelloCommitCount m = 1 /\
  sfiHelloCommitTransportExact m = true /\
  sfiHelloCommitPendingExact m = true /\
  sfiHelloFailCount m = 1 /\
  sfiHelloFailPendingExact m = true /\
  sfiHelloFailReasonExact m = true /\
  sfiHelloDestroyCount m = 1 /\
  sfiHelloDestroyPendingExact m = true /\
  sfiHelloDestroyFrameExact m = true /\
  sfiHelloFailBeforeDestroy m = true /\

  sfiBeginReceiveCount m = 1 /\
  sfiBeginTransportExact m = true /\
  sfiBeginPendingOutputExact m = true /\
  sfiBeginFrameOutputExact m = true /\
  sfiBeginBorrowCount m = 1 /\
  sfiBeginBorrowFrameExact m = true /\
  sfiBeginBorrowNoCopy m = true /\
  sfiBeginRecognizeCount m = 1 /\
  sfiBeginRecognizePendingExact m = true /\
  sfiBeginRecognizeRawExact m = true /\
  sfiBeginRecognizeRecordExact m = true /\
  sfiBeginRecognizeReasonExact m = true /\
  sfiBeginBranchesExact m = true /\
  sfiBeginCommitCount m = 1 /\
  sfiBeginCommitTransportExact m = true /\
  sfiBeginCommitPendingExact m = true /\
  sfiBeginFailCount m = 1 /\
  sfiBeginFailPendingExact m = true /\
  sfiBeginFailReasonExact m = true /\
  sfiBeginDestroyCount m = 1 /\
  sfiBeginDestroyPendingExact m = true /\
  sfiBeginDestroyFrameExact m = true /\
  sfiBeginFailBeforeDestroy m = true /\

  sfiRecognitionReasonsDistinct m = true /\
  sfiLegacyNullaryIngressCount m = 0 /\
  sfiAmbientIngressStateCount m = 0 /\
  sfiUnresolvedIngressControlCount m = 0 /\
  sfiClaimsConcreteFrameCodec m = false /\
  sfiClaimsProviderHandleLifetime m = false /\
  sfiClaimsStorageFailureDetail m = false.

Theorem verified_llvm_server_framed_ingress_reuses_source_and_predecessor_authority :
  forall m, verified_llvm_server_framed_ingress m ->
    sfiSourceRecognitionFailureAuthority m = true /\
    sfiPredecessorClientControlSendAuthority m = true.
Proof.
  intros m H. unfold verified_llvm_server_framed_ingress in H. tauto.
Qed.

Theorem verified_llvm_server_framed_ingress_preserves_exact_hello_ingress :
  forall m, verified_llvm_server_framed_ingress m ->
    sfiHelloReceiveCount m = 1 /\
    sfiHelloTransportExact m = true /\
    sfiHelloPendingOutputExact m = true /\
    sfiHelloFrameOutputExact m = true /\
    sfiHelloBorrowCount m = 1 /\
    sfiHelloBorrowNoCopy m = true /\
    sfiHelloRecognizeCount m = 1 /\
    sfiHelloRecognizeRecordExact m = true /\
    sfiHelloRecognizeReasonExact m = true.
Proof.
  intros m H. unfold verified_llvm_server_framed_ingress in H. tauto.
Qed.

Theorem verified_llvm_server_framed_ingress_preserves_exact_begin_ingress :
  forall m, verified_llvm_server_framed_ingress m ->
    sfiBeginReceiveCount m = 1 /\
    sfiBeginTransportExact m = true /\
    sfiBeginPendingOutputExact m = true /\
    sfiBeginFrameOutputExact m = true /\
    sfiBeginBorrowCount m = 1 /\
    sfiBeginBorrowNoCopy m = true /\
    sfiBeginRecognizeCount m = 1 /\
    sfiBeginRecognizeRecordExact m = true /\
    sfiBeginRecognizeReasonExact m = true.
Proof.
  intros m H. unfold verified_llvm_server_framed_ingress in H. tauto.
Qed.

Theorem verified_llvm_server_framed_ingress_preserves_commit_and_failure_cleanup :
  forall m, verified_llvm_server_framed_ingress m ->
    sfiHelloCommitCount m = 1 /\
    sfiHelloFailCount m = 1 /\
    sfiHelloDestroyCount m = 1 /\
    sfiHelloFailBeforeDestroy m = true /\
    sfiBeginCommitCount m = 1 /\
    sfiBeginFailCount m = 1 /\
    sfiBeginDestroyCount m = 1 /\
    sfiBeginFailBeforeDestroy m = true.
Proof.
  intros m H. unfold verified_llvm_server_framed_ingress in H. tauto.
Qed.

Theorem verified_llvm_server_framed_ingress_preserves_distinct_failure_reasons :
  forall m, verified_llvm_server_framed_ingress m ->
    sfiHelloFailReasonExact m = true /\
    sfiBeginFailReasonExact m = true /\
    sfiRecognitionReasonsDistinct m = true.
Proof.
  intros m H. unfold verified_llvm_server_framed_ingress in H. tauto.
Qed.

Theorem verified_llvm_server_framed_ingress_eliminates_legacy_and_ambient_ingress_state :
  forall m, verified_llvm_server_framed_ingress m ->
    sfiLegacyNullaryIngressCount m = 0 /\
    sfiAmbientIngressStateCount m = 0 /\
    sfiUnresolvedIngressControlCount m = 0.
Proof.
  intros m H. unfold verified_llvm_server_framed_ingress in H. tauto.
Qed.

Theorem verified_llvm_server_framed_ingress_claims_no_codec_lifetime_or_storage_detail :
  forall m, verified_llvm_server_framed_ingress m ->
    sfiClaimsConcreteFrameCodec m = false /\
    sfiClaimsProviderHandleLifetime m = false /\
    sfiClaimsStorageFailureDetail m = false.
Proof.
  intros m H. unfold verified_llvm_server_framed_ingress in H. tauto.
Qed.

Theorem llvm_server_framed_ingress_identity_or_order_drift_is_rejected :
  forall m,
    sfiHelloRecognizeReasonExact m <> true \/
    sfiBeginRecognizeReasonExact m <> true \/
    sfiHelloFailBeforeDestroy m <> true \/
    sfiBeginFailBeforeDestroy m <> true ->
    ~ verified_llvm_server_framed_ingress m.
Proof.
  intros m Hbad Hgood. unfold verified_llvm_server_framed_ingress in Hgood. tauto.
Qed.

Theorem llvm_server_framed_ingress_ambient_or_legacy_drift_is_rejected :
  forall m,
    sfiLegacyNullaryIngressCount m <> 0 \/
    sfiAmbientIngressStateCount m <> 0 \/
    sfiHelloBorrowNoCopy m <> true \/
    sfiBeginBorrowNoCopy m <> true ->
    ~ verified_llvm_server_framed_ingress m.
Proof.
  intros m Hbad Hgood. unfold verified_llvm_server_framed_ingress in Hgood. tauto.
Qed.
