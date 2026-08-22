From Phil.Systems Require Import RecognizedRecord.

(*
  PHIL-SYS-DIGEST-001 — normalized proof model for the explicit
  DigestMatches(begin, payloadView) Systems candidate.

  The concrete candidate introduced by PR #50 corrects the historical
  one-subject digest check by carrying the exact recognized Begin record and
  the exact borrowed payload view in source order.  The borrow must be unique,
  must name the exact payload owner, and must precede the digest terminator.

  This proof deliberately stops at the Systems boundary.  It does not choose a
  physical representation for the borrow, prove SHA-256, or prove the runtime
  provider.  Those are downstream LLVM/runtime obligations.
*)

Definition DigestBlockId := nat.

Record SystemsDigestValidationModel : Type := mkSystemsDigestValidationModel {
  systemsDigestRecognizedRecord : RecognizedRecordModel;
  systemsDigestWitnessRecord : ValueId;
  systemsDigestActualRecordSubject : ValueId;
  systemsDigestWitnessGrammar : RecordGrammarId;
  systemsDigestActualRecordGrammar : RecordGrammarId;
  systemsDigestPayloadOwner : ValueId;
  systemsDigestPayloadView : ValueId;
  systemsDigestBorrowView : ValueId;
  systemsDigestBorrowOwner : ValueId;
  systemsDigestBorrowCount : nat;
  systemsDigestBorrowPrecedesCheck : bool;
  systemsDigestSubjectCount : nat;
  systemsDigestSubject0 : ValueId;
  systemsDigestSubject1 : ValueId;
  systemsDigestBoundaryIsDigest : bool;
  systemsDigestSuccessBlock : DigestBlockId;
  systemsDigestFailureBlock : DigestBlockId
}.

Record SystemsDigestValidationVerificationSuccess
  (model : SystemsDigestValidationModel) : Prop :=
  mkSystemsDigestValidationVerificationSuccess {
    systems_digest_success_recognized_record :
      RecognizedRecordVerificationSuccess
        (systemsDigestRecognizedRecord model);
    systems_digest_success_witness_record :
      systemsDigestWitnessRecord model =
        recordValue (systemsDigestRecognizedRecord model);
    systems_digest_success_witness_grammar :
      systemsDigestWitnessGrammar model =
        recordWitnessGrammar (systemsDigestRecognizedRecord model);
    systems_digest_success_record_subject :
      systemsDigestActualRecordSubject model =
        systemsDigestWitnessRecord model;
    systems_digest_success_record_grammar :
      systemsDigestActualRecordGrammar model =
        systemsDigestWitnessGrammar model;
    systems_digest_success_borrow_view :
      systemsDigestBorrowView model = systemsDigestPayloadView model;
    systems_digest_success_borrow_owner :
      systemsDigestBorrowOwner model = systemsDigestPayloadOwner model;
    systems_digest_success_single_borrow :
      systemsDigestBorrowCount model = 1;
    systems_digest_success_borrow_precedes_check :
      systemsDigestBorrowPrecedesCheck model = true;
    systems_digest_success_two_subjects :
      systemsDigestSubjectCount model = 2;
    systems_digest_success_subject0 :
      systemsDigestSubject0 model = systemsDigestActualRecordSubject model;
    systems_digest_success_subject1 :
      systemsDigestSubject1 model = systemsDigestPayloadView model;
    systems_digest_success_digest_boundary :
      systemsDigestBoundaryIsDigest model = true
  }.

Theorem verified_systems_digest_reuses_recognized_record_authority :
  forall model,
    SystemsDigestValidationVerificationSuccess model ->
    RecognizedRecordVerificationSuccess
      (systemsDigestRecognizedRecord model).
Proof.
  intros model H.
  exact (systems_digest_success_recognized_record model H).
Qed.

Theorem verified_systems_digest_uses_exact_recognized_record_subject :
  forall model,
    SystemsDigestValidationVerificationSuccess model ->
    systemsDigestActualRecordSubject model =
      recordValue (systemsDigestRecognizedRecord model) /\
    systemsDigestActualRecordGrammar model =
      recordWitnessGrammar (systemsDigestRecognizedRecord model).
Proof.
  intros model H.
  split.
  - rewrite (systems_digest_success_record_subject model H).
    exact (systems_digest_success_witness_record model H).
  - rewrite (systems_digest_success_record_grammar model H).
    exact (systems_digest_success_witness_grammar model H).
Qed.

Theorem verified_systems_digest_borrows_exact_payload_owner_once :
  forall model,
    SystemsDigestValidationVerificationSuccess model ->
    systemsDigestBorrowView model = systemsDigestPayloadView model /\
    systemsDigestBorrowOwner model = systemsDigestPayloadOwner model /\
    systemsDigestBorrowCount model = 1.
Proof.
  intros model H.
  repeat split.
  - exact (systems_digest_success_borrow_view model H).
  - exact (systems_digest_success_borrow_owner model H).
  - exact (systems_digest_success_single_borrow model H).
Qed.

Theorem verified_systems_digest_orders_borrow_before_check :
  forall model,
    SystemsDigestValidationVerificationSuccess model ->
    systemsDigestBorrowPrecedesCheck model = true.
Proof.
  intros model H.
  exact (systems_digest_success_borrow_precedes_check model H).
Qed.

Theorem verified_systems_digest_preserves_exact_ordered_subject_pair :
  forall model,
    SystemsDigestValidationVerificationSuccess model ->
    systemsDigestSubjectCount model = 2 /\
    systemsDigestSubject0 model =
      recordValue (systemsDigestRecognizedRecord model) /\
    systemsDigestSubject1 model = systemsDigestPayloadView model.
Proof.
  intros model H.
  repeat split.
  - exact (systems_digest_success_two_subjects model H).
  - rewrite (systems_digest_success_subject0 model H).
    rewrite (systems_digest_success_record_subject model H).
    exact (systems_digest_success_witness_record model H).
  - exact (systems_digest_success_subject1 model H).
Qed.

Theorem verified_systems_digest_uses_digest_boundary :
  forall model,
    SystemsDigestValidationVerificationSuccess model ->
    systemsDigestBoundaryIsDigest model = true.
Proof.
  intros model H.
  exact (systems_digest_success_digest_boundary model H).
Qed.

Theorem systems_digest_record_subject_drift_is_rejected :
  forall model,
    systemsDigestActualRecordSubject model <>
      systemsDigestWitnessRecord model ->
    ~ SystemsDigestValidationVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (systems_digest_success_record_subject model H).
Qed.

Theorem systems_digest_borrow_owner_drift_is_rejected :
  forall model,
    systemsDigestBorrowOwner model <> systemsDigestPayloadOwner model ->
    ~ SystemsDigestValidationVerificationSuccess model.
Proof.
  intros model Hdrift H.
  apply Hdrift.
  exact (systems_digest_success_borrow_owner model H).
Qed.

Theorem systems_digest_competing_or_missing_borrow_is_rejected :
  forall model,
    systemsDigestBorrowCount model <> 1 ->
    ~ SystemsDigestValidationVerificationSuccess model.
Proof.
  intros model Hcount H.
  apply Hcount.
  exact (systems_digest_success_single_borrow model H).
Qed.

Theorem systems_digest_late_borrow_is_rejected :
  forall model,
    systemsDigestBorrowPrecedesCheck model = false ->
    ~ SystemsDigestValidationVerificationSuccess model.
Proof.
  intros model Hlate H.
  rewrite (systems_digest_success_borrow_precedes_check model H) in Hlate.
  discriminate.
Qed.

Theorem systems_digest_subject_arity_drift_is_rejected :
  forall model,
    systemsDigestSubjectCount model <> 2 ->
    ~ SystemsDigestValidationVerificationSuccess model.
Proof.
  intros model Harity H.
  apply Harity.
  exact (systems_digest_success_two_subjects model H).
Qed.

Theorem systems_digest_subject_order_or_identity_drift_is_rejected :
  forall model,
    systemsDigestSubject0 model <>
      systemsDigestActualRecordSubject model \/
    systemsDigestSubject1 model <> systemsDigestPayloadView model ->
    ~ SystemsDigestValidationVerificationSuccess model.
Proof.
  intros model Hdrift H.
  destruct Hdrift as [Hrecord | Hview].
  - apply Hrecord. exact (systems_digest_success_subject0 model H).
  - apply Hview. exact (systems_digest_success_subject1 model H).
Qed.

Theorem systems_digest_non_digest_boundary_is_rejected :
  forall model,
    systemsDigestBoundaryIsDigest model = false ->
    ~ SystemsDigestValidationVerificationSuccess model.
Proof.
  intros model Hboundary H.
  rewrite (systems_digest_success_digest_boundary model H) in Hboundary.
  discriminate.
Qed.
