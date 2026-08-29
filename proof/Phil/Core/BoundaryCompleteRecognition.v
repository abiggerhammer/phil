From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(*
  PHIL-BND-COMPLETE-001 — complete-frame recognition and failure semantics.

  This proof isolates the Phase 1 boundary-recognition rule layered over the
  existing recognition machinery: success/failure classification is only
  eligible after exact complete-frame consumption, success/failure witnesses
  preserve exact ingress provenance, and malformed recognition finalization
  consumes the pending recognition state without manufacturing a success
  continuation.
*)

Record RecognitionExtent : Type := mkRecognitionExtent {
  declaredFrameBytes : Z;
  consumedFrameBytes : Z
}.

Inductive ExtentCheck : Type :=
| ExtentInvalid
| ExtentTrailing
| ExtentPast
| ExtentComplete.

Definition checkCompleteExtent (extent : RecognitionExtent) : ExtentCheck :=
  if Z.ltb (declaredFrameBytes extent) 0 then ExtentInvalid
  else if Z.ltb (consumedFrameBytes extent) 0 then ExtentInvalid
  else if Z.ltb (consumedFrameBytes extent) (declaredFrameBytes extent)
       then ExtentTrailing
  else if Z.ltb (declaredFrameBytes extent) (consumedFrameBytes extent)
       then ExtentPast
  else ExtentComplete.

Definition CompleteExtent (extent : RecognitionExtent) : Prop :=
  0 <= declaredFrameBytes extent /\
  0 <= consumedFrameBytes extent /\
  consumedFrameBytes extent = declaredFrameBytes extent.

Theorem check_complete_extent_complete_iff :
  forall extent,
    checkCompleteExtent extent = ExtentComplete <->
    CompleteExtent extent.
Proof.
  intros [declared consumed].
  unfold checkCompleteExtent, CompleteExtent.
  simpl.
  split.
  - intro Hcheck.
    destruct (Z.ltb declared 0) eqn:Hdeclared; try discriminate.
    destruct (Z.ltb consumed 0) eqn:Hconsumed; try discriminate.
    destruct (Z.ltb consumed declared) eqn:Htrailing; try discriminate.
    destruct (Z.ltb declared consumed) eqn:Hpast; try discriminate.
    inversion Hcheck; clear Hcheck.
    pose proof ((proj1 (Z.ltb_ge declared 0)) Hdeclared) as HdeclaredNonnegative.
    pose proof ((proj1 (Z.ltb_ge consumed 0)) Hconsumed) as HconsumedNonnegative.
    pose proof ((proj1 (Z.ltb_ge consumed declared)) Htrailing) as HnotTrailing.
    pose proof ((proj1 (Z.ltb_ge declared consumed)) Hpast) as HnotPast.
    repeat split; lia.
  - intros [Hdeclared [Hconsumed Hequal]].
    subst consumed.
    assert (Hnonnegative : (declared <? 0) = false).
    { exact ((proj2 (Z.ltb_ge declared 0)) Hdeclared). }
    assert (Hself : (declared <? declared) = false).
    { exact ((proj2 (Z.ltb_ge declared declared)) (Z.le_refl declared)). }
    repeat rewrite Hnonnegative.
    repeat rewrite Hself.
    reflexivity.
Qed.

Theorem trailing_extent_classifies_exactly :
  forall declared consumed,
    0 <= declared ->
    0 <= consumed ->
    consumed < declared ->
    checkCompleteExtent (mkRecognitionExtent declared consumed) = ExtentTrailing.
Proof.
  intros declared consumed Hdeclared Hconsumed Hlt.
  unfold checkCompleteExtent.
  simpl.
  assert (Hd : (declared <? 0) = false).
  { exact ((proj2 (Z.ltb_ge declared 0)) Hdeclared). }
  assert (Hc : (consumed <? 0) = false).
  { exact ((proj2 (Z.ltb_ge consumed 0)) Hconsumed). }
  assert (Ht : (consumed <? declared) = true).
  { exact ((proj2 (Z.ltb_lt consumed declared)) Hlt). }
  rewrite Hd, Hc, Ht.
  reflexivity.
Qed.

Theorem consumed_past_frame_classifies_exactly :
  forall declared consumed,
    0 <= declared ->
    0 <= consumed ->
    declared < consumed ->
    checkCompleteExtent (mkRecognitionExtent declared consumed) = ExtentPast.
Proof.
  intros declared consumed Hdeclared Hconsumed Hlt.
  unfold checkCompleteExtent.
  simpl.
  assert (Hd : (declared <? 0) = false).
  { exact ((proj2 (Z.ltb_ge declared 0)) Hdeclared). }
  assert (Hc : (consumed <? 0) = false).
  { exact ((proj2 (Z.ltb_ge consumed 0)) Hconsumed). }
  assert (HnotTrailing : (consumed <? declared) = false).
  { exact ((proj2 (Z.ltb_ge consumed declared)) (Z.le_trans _ _ _ (Z.le_refl declared) (Z.lt_le_incl _ _ Hlt))). }
  assert (Hpast : (declared <? consumed) = true).
  { exact ((proj2 (Z.ltb_lt declared consumed)) Hlt). }
  rewrite Hd, Hc, HnotTrailing, Hpast.
  reflexivity.
Qed.

Theorem negative_extent_rejects :
  forall declared consumed,
    declared < 0 \/ consumed < 0 ->
    checkCompleteExtent (mkRecognitionExtent declared consumed) = ExtentInvalid.
Proof.
  intros declared consumed [Hdeclared | Hconsumed].
  - unfold checkCompleteExtent.
    simpl.
    assert (Hd : (declared <? 0) = true).
    { exact ((proj2 (Z.ltb_lt declared 0)) Hdeclared). }
    rewrite Hd.
    reflexivity.
  - unfold checkCompleteExtent.
    simpl.
    destruct (Z.ltb declared 0) eqn:Hd.
    + reflexivity.
    + assert (Hc : (consumed <? 0) = true).
      { exact ((proj2 (Z.ltb_lt consumed 0)) Hconsumed). }
      rewrite Hc.
      reflexivity.
Qed.

Record PendingRawView : Type := mkPendingRawView {
  rawPendingOwner : nat;
  rawGrammarId : nat;
  rawFrameId : nat
}.

Record ParsedWitness : Type := mkParsedWitness {
  parsedPendingOwner : nat;
  parsedGrammarId : nat;
  parsedFrameId : nat;
  parsedValueName : nat
}.

Definition recognizeCompleteFrame
  (raw : PendingRawView)
  (valueName : nat)
  (extent : RecognitionExtent) : option ParsedWitness :=
  match checkCompleteExtent extent with
  | ExtentComplete =>
      Some (mkParsedWitness
        (rawPendingOwner raw)
        (rawGrammarId raw)
        (rawFrameId raw)
        valueName)
  | _ => None
  end.

Theorem successful_complete_recognition_has_exact_extent_and_provenance :
  forall raw valueName extent parsed,
    recognizeCompleteFrame raw valueName extent = Some parsed ->
    CompleteExtent extent /\
    parsedPendingOwner parsed = rawPendingOwner raw /\
    parsedGrammarId parsed = rawGrammarId raw /\
    parsedFrameId parsed = rawFrameId raw /\
    parsedValueName parsed = valueName.
Proof.
  intros raw valueName extent parsed Hsuccess.
  unfold recognizeCompleteFrame in Hsuccess.
  destruct (checkCompleteExtent extent) eqn:Hextent; try discriminate.
  inversion Hsuccess; subst parsed; clear Hsuccess.
  split.
  - exact ((proj1 (check_complete_extent_complete_iff extent)) Hextent).
  - repeat split; reflexivity.
Qed.

Theorem trailing_bytes_cannot_produce_success :
  forall raw valueName extent,
    checkCompleteExtent extent = ExtentTrailing ->
    recognizeCompleteFrame raw valueName extent = None.
Proof.
  intros raw valueName extent Hextent.
  unfold recognizeCompleteFrame.
  rewrite Hextent.
  reflexivity.
Qed.

Theorem consumed_past_frame_cannot_produce_success :
  forall raw valueName extent,
    checkCompleteExtent extent = ExtentPast ->
    recognizeCompleteFrame raw valueName extent = None.
Proof.
  intros raw valueName extent Hextent.
  unfold recognizeCompleteFrame.
  rewrite Hextent.
  reflexivity.
Qed.

Theorem invalid_extent_cannot_produce_success :
  forall raw valueName extent,
    checkCompleteExtent extent = ExtentInvalid ->
    recognizeCompleteFrame raw valueName extent = None.
Proof.
  intros raw valueName extent Hextent.
  unfold recognizeCompleteFrame.
  rewrite Hextent.
  reflexivity.
Qed.

Record RecognitionFailure : Type := mkRecognitionFailure {
  failurePendingOwner : nat;
  failureGrammarId : nat;
  failureFrameId : nat;
  failureDetail : nat
}.

Definition rejectMalformedCompleteFrame
  (raw : PendingRawView)
  (detail : nat)
  (extent : RecognitionExtent) : option RecognitionFailure :=
  match checkCompleteExtent extent with
  | ExtentComplete =>
      Some (mkRecognitionFailure
        (rawPendingOwner raw)
        (rawGrammarId raw)
        (rawFrameId raw)
        detail)
  | _ => None
  end.

Theorem malformed_complete_frame_failure_has_exact_provenance :
  forall raw detail extent failure,
    rejectMalformedCompleteFrame raw detail extent = Some failure ->
    CompleteExtent extent /\
    failurePendingOwner failure = rawPendingOwner raw /\
    failureGrammarId failure = rawGrammarId raw /\
    failureFrameId failure = rawFrameId raw /\
    failureDetail failure = detail.
Proof.
  intros raw detail extent failure Hfailure.
  unfold rejectMalformedCompleteFrame in Hfailure.
  destruct (checkCompleteExtent extent) eqn:Hextent; try discriminate.
  inversion Hfailure; subst failure; clear Hfailure.
  split.
  - exact ((proj1 (check_complete_extent_complete_iff extent)) Hextent).
  - repeat split; reflexivity.
Qed.

Record FailedPendingFinalization : Type := mkFailedPendingFinalization {
  finalizedFailure : RecognitionFailure;
  finalizedPendingConsumed : bool;
  finalizedSuccessor : option nat
}.

Definition finalizeRecognitionFailure
  (failure : RecognitionFailure) : FailedPendingFinalization :=
  mkFailedPendingFinalization failure true None.

Theorem recognition_failure_creates_no_success_successor :
  forall failure,
    finalizedPendingConsumed (finalizeRecognitionFailure failure) = true /\
    finalizedSuccessor (finalizeRecognitionFailure failure) = None.
Proof.
  intro failure.
  split; reflexivity.
Qed.

Theorem malformed_complete_frame_creates_no_success_artifact :
  forall raw detail extent failure,
    rejectMalformedCompleteFrame raw detail extent = Some failure ->
    finalizedSuccessor (finalizeRecognitionFailure failure) = None.
Proof.
  intros raw detail extent failure Hfailure.
  reflexivity.
Qed.
