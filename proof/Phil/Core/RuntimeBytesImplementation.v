From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import RuntimeBytes.

(*
  PHIL-P1-IO-BYTES-001 — executable implementation correspondence.

  Production computes concrete type/equality/visibility/evidence facts.  This
  file owns only the ordered Bytes-family decisions reflected by Phil.Core.Value:

    1. exact-index forgetting wins before ordinary type comparison;
    2. otherwise definitional equality accepts;
    3. otherwise another Bytes-family member requires explicit transport;
    4. otherwise the types are incompatible;

  and for runtime Bytes -> Bytes[n] transport:

    1. source must be runtime-sized Bytes;
    2. target must be exact Bytes[n];
    3. the value subject must be visible so len(value) can be named;
    4. exact accepted length evidence is required.
*)

Inductive BytesCheckDecision : Type :=
| BytesCheckAcceptedForgetting
| BytesCheckAcceptedDefinitionallyEqual
| BytesCheckRequiresExplicitTransport
| BytesCheckIncompatible.

Definition decideBytesCheckByFacts
  (lengthForgetting definitionallyEqual sameBytesFamily : bool)
  : BytesCheckDecision :=
  if lengthForgetting then
    BytesCheckAcceptedForgetting
  else if definitionallyEqual then
    BytesCheckAcceptedDefinitionallyEqual
  else if sameBytesFamily then
    BytesCheckRequiresExplicitTransport
  else
    BytesCheckIncompatible.

Definition bytesCheckDecisionAccepted (decision : BytesCheckDecision) : bool :=
  match decision with
  | BytesCheckAcceptedForgetting => true
  | BytesCheckAcceptedDefinitionallyEqual => true
  | _ => false
  end.

Definition bytesCheckAcceptanceFacts
  (lengthForgetting definitionallyEqual : bool) : bool :=
  orb lengthForgetting definitionallyEqual.

Theorem bytes_check_accept_iff_forgetting_or_definitional_equality :
  forall lengthForgetting definitionallyEqual sameBytesFamily,
    bytesCheckDecisionAccepted
      (decideBytesCheckByFacts
        lengthForgetting definitionallyEqual sameBytesFamily) = true <->
    bytesCheckAcceptanceFacts lengthForgetting definitionallyEqual = true.
Proof.
  intros lengthForgetting definitionallyEqual sameBytesFamily.
  destruct lengthForgetting, definitionallyEqual, sameBytesFamily;
    simpl; split; intro H; try reflexivity; discriminate H.
Qed.

Theorem exact_index_forgetting_precedes_type_comparison :
  forall definitionallyEqual sameBytesFamily,
    decideBytesCheckByFacts true definitionallyEqual sameBytesFamily =
      BytesCheckAcceptedForgetting.
Proof.
  reflexivity.
Qed.

Theorem definitional_equality_accepts_after_nonforgetting :
  forall sameBytesFamily,
    decideBytesCheckByFacts false true sameBytesFamily =
      BytesCheckAcceptedDefinitionallyEqual.
Proof.
  reflexivity.
Qed.

Theorem nondefinitional_bytes_family_change_requires_transport :
  decideBytesCheckByFacts false false true =
    BytesCheckRequiresExplicitTransport.
Proof.
  reflexivity.
Qed.

Theorem unrelated_nondefinitional_type_rejects :
  decideBytesCheckByFacts false false false = BytesCheckIncompatible.
Proof.
  reflexivity.
Qed.

Inductive RuntimeBytesRefinementDecision : Type :=
| RuntimeBytesRefinementAccepted
| RuntimeBytesRefinementSourceNotRuntime
| RuntimeBytesRefinementTargetNotExact
| RuntimeBytesRefinementSubjectNotVisible
| RuntimeBytesRefinementEvidenceRequired.

Definition decideRuntimeBytesRefinementByFacts
  (sourceIsRuntime targetIsExact subjectVisible lengthEvidenceAccepted : bool)
  : RuntimeBytesRefinementDecision :=
  if sourceIsRuntime then
    if targetIsExact then
      if subjectVisible then
        if lengthEvidenceAccepted then
          RuntimeBytesRefinementAccepted
        else
          RuntimeBytesRefinementEvidenceRequired
      else
        RuntimeBytesRefinementSubjectNotVisible
    else
      RuntimeBytesRefinementTargetNotExact
  else
    RuntimeBytesRefinementSourceNotRuntime.

Definition runtimeBytesRefinementDecisionAccepted
  (decision : RuntimeBytesRefinementDecision) : bool :=
  match decision with
  | RuntimeBytesRefinementAccepted => true
  | _ => false
  end.

Definition runtimeBytesRefinementFactsAccepted
  (sourceIsRuntime targetIsExact subjectVisible lengthEvidenceAccepted : bool)
  : bool :=
  andb sourceIsRuntime
    (andb targetIsExact
      (andb subjectVisible lengthEvidenceAccepted)).

Theorem runtime_bytes_refinement_accept_iff_all_facts :
  forall sourceIsRuntime targetIsExact subjectVisible lengthEvidenceAccepted,
    runtimeBytesRefinementDecisionAccepted
      (decideRuntimeBytesRefinementByFacts
        sourceIsRuntime targetIsExact subjectVisible lengthEvidenceAccepted) = true <->
    runtimeBytesRefinementFactsAccepted
      sourceIsRuntime targetIsExact subjectVisible lengthEvidenceAccepted = true.
Proof.
  intros sourceIsRuntime targetIsExact subjectVisible lengthEvidenceAccepted.
  destruct sourceIsRuntime, targetIsExact, subjectVisible, lengthEvidenceAccepted;
    simpl; split; intro H; try reflexivity; discriminate H.
Qed.

Theorem nonruntime_source_rejects_first :
  forall targetIsExact subjectVisible lengthEvidenceAccepted,
    decideRuntimeBytesRefinementByFacts
      false targetIsExact subjectVisible lengthEvidenceAccepted =
      RuntimeBytesRefinementSourceNotRuntime.
Proof.
  reflexivity.
Qed.

Theorem nonexact_target_rejects_second :
  forall subjectVisible lengthEvidenceAccepted,
    decideRuntimeBytesRefinementByFacts
      true false subjectVisible lengthEvidenceAccepted =
      RuntimeBytesRefinementTargetNotExact.
Proof.
  reflexivity.
Qed.

Theorem invisible_runtime_bytes_subject_cannot_form_length_refinement :
  forall lengthEvidenceAccepted,
    decideRuntimeBytesRefinementByFacts true true false lengthEvidenceAccepted =
      RuntimeBytesRefinementSubjectNotVisible.
Proof.
  reflexivity.
Qed.

Theorem runtime_bytes_refinement_without_length_evidence_rejects :
  decideRuntimeBytesRefinementByFacts true true true false =
    RuntimeBytesRefinementEvidenceRequired.
Proof.
  reflexivity.
Qed.

Theorem runtime_bytes_refinement_with_exact_evidence_accepts :
  decideRuntimeBytesRefinementByFacts true true true true =
    RuntimeBytesRefinementAccepted.
Proof.
  reflexivity.
Qed.

Theorem forgetting_decision_constructs_semantic_transition :
  forall value length,
    BytesValueHasType value (ExactBytesIndex length) ->
    decideBytesCheckByFacts true false true =
      BytesCheckAcceptedForgetting ->
    CheckedBytesViewTransition
      value (ExactBytesIndex length) RuntimeBytesIndex.
Proof.
  intros value length Htyped Hdecision.
  apply CheckedBytesForgetExactIndex.
  exact Htyped.
Qed.

Theorem accepted_runtime_refinement_constructs_semantic_transition :
  forall value length,
    AcceptedBytesLengthEvidence value length ->
    decideRuntimeBytesRefinementByFacts true true true true =
      RuntimeBytesRefinementAccepted ->
    CheckedBytesViewTransition
      value RuntimeBytesIndex (ExactBytesIndex length).
Proof.
  intros value length Hevidence Hdecision.
  apply CheckedBytesRefineRuntimeIndex.
  exact Hevidence.
Qed.

Theorem accepted_runtime_refinement_preserves_linear_consumption :
  forall value length,
    AcceptedBytesLengthEvidence value length ->
    decideRuntimeBytesRefinementByFacts true true true true =
      RuntimeBytesRefinementAccepted ->
    CheckedBytesUse
      value
      RuntimeBytesIndex
      (ExactBytesIndex length)
      BytesOwnerLive
      BytesOwnerConsumed.
Proof.
  intros value length Hevidence Hdecision.
  unfold CheckedBytesUse.
  split.
  - apply CheckedBytesRefineRuntimeIndex.
    exact Hevidence.
  - constructor.
Qed.
