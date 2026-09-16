From Stdlib Require Import Arith.PeanoNat.

(*
  PHIL-P1-IO-BYTES-001 — runtime-sized and exact-length Bytes form one
  semantic family.

  This proof owns the semantic relation between bare runtime-sized Bytes and
  exact Bytes[n], including directional exact-index forgetting and checked
  runtime-to-exact refinement.  Generic resource ownership/transport machinery
  remains a predecessor boundary; the small ownership model below records only
  the linear one-use property that both Bytes views require.
*)

Inductive BytesIndex : Type :=
| RuntimeBytesIndex
| ExactBytesIndex (length : nat).

Inductive BytesMode : Type :=
| BytesLinear.

Definition bytesMode (_ : BytesIndex) : BytesMode := BytesLinear.

Record SemanticBytesValue : Type := mkSemanticBytesValue {
  semanticBytesIdentity : nat;
  semanticBytesRuntimeLength : nat
}.

Definition BytesValueHasType
  (value : SemanticBytesValue)
  (index : BytesIndex) : Prop :=
  match index with
  | RuntimeBytesIndex => True
  | ExactBytesIndex length => semanticBytesRuntimeLength value = length
  end.

(*
  Evidence truth/competence is imported from the ordinary proposition/evidence
  checker.  This obligation requires exact accepted length evidence but does not
  redefine what makes an evidence producer competent.
*)
Parameter AcceptedBytesLengthEvidence : SemanticBytesValue -> nat -> Prop.

Axiom accepted_bytes_length_evidence_sound :
  forall value length,
    AcceptedBytesLengthEvidence value length ->
    semanticBytesRuntimeLength value = length.

Inductive CheckedBytesViewTransition
  : SemanticBytesValue -> BytesIndex -> BytesIndex -> Prop :=
| CheckedBytesViewSame :
    forall value index,
      BytesValueHasType value index ->
      CheckedBytesViewTransition value index index
| CheckedBytesForgetExactIndex :
    forall value length,
      BytesValueHasType value (ExactBytesIndex length) ->
      CheckedBytesViewTransition
        value (ExactBytesIndex length) RuntimeBytesIndex
| CheckedBytesRefineRuntimeIndex :
    forall value length,
      AcceptedBytesLengthEvidence value length ->
      CheckedBytesViewTransition
        value RuntimeBytesIndex (ExactBytesIndex length).

Theorem every_bytes_family_member_is_linear :
  forall index,
    bytesMode index = BytesLinear.
Proof.
  intros index.
  reflexivity.
Qed.

Theorem runtime_bytes_carries_no_exact_length_requirement :
  forall value,
    BytesValueHasType value RuntimeBytesIndex.
Proof.
  intros value.
  simpl.
  exact I.
Qed.

Theorem exact_bytes_implies_runtime_bytes :
  forall value length,
    BytesValueHasType value (ExactBytesIndex length) ->
    BytesValueHasType value RuntimeBytesIndex.
Proof.
  intros value length Htyped.
  simpl.
  exact I.
Qed.

Theorem exact_index_forgetting_needs_no_length_evidence :
  forall value length,
    BytesValueHasType value (ExactBytesIndex length) ->
    CheckedBytesViewTransition
      value (ExactBytesIndex length) RuntimeBytesIndex.
Proof.
  intros value length Htyped.
  apply CheckedBytesForgetExactIndex.
  exact Htyped.
Qed.

Theorem exact_index_forgetting_preserves_value_identity :
  forall value length,
    BytesValueHasType value (ExactBytesIndex length) ->
    CheckedBytesViewTransition
      value (ExactBytesIndex length) RuntimeBytesIndex /\
    semanticBytesIdentity value = semanticBytesIdentity value.
Proof.
  intros value length Htyped.
  split.
  - apply CheckedBytesForgetExactIndex.
    exact Htyped.
  - reflexivity.
Qed.

Theorem accepted_length_evidence_refines_runtime_bytes :
  forall value length,
    AcceptedBytesLengthEvidence value length ->
    CheckedBytesViewTransition
      value RuntimeBytesIndex (ExactBytesIndex length).
Proof.
  intros value length Hevidence.
  apply CheckedBytesRefineRuntimeIndex.
  exact Hevidence.
Qed.

Theorem runtime_to_exact_requires_accepted_length_evidence :
  forall value length,
    CheckedBytesViewTransition
      value RuntimeBytesIndex (ExactBytesIndex length) ->
    AcceptedBytesLengthEvidence value length.
Proof.
  intros value length Htransition.
  inversion Htransition; subst; assumption.
Qed.

Theorem accepted_runtime_refinement_has_exact_length :
  forall value length,
    CheckedBytesViewTransition
      value RuntimeBytesIndex (ExactBytesIndex length) ->
    semanticBytesRuntimeLength value = length.
Proof.
  intros value length Htransition.
  apply accepted_bytes_length_evidence_sound.
  eapply runtime_to_exact_requires_accepted_length_evidence.
  exact Htransition.
Qed.

Theorem wrong_runtime_length_cannot_refine_to_exact_bytes :
  forall value length,
    semanticBytesRuntimeLength value <> length ->
    ~ CheckedBytesViewTransition
        value RuntimeBytesIndex (ExactBytesIndex length).
Proof.
  intros value length Hwrong Htransition.
  apply Hwrong.
  eapply accepted_runtime_refinement_has_exact_length.
  exact Htransition.
Qed.

Theorem runtime_refinement_preserves_value_identity :
  forall value length,
    AcceptedBytesLengthEvidence value length ->
    CheckedBytesViewTransition
      value RuntimeBytesIndex (ExactBytesIndex length) /\
    semanticBytesIdentity value = semanticBytesIdentity value.
Proof.
  intros value length Hevidence.
  split.
  - apply CheckedBytesRefineRuntimeIndex.
    exact Hevidence.
  - reflexivity.
Qed.

(* Minimal linear-ownership model for the Bytes family. *)
Inductive BytesOwnerState : Type :=
| BytesOwnerLive
| BytesOwnerConsumed.

Inductive ConsumeBytesOwner : BytesOwnerState -> BytesOwnerState -> Prop :=
| ConsumeBytesOwnerOnce :
    ConsumeBytesOwner BytesOwnerLive BytesOwnerConsumed.

Definition BytesOwnerComplete (state : BytesOwnerState) : Prop :=
  state = BytesOwnerConsumed.

Theorem linear_bytes_cannot_be_consumed_twice :
  forall middle final,
    ConsumeBytesOwner BytesOwnerLive middle ->
    ~ ConsumeBytesOwner middle final.
Proof.
  intros middle final Hfirst Hsecond.
  inversion Hfirst; subst.
  inversion Hsecond.
Qed.

Theorem live_bytes_owner_cannot_be_silently_dropped :
  ~ BytesOwnerComplete BytesOwnerLive.
Proof.
  unfold BytesOwnerComplete.
  discriminate.
Qed.

Definition CheckedBytesUse
  (value : SemanticBytesValue)
  (source target : BytesIndex)
  (before after : BytesOwnerState) : Prop :=
  CheckedBytesViewTransition value source target /\
  ConsumeBytesOwner before after.

Theorem exact_index_forgetting_consumes_same_linear_owner_once :
  forall value length,
    BytesValueHasType value (ExactBytesIndex length) ->
    CheckedBytesUse
      value
      (ExactBytesIndex length)
      RuntimeBytesIndex
      BytesOwnerLive
      BytesOwnerConsumed.
Proof.
  intros value length Htyped.
  unfold CheckedBytesUse.
  split.
  - apply CheckedBytesForgetExactIndex.
    exact Htyped.
  - constructor.
Qed.

Theorem runtime_refinement_consumes_same_linear_owner_once :
  forall value length,
    AcceptedBytesLengthEvidence value length ->
    CheckedBytesUse
      value
      RuntimeBytesIndex
      (ExactBytesIndex length)
      BytesOwnerLive
      BytesOwnerConsumed.
Proof.
  intros value length Hevidence.
  unfold CheckedBytesUse.
  split.
  - apply CheckedBytesRefineRuntimeIndex.
    exact Hevidence.
  - constructor.
Qed.
