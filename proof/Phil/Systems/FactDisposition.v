From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  PHIL-SYS-FACT-001 — proof-oriented model of stage-fact disposition.

  The Haskell checker first rejects duplicate/empty fact IDs.  This model starts
  from the corresponding normalized partial map, so key uniqueness is
  structural.  Haskell's nonempty transferred-invariant list is normalized to
  one checked witness; additional invariants do not change the authority rule.
*)

Definition FactId := nat.
Definition RevisionId := nat.
Definition InvariantId := nat.
Definition AssuranceUseId := nat.
Definition EvidenceId := nat.

Inductive FactDisposition : Type :=
| FactConsumed
| FactTransferred : InvariantId -> FactDisposition
| FactErased : AssuranceUseId -> FactDisposition
| FactRuntimeRetained : EvidenceId -> FactDisposition
| FactDerived : RevisionId -> FactDisposition.

Record FactRecord : Type := mkFactRecord {
  factSourceRevision : option RevisionId;
  factDisposition : FactDisposition
}.

Definition FactEnvironment := FactId -> option FactRecord.
Definition FactSet := FactId -> bool.
Definition InvariantSet := InvariantId -> bool.
Definition UseSet := AssuranceUseId -> bool.
Definition EvidenceSet := EvidenceId -> bool.
Definition RevisionSet := RevisionId -> bool.

Record StageFactModel : Type := mkStageFactModel {
  trustedFacts : FactSet;
  stageFacts : FactEnvironment;
  factsRequiringTransfer : FactSet;
  checkedInvariants : InvariantSet;
  selectedUses : UseSet;
  selectedEvidence : EvidenceSet;
  selectedRevisions : RevisionSet;
  useRevision : AssuranceUseId -> option RevisionId;
  evidenceRevision : EvidenceId -> option RevisionId;
  loweringDecisionErasesUse : AssuranceUseId -> bool;
  programErasesUse : RevisionId -> AssuranceUseId -> bool
}.

Definition ExactFactCoverage (model : StageFactModel) : Prop :=
  forall factId,
    trustedFacts model factId = true <->
    exists record, stageFacts model factId = Some record.

Definition FactDispositionValid
  (model : StageFactModel)
  (factId : FactId)
  (record : FactRecord) : Prop :=
  match factDisposition record with
  | FactConsumed =>
      factsRequiringTransfer model factId = false
  | FactTransferred invariantId =>
      checkedInvariants model invariantId = true
  | FactErased useId =>
      exists revision,
        factSourceRevision record = Some revision /\
        selectedUses model useId = true /\
        useRevision model useId = Some revision /\
        loweringDecisionErasesUse model useId = true /\
        programErasesUse model revision useId = true
  | FactRuntimeRetained evidenceId =>
      selectedEvidence model evidenceId = true /\
      match factSourceRevision record with
      | Some revision => evidenceRevision model evidenceId = Some revision
      | None => True
      end
  | FactDerived revision =>
      selectedRevisions model revision = true
  end.

Definition StageFactVerificationSuccess (model : StageFactModel) : Prop :=
  ExactFactCoverage model /\
  stageFacts model 0 = None /\
  (forall factId record,
    stageFacts model factId = Some record ->
    FactDispositionValid model factId record).

Theorem verified_stage_covers_exact_trusted_fact_set :
  forall model,
    StageFactVerificationSuccess model ->
    ExactFactCoverage model.
Proof.
  intros model Hverified.
  destruct Hverified as [Hexact _].
  exact Hexact.
Qed.

Theorem verified_stage_has_no_empty_fact_identity :
  forall model,
    StageFactVerificationSuccess model ->
    stageFacts model 0 = None.
Proof.
  intros model Hverified.
  destruct Hverified as [_ [Hempty _]].
  exact Hempty.
Qed.

Theorem normalized_stage_fact_identity_is_unique :
  forall model factId left right,
    stageFacts model factId = Some left ->
    stageFacts model factId = Some right ->
    left = right.
Proof.
  intros model factId left right Hleft Hright.
  rewrite Hleft in Hright.
  inversion Hright.
  reflexivity.
Qed.

Theorem required_transfer_fact_cannot_be_consumed :
  forall model factId revision,
    StageFactVerificationSuccess model ->
    stageFacts model factId = Some (mkFactRecord revision FactConsumed) ->
    factsRequiringTransfer model factId = true ->
    False.
Proof.
  intros model factId revision Hverified Hlookup Hrequired.
  destruct Hverified as [_ [_ Hvalid]].
  pose proof (Hvalid factId (mkFactRecord revision FactConsumed) Hlookup) as Hdisposition.
  unfold FactDispositionValid in Hdisposition.
  simpl in Hdisposition.
  rewrite Hrequired in Hdisposition.
  discriminate.
Qed.

Theorem transferred_fact_has_checked_invariant :
  forall model factId revision invariantId,
    StageFactVerificationSuccess model ->
    stageFacts model factId =
      Some (mkFactRecord revision (FactTransferred invariantId)) ->
    checkedInvariants model invariantId = true.
Proof.
  intros model factId revision invariantId Hverified Hlookup.
  destruct Hverified as [_ [_ Hvalid]].
  pose proof (Hvalid factId
    (mkFactRecord revision (FactTransferred invariantId)) Hlookup) as Hdisposition.
  unfold FactDispositionValid in Hdisposition.
  simpl in Hdisposition.
  exact Hdisposition.
Qed.

Theorem erased_fact_requires_exact_selected_erasure_chain :
  forall model factId sourceRevision useId,
    StageFactVerificationSuccess model ->
    stageFacts model factId =
      Some (mkFactRecord sourceRevision (FactErased useId)) ->
    exists revision,
      sourceRevision = Some revision /\
      selectedUses model useId = true /\
      useRevision model useId = Some revision /\
      loweringDecisionErasesUse model useId = true /\
      programErasesUse model revision useId = true.
Proof.
  intros model factId sourceRevision useId Hverified Hlookup.
  destruct Hverified as [_ [_ Hvalid]].
  pose proof (Hvalid factId
    (mkFactRecord sourceRevision (FactErased useId)) Hlookup) as Hdisposition.
  unfold FactDispositionValid in Hdisposition.
  simpl in Hdisposition.
  exact Hdisposition.
Qed.

Theorem runtime_retained_fact_uses_selected_evidence :
  forall model factId sourceRevision evidenceId,
    StageFactVerificationSuccess model ->
    stageFacts model factId =
      Some (mkFactRecord sourceRevision (FactRuntimeRetained evidenceId)) ->
    selectedEvidence model evidenceId = true.
Proof.
  intros model factId sourceRevision evidenceId Hverified Hlookup.
  destruct Hverified as [_ [_ Hvalid]].
  pose proof (Hvalid factId
    (mkFactRecord sourceRevision (FactRuntimeRetained evidenceId)) Hlookup) as Hdisposition.
  unfold FactDispositionValid in Hdisposition.
  simpl in Hdisposition.
  destruct Hdisposition as [Hselected _].
  exact Hselected.
Qed.

Theorem runtime_retained_fact_preserves_revision_alignment :
  forall model factId revision evidenceId,
    StageFactVerificationSuccess model ->
    stageFacts model factId =
      Some (mkFactRecord (Some revision) (FactRuntimeRetained evidenceId)) ->
    evidenceRevision model evidenceId = Some revision.
Proof.
  intros model factId revision evidenceId Hverified Hlookup.
  destruct Hverified as [_ [_ Hvalid]].
  pose proof (Hvalid factId
    (mkFactRecord (Some revision) (FactRuntimeRetained evidenceId)) Hlookup) as Hdisposition.
  unfold FactDispositionValid in Hdisposition.
  simpl in Hdisposition.
  destruct Hdisposition as [_ Haligned].
  exact Haligned.
Qed.

Theorem derived_fact_names_selected_obligation :
  forall model factId sourceRevision revision,
    StageFactVerificationSuccess model ->
    stageFacts model factId =
      Some (mkFactRecord sourceRevision (FactDerived revision)) ->
    selectedRevisions model revision = true.
Proof.
  intros model factId sourceRevision revision Hverified Hlookup.
  destruct Hverified as [_ [_ Hvalid]].
  pose proof (Hvalid factId
    (mkFactRecord sourceRevision (FactDerived revision)) Hlookup) as Hdisposition.
  unfold FactDispositionValid in Hdisposition.
  simpl in Hdisposition.
  exact Hdisposition.
Qed.

(* ADR-011 erasure is allowed only when the disappearing representation has a
   surviving semantic carrier.  The Haskell verifier accepts either a checked
   transferred invariant or a selected derived obligation; this normalized
   model records one such witness. *)

Inductive ErasureCarrier : Type :=
| CarrierInvariant : InvariantId -> ErasureCarrier
| CarrierDerived : RevisionId -> ErasureCarrier.

Record EraseDecisionModel : Type := mkEraseDecisionModel {
  erasureCarrier : ErasureCarrier;
  erasureCheckedInvariant : InvariantSet;
  erasureSelectedRevision : RevisionSet
}.

Definition EraseDecisionVerificationSuccess
  (decision : EraseDecisionModel) : Prop :=
  match erasureCarrier decision with
  | CarrierInvariant invariantId =>
      erasureCheckedInvariant decision invariantId = true
  | CarrierDerived revision =>
      erasureSelectedRevision decision revision = true
  end.

Theorem verified_erasure_has_surviving_semantic_carrier :
  forall decision,
    EraseDecisionVerificationSuccess decision ->
    (exists invariantId,
      erasureCarrier decision = CarrierInvariant invariantId /\
      erasureCheckedInvariant decision invariantId = true) \/
    (exists revision,
      erasureCarrier decision = CarrierDerived revision /\
      erasureSelectedRevision decision revision = true).
Proof.
  intros decision Hverified.
  unfold EraseDecisionVerificationSuccess in Hverified.
  destruct (erasureCarrier decision) as [invariantId | revision] eqn:Hcarrier.
  - left.
    exists invariantId.
    split.
    + exact Hcarrier.
    + exact Hverified.
  - right.
    exists revision.
    split.
    + exact Hcarrier.
    + exact Hverified.
Qed.
