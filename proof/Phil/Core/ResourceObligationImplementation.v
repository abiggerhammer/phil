From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ResourceObligation.

Inductive PendingObligationDecision : Type :=
| PendingObligationAcceptedDecision
| PendingObligationLostDecision.

Definition decidePendingObigationReconvergenceByFacts
  (pendingBefore pendingAfter : bool)
  : PendingObligationDecision :=
  if pendingBefore then
    if pendingAfter then
      PendingObligationAcceptedDecision
    else
      PendingObligationLostDecision
  else
    PendingObligationAcceptedDecision.

Theorem pending_obligation_decision_exact :
  forall pendingBefore pendingAfter,
    (decidePendingObigationReconvergenceByFacts pendingBefore pendingAfter =
       PendingObligationAcceptedDecision <->
     (pendingBefore = true -> pendingAfter = true)).
Proof.
  intros pendingBefore pendingAfter.
  destruct pendingBefore; destruct pendingAfter; simpl.
  - split.
    + intros _ _. reflexivity.
    + intros _. reflexivity.
  - split.
    + discriminate.
    + intro Hpreserved.
      specialize (Hpreserved eq_refl).
      discriminate.
  - split.
    + intros _ Hfalse. discriminate.
    + intros _. reflexivity.
  - split.
    + intros _ Hfalse. discriminate.
    + intros _. reflexivity.
Qed.

Theorem pending_obligation_decision_corresponds_reconvergence :
  forall payloadBefore payloadAfter obligation pendingBefore pendingAfter,
    (pendingBefore = true <-> PendingObligation payloadBefore obligation) ->
    (pendingAfter = true <-> PendingObligation payloadAfter obligation) ->
    (decidePendingObigationReconvergenceByFacts pendingBefore pendingAfter =
       PendingObligationAcceptedDecision <->
     (PendingObligation payloadBefore obligation ->
      PendingObligation payloadAfter obligation)).
Proof.
  intros payloadBefore payloadAfter obligation pendingBefore pendingAfter
    Hbefore Hafter.
  split.
  - intro Hdecision.
    pose proof
      ((proj1 (pending_obligation_decision_exact pendingBefore pendingAfter))
        Hdecision) as Hpreserved.
    intro HpendingBefore.
    apply (proj1 Hafter).
    apply Hpreserved.
    apply (proj2 Hbefore).
    exact HpendingBefore.
  - intro Hpreserved.
    apply (proj2 (pending_obligation_decision_exact pendingBefore pendingAfter)).
    intro HbeforeBool.
    apply (proj2 Hafter).
    apply Hpreserved.
    apply (proj1 Hbefore).
    exact HbeforeBool.
Qed.

Theorem accepted_pending_decision_cannot_fabricate_explicit_disposition :
  forall payloadBefore payloadAfter obligation pendingBefore pendingAfter,
    (pendingBefore = true <-> PendingObligation payloadBefore obligation) ->
    (pendingAfter = true <-> PendingObligation payloadAfter obligation) ->
    decidePendingObigationReconvergenceByFacts pendingBefore pendingAfter =
      PendingObligationAcceptedDecision ->
    PendingObligation payloadBefore obligation ->
    ~ ExplicitDisposition (obligationStatus payloadAfter obligation).
Proof.
  intros payloadBefore payloadAfter obligation pendingBefore pendingAfter
    Hbefore Hafter Hdecision HpendingBefore.
  apply pending_has_no_explicit_disposition.
  apply
    ((proj1
      (pending_obligation_decision_corresponds_reconvergence
        payloadBefore payloadAfter obligation pendingBefore pendingAfter
        Hbefore Hafter)) Hdecision).
  exact HpendingBefore.
Qed.

Theorem pending_obligation_decision_composes :
  forall before middle after,
    decidePendingObigationReconvergenceByFacts before middle =
      PendingObligationAcceptedDecision ->
    decidePendingObigationReconvergenceByFacts middle after =
      PendingObligationAcceptedDecision ->
    before = true ->
    after = true.
Proof.
  intros before middle after Hfirst Hsecond Hbefore.
  pose proof
    ((proj1 (pending_obligation_decision_exact before middle)) Hfirst)
    as HfirstPreserved.
  pose proof
    ((proj1 (pending_obligation_decision_exact middle after)) Hsecond)
    as HsecondPreserved.
  apply HsecondPreserved.
  apply HfirstPreserved.
  exact Hbefore.
Qed.
