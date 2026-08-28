From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin ProcessJoin.

(*
  PHIL-RES-OBL-001 — unresolved obligations cannot be laundered away by
  reconvergence.

  ProcessJoin.v already proves the crucial lower-layer fact: joinBranches may
  normalize the ResourceContext of a Continue path, but it preserves the entire
  opaque non-resource checker-state payload exactly.  Residual obligations live
  in that payload in the Haskell checker.  This proof therefore models only the
  obligation-status observation over StatePayload and derives non-laundering
  directly from the certified process-join theorem.

  Discharge, runtime binding, permitted assumption, and permitted export are
  explicit semantic events owned by their existing boundary/evidence rules.
  They are represented below only as distinct recorded statuses.  Reconvergence
  itself cannot manufacture any of them, because it cannot change StatePayload.
*)

Definition ObligationId : Type := nat.

Inductive ObligationStatus : Type :=
| ObligationPending
| ObligationDischarged
| ObligationRuntimeBound
| ObligationAssumed
| ObligationExported.

Parameter obligationStatus : StatePayload -> ObligationId -> ObligationStatus.

Definition PendingObligation
  (payload : StatePayload)
  (obligation : ObligationId) : Prop :=
  obligationStatus payload obligation = ObligationPending.

Inductive ExplicitDisposition : ObligationStatus -> Prop :=
| ExplicitlyDischarged : ExplicitDisposition ObligationDischarged
| ExplicitlyRuntimeBound : ExplicitDisposition ObligationRuntimeBound
| ExplicitlyAssumed : ExplicitDisposition ObligationAssumed
| ExplicitlyExported : ExplicitDisposition ObligationExported.

Theorem pending_has_no_explicit_disposition :
  forall payload obligation,
    PendingObligation payload obligation ->
    ~ ExplicitDisposition (obligationStatus payload obligation).
Proof.
  intros payload obligation Hpending Hdisposition.
  unfold PendingObligation in Hpending.
  rewrite Hpending in Hdisposition.
  inversion Hdisposition.
Qed.

(*
  A successful reconvergence preserves the exact obligation status attached to
  every original continuing path.  The only mutated field is its ResourceContext.
*)
Theorem reconvergence_preserves_exact_obligation_status :
  forall flows output path obligation,
    ProcessJoinSuccess flows output ->
    In path (flattenBranches flows) ->
    joinControl path = Continue ->
    exists joined,
      ContextJoinSuccess (continuingContexts (flattenBranches flows)) joined /\
      In (normalizeContinue joined path) output /\
      obligationStatus
        (joinPayload (joinState (normalizeContinue joined path))) obligation =
      obligationStatus (joinPayload (joinState path)) obligation.
Proof.
  intros flows output path obligation Hjoin Hin Hcontinue.
  destruct
    (process_join_normalizes_every_continue
      flows output path Hjoin Hin Hcontinue)
    as [joined [Hcontext [Hinout [Hcontrol [Hresources Hpayload]]]]].
  exists joined.
  split.
  - exact Hcontext.
  - split.
    + exact Hinout.
    + rewrite Hpayload.
      reflexivity.
Qed.

(*
  If an obligation was still pending on a continuing predecessor, it remains
  represented as pending on that exact continuing path after the join.
*)
Theorem pending_obligation_survives_reconvergence :
  forall flows output path obligation,
    ProcessJoinSuccess flows output ->
    In path (flattenBranches flows) ->
    joinControl path = Continue ->
    PendingObligation (joinPayload (joinState path)) obligation ->
    exists joined,
      In (normalizeContinue joined path) output /\
      PendingObligation
        (joinPayload (joinState (normalizeContinue joined path))) obligation.
Proof.
  intros flows output path obligation Hjoin Hin Hcontinue Hpending.
  destruct
    (reconvergence_preserves_exact_obligation_status
      flows output path obligation Hjoin Hin Hcontinue)
    as [joined [Hcontext [Hinout Hstatus]]].
  exists joined.
  split.
  - exact Hinout.
  - unfold PendingObligation in *.
    rewrite Hstatus.
    exact Hpending.
Qed.

(*
  A join cannot silently reclassify a pending obligation as discharged,
  runtime-bound, assumed, or exported.  Any such disposition must therefore be
  established by some semantic event outside reconvergence itself.
*)
Theorem reconvergence_cannot_fabricate_explicit_disposition :
  forall flows output path obligation,
    ProcessJoinSuccess flows output ->
    In path (flattenBranches flows) ->
    joinControl path = Continue ->
    PendingObligation (joinPayload (joinState path)) obligation ->
    exists joined,
      In (normalizeContinue joined path) output /\
      ~ ExplicitDisposition
          (obligationStatus
            (joinPayload (joinState (normalizeContinue joined path)))
            obligation).
Proof.
  intros flows output path obligation Hjoin Hin Hcontinue Hpending.
  destruct
    (pending_obligation_survives_reconvergence
      flows output path obligation Hjoin Hin Hcontinue Hpending)
    as [joined [Hinout Hpendingout]].
  exists joined.
  split.
  - exact Hinout.
  - eapply pending_has_no_explicit_disposition.
    exact Hpendingout.
Qed.

(*
  Repeated reconvergence — including the loop-like case in which a continuing
  path is fed through another join — preserves the same pending obligation.
*)
Theorem pending_obligation_survives_repeated_reconvergence :
  forall flows firstOutput secondOutput path obligation,
    ProcessJoinSuccess flows firstOutput ->
    ProcessJoinSuccess [firstOutput] secondOutput ->
    In path (flattenBranches flows) ->
    joinControl path = Continue ->
    PendingObligation (joinPayload (joinState path)) obligation ->
    exists joinedFirst joinedSecond,
      In (normalizeContinue joinedFirst path) firstOutput /\
      In
        (normalizeContinue joinedSecond (normalizeContinue joinedFirst path))
        secondOutput /\
      PendingObligation
        (joinPayload
          (joinState
            (normalizeContinue joinedSecond
              (normalizeContinue joinedFirst path))))
        obligation.
Proof.
  intros flows firstOutput secondOutput path obligation
    Hfirst Hsecond Hin Hcontinue Hpending.
  destruct
    (pending_obligation_survives_reconvergence
      flows firstOutput path obligation Hfirst Hin Hcontinue Hpending)
    as [joinedFirst [HinFirst HpendingFirst]].
  pose proof
    (normalize_continuing_exact joinedFirst path Hcontinue)
    as HnormalizedFirst.
  destruct HnormalizedFirst as
    [HcontinueFirst [HresourcesFirst HpayloadFirst]].
  assert
    (HinFirstFlattened :
      In (normalizeContinue joinedFirst path) (flattenBranches [firstOutput])).
  {
    simpl.
    exact HinFirst.
  }
  destruct
    (pending_obligation_survives_reconvergence
      [firstOutput]
      secondOutput
      (normalizeContinue joinedFirst path)
      obligation
      Hsecond
      HinFirstFlattened
      HcontinueFirst
      HpendingFirst)
    as [joinedSecond [HinSecond HpendingSecond]].
  exists joinedFirst, joinedSecond.
  repeat split; assumption.
Qed.
