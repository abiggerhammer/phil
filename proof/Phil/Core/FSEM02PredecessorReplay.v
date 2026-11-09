From Stdlib Require Import Strings.String Bool.Bool.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice.
Open Scope string_scope.

(*
  Non-normative bounded owner-observation model. The native production gate
  replays full protocol/resource/owner state; this abstract finite observation
  is not a general Haskell-to-Rocq refinement or source authority theorem.
*)
Definition fsem02PredecessorOwnerObservation
  (replayed : option FSEM02OwnerLedger)
  (cached : FSEM02OwnerLedger) (occurrence : string) : bool :=
  match replayed with
  | None => false
  | Some expected =>
      match expected occurrence, cached occurrence with
      | None, None => true
      | Some (p, n), Some (q, m) => String.eqb p q && String.eqb n m
      | _, _ => false
      end
  end.

Theorem fsem02PredecessorRejectsFailedReplay :
  forall cached occurrence,
    fsem02PredecessorOwnerObservation None cached occurrence = false.
Proof. intros; reflexivity. Qed.

Theorem fsem02PredecessorObservedSuccessExact :
  forall expected cached occurrence,
    fsem02PredecessorOwnerObservation (Some expected) cached occurrence = true ->
    expected occurrence = cached occurrence.
Proof.
  intros expected cached occurrence H.
  unfold fsem02PredecessorOwnerObservation in H.
  destruct (expected occurrence) as [[p n]|] eqn:He;
  destruct (cached occurrence) as [[q m]|] eqn:Hc;
    try discriminate.
  - apply andb_true_iff in H as [Hp Hn].
    apply String.eqb_eq in Hp.
    apply String.eqb_eq in Hn.
    subst. now rewrite He, Hc.
  - now rewrite He, Hc.
Qed.

Theorem fsem02PredecessorRejectsInventedOwner :
  forall expected cached occurrence process name,
    expected occurrence = None ->
    cached occurrence = Some (process, name) ->
    fsem02PredecessorOwnerObservation (Some expected) cached occurrence = false.
Proof.
  intros expected cached occurrence process name He Hc.
  unfold fsem02PredecessorOwnerObservation.
  now rewrite He, Hc.
Qed.

Theorem fsem02PredecessorRejectsAlteredOwner :
  forall expected cached occurrence p n q m,
    expected occurrence = Some (p, n) ->
    cached occurrence = Some (q, m) ->
    (p <> q \/ n <> m) ->
    fsem02PredecessorOwnerObservation (Some expected) cached occurrence = false.
Proof.
  intros expected cached occurrence p n q m He Hc Hneq.
  unfold fsem02PredecessorOwnerObservation.
  rewrite He, Hc.
  destruct Hneq as [Hp|Hn].
  - apply String.eqb_neq in Hp. now rewrite Hp.
  - apply String.eqb_neq in Hn.
    rewrite Hn. destruct (String.eqb p q); reflexivity.
Qed.

Theorem fsem02PredecessorTwoObservedKeysExact :
  forall expected cached a b,
    fsem02PredecessorOwnerObservation (Some expected) cached a = true ->
    fsem02PredecessorOwnerObservation (Some expected) cached b = true ->
    expected a = cached a /\ expected b = cached b.
Proof.
  intros expected cached a b Ha Hb.
  split; apply fsem02PredecessorObservedSuccessExact; assumption.
Qed.
