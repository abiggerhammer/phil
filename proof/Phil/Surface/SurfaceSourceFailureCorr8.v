From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax.
From Phil.Surface Require Import
  SurfaceFiniteContextFrame SurfaceFiniteMixedJoinCorr6 SurfaceFiniteTerminalJoinCorr7.

Module F := SurfaceFiniteContextFrame.
Module T := SurfaceFiniteTerminalJoinCorr7.

(*
  FSEM-01 CORR-8: first genuine source failure is terminal for a
  STATIC predecessor classifier, not a terminal success or Core.join error.
  Proofs are over finite model observations. The real checker/source producer
  and finite wire reflection are separate, explicitly bounded evidence.
*)

Lemma corr8_failure_after_clean_prefix :
  forall before reason after,
    T.firstSourceFailure before = None ->
    T.firstSourceFailure (before ++ T.Failed reason :: after) = Some reason.
Proof.
  induction before as [|head tail IH]; intros reason after Hclean; simpl in *.
  - reflexivity.
  - destruct head as [state | | earlier]; simpl in *.
    + apply IH; exact Hclean.
    + apply IH; exact Hclean.
    + discriminate.
Qed.

Theorem corr8_first_source_error_stops_before_join :
  forall typeEq before reason after,
    T.firstSourceFailure before = None ->
    T.replay typeEq (before ++ T.Failed reason :: after) =
      T.SourceRejected reason.
Proof.
  intros typeEq before reason after Hclean.
  unfold T.replay.
  now rewrite (corr8_failure_after_clean_prefix before reason after Hclean).
Qed.

Theorem corr8_no_successor_after_prejoin_failure :
  forall typeEq before reason after joined,
    T.firstSourceFailure before = None ->
    T.replay typeEq (before ++ T.Failed reason :: after) <>
      T.Joined joined.
Proof.
  intros typeEq before reason after joined Hclean.
  rewrite (corr8_first_source_error_stops_before_join
    typeEq before reason after Hclean).
  discriminate.
Qed.

Theorem corr8_left_failure_skips_sibling :
  forall typeEq reason state,
    T.replay typeEq [T.Failed reason; T.Continuing state] =
      T.SourceRejected reason.
Proof. reflexivity. Qed.

Theorem corr8_right_failure_discards_left_successor :
  forall typeEq state reason,
    T.replay typeEq [T.Continuing state; T.Failed reason] =
      T.SourceRejected reason.
Proof. reflexivity. Qed.

Definition closedState : F.FiniteSnapshot :=
  F.mkFiniteSnapshot [] [] [] [].

Theorem corr8_two_closed_continuations_join :
  T.replay (fun (_ _ : Syntax.Ty) => true)
    [T.Continuing closedState; T.Continuing closedState] =
      T.Joined closedState.
Proof. reflexivity. Qed.

Theorem corr8_error_is_not_terminal_completion :
  forall typeEq reason,
    T.replay typeEq [T.Failed reason] <> T.NoContinuation.
Proof. intros; discriminate. Qed.

Print Assumptions corr8_failure_after_clean_prefix.
Print Assumptions corr8_first_source_error_stops_before_join.
Print Assumptions corr8_no_successor_after_prejoin_failure.
Print Assumptions corr8_left_failure_skips_sibling.
Print Assumptions corr8_right_failure_discards_left_successor.
Print Assumptions corr8_two_closed_continuations_join.
Print Assumptions corr8_error_is_not_terminal_completion.
