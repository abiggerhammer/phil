From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.

(*
  FSEM-01 J-1/J-2, NON-NORMATIVE conditional join relation.
  One checked Grammar-v1 if with two branches is projected to actual
  production Core resource contexts by a separate Haskell adapter.
  The following is the established ContextJoin model; no universal
  parser/Map/Text-to-Rocq or exact error-class theorem is claimed.
*)

Definition sourceContinuingInputs
    (predecessors : list (option Context.ResourceContext)) :
    list Context.ResourceContext :=
  flat_map (fun status =>
    match status with
    | Some context => [context]
    | None => []
    end) predecessors.

Theorem two_source_continuing_predecessors_remain_two :
  forall left right,
    sourceContinuingInputs [Some left; Some right] = [left; right].
Proof. intros; reflexivity. Qed.

Theorem terminal_left_predecessor_is_excluded :
  forall (terminated continuing : Context.ResourceContext),
    sourceContinuingInputs [None; Some continuing] = [continuing].
Proof. intros; reflexivity. Qed.

Theorem terminal_right_predecessor_is_excluded :
  forall (continuing terminated : Context.ResourceContext),
    sourceContinuingInputs [Some continuing; None] = [continuing].
Proof. intros; reflexivity. Qed.

Theorem both_terminal_predecessors_have_no_continuing_join :
  sourceContinuingInputs [None; None] = [].
Proof. reflexivity. Qed.

(* The existing successful ContextJoin relation requires identical
   unrestricted and linear maps across ALL continuing predecessors.
   A single owner absent from one and present in the other blocks it,
   regardless of the run-time Boolean branch choice. *)
Theorem changed_linear_owner_blocks_source_join :
  forall left right joined owner ty,
    Context.linearBindings left owner = Some ty ->
    Context.linearBindings right owner = None ->
    ~ ContextJoin.ContextJoinSuccess
        (sourceContinuingInputs [Some left; Some right]) joined.
Proof.
  intros left right joined owner ty Hleft Hright Hjoined.
  simpl in Hjoined.
  pose proof
    (ContextJoin.context_join_linear_converges
      [left; right] joined left Hjoined
      (or_introl eq_refl)) as HleftMap.
  pose proof
    (ContextJoin.context_join_linear_converges
      [left; right] joined right Hjoined
      (or_intror (or_introl eq_refl))) as HrightMap.
  unfold ContextJoin.SameBindingMap in HleftMap, HrightMap.
  specialize (HleftMap owner).
  specialize (HrightMap owner).
  rewrite Hleft in HleftMap.
  rewrite Hright in HrightMap.
  congruence.
Qed.

(* A terminal arm's consumed predecessor resources are NOT merged with
   a live continuing arm. This is a logical conditional about the modeled
   continuing relation, not a proof of the production path filter. *)
Theorem terminal_predecessor_does_not_change_live_linear_owner :
  forall (live joined : Context.ResourceContext) (owner : Syntax.Name),
    ContextJoin.ContextJoinSuccess
      (sourceContinuingInputs [None; Some live]) joined ->
    Context.linearBindings joined owner = Context.linearBindings live owner.
Proof.
  intros live joined owner Hjoin.
  simpl in Hjoin.
  pose proof
    (ContextJoin.context_join_linear_converges
      [live] joined live Hjoin (or_introl eq_refl)) as Hsame.
  unfold ContextJoin.SameBindingMap in Hsame.
  exact (Hsame owner).
Qed.

Theorem checked_source_join_closes_all_loans :
  forall left right joined,
    ContextJoin.ContextJoinSuccess
      (sourceContinuingInputs [Some left; Some right]) joined ->
    ContextJoin.NoLoans joined.
Proof.
  intros left right joined Hjoin.
  eapply ContextJoin.context_join_output_has_no_loans.
  exact Hjoin.
Qed.

Print Assumptions two_source_continuing_predecessors_remain_two.
Print Assumptions terminal_left_predecessor_is_excluded.
Print Assumptions terminal_right_predecessor_is_excluded.
Print Assumptions both_terminal_predecessors_have_no_continuing_join.
Print Assumptions changed_linear_owner_blocks_source_join.
Print Assumptions terminal_predecessor_does_not_change_live_linear_owner.
Print Assumptions checked_source_join_closes_all_loans.
