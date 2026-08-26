From Stdlib Require Import Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin ProcessJoin.

(*
  PHIL-PROC-JOIN-001 certification wrapper.

  The process-join semantic model landed with the Phase 1 control-state
  projection. These theorems reuse that model directly and add no alternate
  control or ResourceContext semantics.
*)

Theorem certified_process_join_nonempty_branch_set :
  forall flows output,
    ProcessJoinSuccess flows output ->
    flows <> [].
Proof.
  exact process_join_nonempty_branch_set.
Qed.

Theorem certified_process_join_preserves_path_count :
  forall flows output,
    ProcessJoinSuccess flows output ->
    length output = length (flattenBranches flows).
Proof.
  exact process_join_preserves_path_count.
Qed.

Theorem certified_process_join_preserves_noncontinuing :
  forall flows output path,
    ProcessJoinSuccess flows output ->
    In path (flattenBranches flows) ->
    joinControl path <> Continue ->
    In path output.
Proof.
  exact process_join_preserves_noncontinuing.
Qed.

Theorem certified_process_join_normalizes_every_continue :
  forall flows output path,
    ProcessJoinSuccess flows output ->
    In path (flattenBranches flows) ->
    joinControl path = Continue ->
    exists joined,
      ContextJoinSuccess (continuingContexts (flattenBranches flows)) joined /\
      In (normalizeContinue joined path) output /\
      joinControl (normalizeContinue joined path) = Continue /\
      joinResources (joinState (normalizeContinue joined path)) = joined /\
      joinPayload (joinState (normalizeContinue joined path)) =
        joinPayload (joinState path).
Proof.
  exact process_join_normalizes_every_continue.
Qed.
