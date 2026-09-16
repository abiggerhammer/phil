From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionMutualRecursiveClosureTotality
  GrammarAstSessionEndRecursiveCarrierSpine
  GrammarAstSessionContinueTransferRecursiveCarrierSpine
  GrammarAstSessionContinueChoiceOneStepCarrierSpine
  GrammarAstSessionContinueMutualRecursiveClosureSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Compose the already-closed session refinement stages into a raw-tree adapter.

  This is forward/lossless only.  The two fuel parameters belong to the older
  raw-tree mutual-recursion normalizer and the newer continue-mutual recursive
  closure respectively.  Existence of sufficient fuel is a successor theorem.
*)

Definition phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels
  (source_fuel closure_fuel : nat)
  (tree : ParseTree)
  : option Phase1SurfaceContinueMutualRecursiveSessionSpine :=
  match phase1_surface_normalize_mutual_recursive_session_tree_fuel
          source_fuel tree with
  | Some mutual =>
      match phase1_surface_normalize_end_refined_recursive_session_spine mutual with
      | Some end_refined =>
          match
            phase1_surface_normalize_continue_transfer_recursive_session_spine
              end_refined
          with
          | Some transfer_refined =>
              match
                phase1_surface_normalize_continue_choice_one_step_session_spine
                  transfer_refined
              with
              | Some choice_refined =>
                  phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel
                    closure_fuel choice_refined
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem
  phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels_round_trip :
  forall source_fuel closure_fuel tree refined,
    phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels
      source_fuel closure_fuel tree = Some refined ->
    phase1_surface_continue_mutual_recursive_session_spine_tree refined = tree.
Proof.
  intros source_fuel closure_fuel tree refined Hnormalize.
  unfold phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels
    in Hnormalize.
  destruct
    (phase1_surface_normalize_mutual_recursive_session_tree_fuel
      source_fuel tree)
    as [mutual |] eqn:Hmutual; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_end_refined_recursive_session_spine mutual)
    as [end_refined |] eqn:Hend; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_continue_transfer_recursive_session_spine
      end_refined)
    as [transfer_refined |] eqn:Htransfer; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_continue_choice_one_step_session_spine
      transfer_refined)
    as [choice_refined |] eqn:Hchoice; try discriminate Hnormalize.
  transitivity
    (phase1_surface_continue_choice_one_step_session_spine_tree choice_refined).
  - eapply
      phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel_round_trip.
    exact Hnormalize.
  - transitivity
      (phase1_surface_continue_transfer_recursive_session_spine_tree
        transfer_refined).
    + eapply
        phase1_surface_normalize_continue_choice_one_step_session_spine_round_trip.
      exact Hchoice.
    + transitivity
        (phase1_surface_end_refined_recursive_session_spine_tree end_refined).
      * eapply
          phase1_surface_normalize_continue_transfer_recursive_session_spine_round_trip.
        exact Htransfer.
      * transitivity
          (phase1_surface_mutual_recursive_session_spine_tree mutual).
        -- eapply
            phase1_surface_normalize_end_refined_recursive_session_spine_round_trip.
           exact Hend.
        -- eapply
            phase1_surface_normalize_mutual_recursive_session_tree_fuel_round_trip.
           exact Hmutual.
Qed.
