From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionContinueMutualRecursiveTreeAdapter
  GrammarAstSessionEndRecursiveCarrierTotality
  GrammarAstSessionContinueTransferRecursiveCarrierTotality
  GrammarAstSessionContinueChoiceOneStepCarrierTotality
  GrammarAstSessionContinueMutualRecursiveClosureTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the raw-tree continue-mutual adapter from #1112. *)

Theorem
  phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest tree ->
    exists source_fuel closure_fuel refined,
      phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels
        source_fuel closure_fuel tree = Some refined /\
      phase1_surface_continue_mutual_recursive_session_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_mutual_recursive_session_tree_total_from_derivation
      path input rest tree Hderive)
    as [source_fuel [mutual [Hmutual Hmutual_tree]]].
  rewrite <- Hmutual_tree in Hderive.
  destruct
    (phase1_surface_normalize_end_refined_recursive_session_spine_total_from_derivation
      path input rest mutual Hderive)
    as [end_refined Hend].
  pose proof
    (phase1_surface_normalize_end_refined_recursive_session_spine_round_trip
      mutual end_refined Hend) as Hend_tree.
  rewrite <- Hend_tree in Hderive.
  destruct
    (phase1_surface_normalize_continue_transfer_recursive_session_spine_total_from_derivation
      path input rest end_refined Hderive)
    as [transfer_refined Htransfer].
  pose proof
    (phase1_surface_normalize_continue_transfer_recursive_session_spine_round_trip
      end_refined transfer_refined Htransfer) as Htransfer_tree.
  rewrite <- Htransfer_tree in Hderive.
  destruct
    (phase1_surface_normalize_continue_choice_one_step_session_spine_total_from_derivation
      path input rest transfer_refined Hderive)
    as [choice_refined Hchoice].
  pose proof
    (phase1_surface_normalize_continue_choice_one_step_session_spine_round_trip
      transfer_refined choice_refined Hchoice) as Hchoice_tree.
  rewrite <- Hchoice_tree in Hderive.
  destruct
    (phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel_total_from_derivation
      path input rest choice_refined Hderive)
    as [closure_fuel [refined [Hclosure Hclosure_tree]]].
  exists source_fuel, closure_fuel, refined.
  assert (Hresult :
    phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels
      source_fuel closure_fuel tree = Some refined).
  {
    unfold phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels.
    rewrite Hmutual, Hend, Htransfer, Hchoice.
    exact Hclosure.
  }
  split.
  - exact Hresult.
  - eapply
      phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels_round_trip.
    exact Hresult.
Qed.
