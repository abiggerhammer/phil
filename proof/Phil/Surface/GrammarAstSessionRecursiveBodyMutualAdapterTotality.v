From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveBodyMutualAdapter
  GrammarAstSessionRecursiveOneStepCarrierTotality
  GrammarAstSessionRecursiveBodyOneStepCarrierTotality
  GrammarAstSessionRecursiveBodyTransferRecursiveCarrierTotality
  GrammarAstSessionRecursiveBodyChoiceOneStepCarrierTotality
  GrammarAstSessionRecursiveBodyMutualRecursiveClosureTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the composed continue-mutual -> recursive-body-mutual adapter.

  Each refinement stage already has derivation-driven totality.  Their source,
  closure, and transfer fuels are combined componentwise with Nat.max and then
  lifted through the existing monotonicity lemmas.  No new recursive induction
  is introduced here.
*)

Theorem
  phase1_surface_normalize_recursive_body_mutual_adapter_fuels_total_from_derivation :
  forall path input rest session,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_continue_mutual_recursive_session_spine_tree session) ->
    exists source_fuel closure_fuel transfer_fuel mutual_fuel refined,
      phase1_surface_normalize_recursive_body_mutual_adapter_fuels
        source_fuel closure_fuel transfer_fuel mutual_fuel session =
        Some refined /\
      phase1_surface_recursive_body_mutual_recursive_session_spine_tree refined =
        phase1_surface_continue_mutual_recursive_session_spine_tree session.
Proof.
  intros path input rest session Hderive.
  destruct
    (phase1_surface_normalize_recursive_one_step_session_spine_total_from_derivation
      path input rest session Hderive)
    as [shell Hshell].
  pose proof
    (phase1_surface_normalize_recursive_one_step_session_spine_round_trip
      session shell Hshell) as Hshell_tree.
  rewrite <- Hshell_tree in Hderive.

  destruct
    (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_total_from_derivation
      path input rest shell Hderive)
    as [body_source_fuel [body_closure_fuel [body_step Hbody]]].
  pose proof
    (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_round_trip
      body_source_fuel body_closure_fuel shell body_step Hbody)
    as Hbody_tree.
  rewrite <- Hbody_tree in Hderive.

  destruct
    (phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_total_from_derivation
      path input rest body_step Hderive)
    as [transfer_source_fuel
      [transfer_closure_fuel
        [transfer_fuel
          [transfer_step [Htransfer Htransfer_tree]]]]].
  rewrite <- Htransfer_tree in Hderive.

  destruct
    (phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels_total_from_derivation
      path input rest transfer_step Hderive)
    as [choice_source_fuel
      [choice_closure_fuel
        [choice_transfer_fuel
          [choice_step [Hchoice Hchoice_tree]]]]].
  rewrite <- Hchoice_tree in Hderive.

  destruct
    (phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel_total_from_derivation
      path input rest choice_step Hderive)
    as [mutual_source_fuel
      [mutual_closure_fuel
        [mutual_transfer_fuel
          [mutual_fuel [refined [Hmutual Hmutual_tree]]]]]].

  let source_fuel :=
    constr:(Nat.max
      (Nat.max body_source_fuel transfer_source_fuel)
      (Nat.max choice_source_fuel mutual_source_fuel)) in
  let closure_fuel :=
    constr:(Nat.max
      (Nat.max body_closure_fuel transfer_closure_fuel)
      (Nat.max choice_closure_fuel mutual_closure_fuel)) in
  let final_transfer_fuel :=
    constr:(Nat.max transfer_fuel
      (Nat.max choice_transfer_fuel mutual_transfer_fuel)) in

  assert (Hbody_source_le : body_source_fuel <= source_fuel).
  {
    eapply Nat.le_trans.
    - apply Nat.le_max_l.
    - apply Nat.le_max_l.
  }
  assert (Htransfer_source_le : transfer_source_fuel <= source_fuel).
  {
    eapply Nat.le_trans.
    - apply Nat.le_max_r.
    - apply Nat.le_max_l.
  }
  assert (Hchoice_source_le : choice_source_fuel <= source_fuel).
  {
    eapply Nat.le_trans.
    - apply Nat.le_max_l.
    - apply Nat.le_max_r.
  }
  assert (Hmutual_source_le : mutual_source_fuel <= source_fuel).
  {
    eapply Nat.le_trans.
    - apply Nat.le_max_r.
    - apply Nat.le_max_r.
  }

  assert (Hbody_closure_le : body_closure_fuel <= closure_fuel).
  {
    eapply Nat.le_trans.
    - apply Nat.le_max_l.
    - apply Nat.le_max_l.
  }
  assert (Htransfer_closure_le : transfer_closure_fuel <= closure_fuel).
  {
    eapply Nat.le_trans.
    - apply Nat.le_max_r.
    - apply Nat.le_max_l.
  }
  assert (Hchoice_closure_le : choice_closure_fuel <= closure_fuel).
  {
    eapply Nat.le_trans.
    - apply Nat.le_max_l.
    - apply Nat.le_max_r.
  }
  assert (Hmutual_closure_le : mutual_closure_fuel <= closure_fuel).
  {
    eapply Nat.le_trans.
    - apply Nat.le_max_r.
    - apply Nat.le_max_r.
  }

  assert (Htransfer_fuel_le : transfer_fuel <= final_transfer_fuel).
  {
    apply Nat.le_max_l.
  }
  assert (Hchoice_transfer_le : choice_transfer_fuel <= final_transfer_fuel).
  {
    eapply Nat.le_trans.
    - apply Nat.le_max_l.
    - apply Nat.le_max_r.
  }
  assert (Hmutual_transfer_le : mutual_transfer_fuel <= final_transfer_fuel).
  {
    eapply Nat.le_trans.
    - apply Nat.le_max_r.
    - apply Nat.le_max_r.
  }

  pose proof
    (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_monotone
      body_source_fuel source_fuel
      body_closure_fuel closure_fuel
      shell body_step Hbody_source_le Hbody_closure_le Hbody)
    as Hbody_lifted.

  pose proof
    (phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_body_monotone
      transfer_source_fuel source_fuel
      transfer_closure_fuel closure_fuel
      transfer_fuel body_step transfer_step
      Htransfer_source_le Htransfer_closure_le Htransfer)
    as Htransfer_body_lifted.
  pose proof
    (phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_transfer_monotone
      source_fuel closure_fuel
      transfer_fuel final_transfer_fuel
      body_step transfer_step Htransfer_fuel_le Htransfer_body_lifted)
    as Htransfer_lifted.

  pose proof
    (phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels_monotone
      choice_source_fuel source_fuel
      choice_closure_fuel closure_fuel
      choice_transfer_fuel final_transfer_fuel
      transfer_step choice_step
      Hchoice_source_le Hchoice_closure_le Hchoice_transfer_le Hchoice)
    as Hchoice_lifted.

  pose proof
    (phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuels_monotone
      mutual_source_fuel source_fuel
      mutual_closure_fuel closure_fuel
      mutual_transfer_fuel final_transfer_fuel
      mutual_fuel mutual_fuel
      choice_step refined
      Hmutual_source_le Hmutual_closure_le Hmutual_transfer_le
      (Nat.le_refl mutual_fuel) Hmutual)
    as Hmutual_lifted.

  assert (Hresult :
    phase1_surface_normalize_recursive_body_mutual_adapter_fuels
      source_fuel closure_fuel final_transfer_fuel mutual_fuel session =
      Some refined).
  {
    unfold phase1_surface_normalize_recursive_body_mutual_adapter_fuels.
    rewrite Hshell, Hbody_lifted, Htransfer_lifted, Hchoice_lifted.
    exact Hmutual_lifted.
  }
  exists source_fuel, closure_fuel, final_transfer_fuel, mutual_fuel, refined.
  split.
  - exact Hresult.
  - eapply phase1_surface_normalize_recursive_body_mutual_adapter_fuels_round_trip.
    exact Hresult.
Qed.
