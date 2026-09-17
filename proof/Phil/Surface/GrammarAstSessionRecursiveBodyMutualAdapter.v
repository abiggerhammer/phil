From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveOneStepCarrierSpine
  GrammarAstSessionRecursiveBodyOneStepCarrierSpine
  GrammarAstSessionRecursiveBodyTransferRecursiveCarrierSpine
  GrammarAstSessionRecursiveBodyChoiceOneStepCarrierSpine
  GrammarAstSessionRecursiveBodyMutualRecursiveClosureSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Compose the already-closed recursive-body refinement stages from the
  continue-mutual session carrier to the recursive-body mutual carrier.

  This adapter is forward/lossless only.  Its four fuels belong to the
  one-level body adapter, transfer recursion, and mutual transfer/choice
  recursion that have already been proved independently.  Keeping this
  composition explicit prevents the later transitive recursive-body normalizer
  from hiding those unrelated stages inside its recursive-body case.
*)

Definition phase1_surface_normalize_recursive_body_mutual_adapter_fuels
  (body_source_fuel body_closure_fuel transfer_fuel mutual_fuel : nat)
  (session : Phase1SurfaceContinueMutualRecursiveSessionSpine)
  : option Phase1SurfaceRecursiveBodyMutualRecursiveSessionSpine :=
  match phase1_surface_normalize_recursive_one_step_session_spine session with
  | Some shell =>
      match
        phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
          body_source_fuel body_closure_fuel shell
      with
      | Some body_step =>
          match
            phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
              body_source_fuel body_closure_fuel transfer_fuel body_step
          with
          | Some transfer_step =>
              match
                phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
                  body_source_fuel body_closure_fuel transfer_fuel transfer_step
              with
              | Some choice_step =>
                  phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel
                    body_source_fuel body_closure_fuel transfer_fuel mutual_fuel
                    choice_step
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_recursive_body_mutual_adapter_fuels_round_trip :
  forall body_source_fuel body_closure_fuel transfer_fuel mutual_fuel
    session refined,
    phase1_surface_normalize_recursive_body_mutual_adapter_fuels
      body_source_fuel body_closure_fuel transfer_fuel mutual_fuel session =
      Some refined ->
    phase1_surface_recursive_body_mutual_recursive_session_spine_tree refined =
      phase1_surface_continue_mutual_recursive_session_spine_tree session.
Proof.
  intros body_source_fuel body_closure_fuel transfer_fuel mutual_fuel
    session refined Hnormalize.
  unfold phase1_surface_normalize_recursive_body_mutual_adapter_fuels
    in Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_one_step_session_spine session)
    as [shell |] eqn:Hshell; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
      body_source_fuel body_closure_fuel shell)
    as [body_step |] eqn:Hbody; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
      body_source_fuel body_closure_fuel transfer_fuel body_step)
    as [transfer_step |] eqn:Htransfer; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels
      body_source_fuel body_closure_fuel transfer_fuel transfer_step)
    as [choice_step |] eqn:Hchoice; try discriminate Hnormalize.
  transitivity
    (phase1_surface_recursive_body_choice_one_step_session_spine_tree
      choice_step).
  - eapply
      phase1_surface_normalize_recursive_body_mutual_recursive_session_spine_fuel_round_trip.
    exact Hnormalize.
  - transitivity
      (phase1_surface_recursive_body_transfer_recursive_session_spine_tree
        transfer_step).
    + eapply
        phase1_surface_normalize_recursive_body_choice_one_step_session_spine_fuels_round_trip.
      exact Hchoice.
    + transitivity
        (phase1_surface_recursive_body_one_step_session_spine_tree body_step).
      * eapply
          phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_round_trip.
        exact Htransfer.
      * transitivity
          (phase1_surface_recursive_one_step_session_spine_tree shell).
        -- eapply
            phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_round_trip.
           exact Hbody.
        -- eapply
            phase1_surface_normalize_recursive_one_step_session_spine_round_trip.
           exact Hshell.
Qed.
