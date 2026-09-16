From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String Lia.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveBodyTransferRecursiveCarrierSpine
  GrammarAstSessionRecursiveBodyOneStepCarrierTotality
  GrammarAstSessionRecursiveOneStepCarrierTotality
  GrammarAstSessionContinueMutualRecursiveTreeAdapter
  GrammarAstSessionMutualRecursiveClosureTotality
  GrammarAstSessionContinueMutualRecursiveClosureTotality
  GrammarAstSessionTransferRecursiveClosureTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for transfer-recursive propagation of one-level recursive-body
  refinement from #1121.

  The two body-adapter fuels are shared across the entire transfer chain, so
  this proof first closes their monotonicity and then combines local/deeper
  requirements with Nat.max.  Select/offer branch continuations remain outside
  this recursive closure.
*)

Lemma
  phase1_surface_normalize_mutual_recursive_session_tree_fuel_monotone_for_body :
  forall fuel larger tree refined,
    fuel <= larger ->
    phase1_surface_normalize_mutual_recursive_session_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_normalize_mutual_recursive_session_tree_fuel
      larger tree = Some refined.
Proof.
  intros fuel larger tree refined Hle Hnormalize.
  unfold phase1_surface_normalize_mutual_recursive_session_tree_fuel
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_choice_refined_recursive_session_tree_fuel
      fuel tree)
    as [step |] eqn:Hstep; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_choice_refined_recursive_session_tree_fuel_monotone
      fuel larger tree step Hle Hstep) as Hstep_larger.
  rewrite Hstep_larger.
  eapply phase1_surface_normalize_mutual_recursive_session_spine_fuel_monotone.
  - exact Hle.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels_monotone_for_body :
  forall source_fuel larger_source closure_fuel larger_closure tree refined,
    source_fuel <= larger_source ->
    closure_fuel <= larger_closure ->
    phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels
      source_fuel closure_fuel tree = Some refined ->
    phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels
      larger_source larger_closure tree = Some refined.
Proof.
  intros source_fuel larger_source closure_fuel larger_closure
    tree refined Hsource Hclosure Hnormalize.
  unfold phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels
    in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_mutual_recursive_session_tree_fuel
      source_fuel tree)
    as [mutual |] eqn:Hmutual; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_mutual_recursive_session_tree_fuel_monotone_for_body
      source_fuel larger_source tree mutual Hsource Hmutual)
    as Hmutual_larger.
  rewrite Hmutual_larger.
  destruct
    (phase1_surface_normalize_end_refined_recursive_session_spine mutual)
    as [end_refined |] eqn:Hend; try discriminate Hnormalize.
  rewrite Hend.
  destruct
    (phase1_surface_normalize_continue_transfer_recursive_session_spine
      end_refined)
    as [transfer_refined |] eqn:Htransfer; try discriminate Hnormalize.
  rewrite Htransfer.
  destruct
    (phase1_surface_normalize_continue_choice_one_step_session_spine
      transfer_refined)
    as [choice_refined |] eqn:Hchoice; try discriminate Hnormalize.
  rewrite Hchoice.
  eapply
    phase1_surface_normalize_continue_mutual_recursive_session_spine_fuel_monotone.
  - exact Hclosure.
  - exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_monotone :
  forall source_fuel larger_source closure_fuel larger_closure session refined,
    source_fuel <= larger_source ->
    closure_fuel <= larger_closure ->
    phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
      source_fuel closure_fuel session = Some refined ->
    phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
      larger_source larger_closure session = Some refined.
Proof.
  intros source_fuel larger_source closure_fuel larger_closure
    [nonreference | reference_tree] refined Hsource Hclosure Hnormalize.
  - destruct nonreference as
      [direction parameter boundary guard continuation
      |choice
      |choice
      |terminal
      |recursive_payload
      |payload].
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + destruct recursive_payload as [name body_tree].
      cbn in Hnormalize |- *.
      destruct
        (phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels
          source_fuel closure_fuel body_tree)
        as [body |] eqn:Hbody; try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      pose proof
        (phase1_surface_normalize_continue_mutual_recursive_session_tree_fuels_monotone_for_body
          source_fuel larger_source closure_fuel larger_closure
          body_tree body Hsource Hclosure Hbody)
        as Hbody_larger.
      rewrite Hbody_larger.
      reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_body_monotone :
  forall source_fuel larger_source closure_fuel larger_closure
    transfer_fuel session refined,
    source_fuel <= larger_source ->
    closure_fuel <= larger_closure ->
    phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
      source_fuel closure_fuel transfer_fuel session = Some refined ->
    phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
      larger_source larger_closure transfer_fuel session = Some refined.
Proof.
  induction transfer_fuel as [|remaining IH];
    intros session refined Hsource Hclosure Hnormalize.
  - discriminate Hnormalize.
  - cbn in Hnormalize |- *.
    assert (Hcontinuation :
      forall continuation converted,
        (match
          phase1_surface_normalize_recursive_one_step_session_spine continuation
        with
        | Some shell =>
            match
              phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
                source_fuel closure_fuel shell
            with
            | Some body_step =>
                phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
                  source_fuel closure_fuel remaining body_step
            | None => None
            end
        | None => None
        end) = Some converted ->
        (match
          phase1_surface_normalize_recursive_one_step_session_spine continuation
        with
        | Some shell =>
            match
              phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
                larger_source larger_closure shell
            with
            | Some body_step =>
                phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
                  larger_source larger_closure remaining body_step
            | None => None
            end
        | None => None
        end) = Some converted).
    {
      intros continuation converted Hconverted.
      destruct
        (phase1_surface_normalize_recursive_one_step_session_spine continuation)
        as [shell |] eqn:Hshell; try discriminate Hconverted.
      destruct
        (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
          source_fuel closure_fuel shell)
        as [body_step |] eqn:Hbody; try discriminate Hconverted.
      pose proof
        (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_monotone
          source_fuel larger_source closure_fuel larger_closure
          shell body_step Hsource Hclosure Hbody)
        as Hbody_larger.
      rewrite Hshell, Hbody_larger.
      eapply IH.
      - exact Hsource.
      - exact Hclosure.
      - exact Hconverted.
    }
    destruct session as [nonreference | reference_tree].
    + destruct nonreference as
        [direction parameter boundary guard continuation
        |choice
        |choice
        |terminal
        |payload
        |payload].
      * destruct
          (match
            phase1_surface_normalize_recursive_one_step_session_spine continuation
          with
          | Some shell =>
              match
                phase1_surface_normalize_recursive_body_one_step_session_spine_fuels
                  source_fuel closure_fuel shell
              with
              | Some body_step =>
                  phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
                    source_fuel closure_fuel remaining body_step
              | None => None
              end
          | None => None
          end)
          as [converted |] eqn:Hconverted; try discriminate Hnormalize.
        inversion Hnormalize; subst refined.
        rewrite (Hcontinuation continuation converted Hconverted).
        reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
      * inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined.
      reflexivity.
Qed.

Lemma
  phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_total_measure :
  forall measure path input rest session,
    List.length input < measure ->
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_recursive_body_one_step_session_spine_tree session) ->
    exists source_fuel closure_fuel transfer_fuel refined,
      phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
        source_fuel closure_fuel transfer_fuel session = Some refined.
Proof.
  induction measure as [|measure IH];
    intros path input rest session Hmeasure Hderive.
  - lia.
  - destruct session as [nonreference | reference_tree].
    + destruct nonreference as
        [direction parameter boundary guard continuation
        |choice
        |choice
        |terminal
        |payload
        |payload].
      * let transfer := constr:(
          {| phase1_guard_refined_transfer_direction := direction;
             phase1_guard_refined_transfer_parameter := parameter;
             phase1_guard_refined_transfer_boundary := boundary;
             phase1_guard_refined_transfer_guard := guard;
             phase1_guard_refined_transfer_continuation_tree :=
               phase1_surface_continue_mutual_recursive_session_spine_tree
                 continuation |}) in
        assert (Htransfer_tree :
          phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
            (Phase1GuardRefinedBoundaryTypedTransferNonreferenceSession
              (Phase1GuardRefinedBoundaryTypedTransferSession transfer)) =
          phase1_surface_recursive_body_one_step_session_spine_tree
            (Phase1RecursiveBodyOneStepNonreferenceSession
              (Phase1RecursiveBodyOneStepTransferSession
                direction parameter boundary guard continuation)))
          by reflexivity;
        destruct
          (phase1_surface_guard_refined_transfer_continuation_derivation_shorter
            path input rest
            (phase1_surface_recursive_body_one_step_session_spine_tree
              (Phase1RecursiveBodyOneStepNonreferenceSession
                (Phase1RecursiveBodyOneStepTransferSession
                  direction parameter boundary guard continuation)))
            transfer Hderive Htransfer_tree)
          as [continuation_path
            [continuation_input [continuation_rest
              [Hcontinuation Hshort]]]];
        destruct
          (phase1_surface_normalize_recursive_one_step_session_spine_total_from_derivation
            continuation_path continuation_input continuation_rest
            continuation Hcontinuation)
          as [shell Hshell];
        pose proof
          (phase1_surface_normalize_recursive_one_step_session_spine_round_trip
            continuation shell Hshell) as Hshell_tree;
        rewrite <- Hshell_tree in Hcontinuation;
        destruct
          (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_total_from_derivation
            continuation_path continuation_input continuation_rest
            shell Hcontinuation)
          as [body_source_fuel
            [body_closure_fuel [body_step Hbody]]];
        pose proof
          (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_round_trip
            body_source_fuel body_closure_fuel shell body_step Hbody)
          as Hbody_tree;
        rewrite <- Hbody_tree in Hcontinuation;
        assert (Hrecursive_measure :
          List.length continuation_input < measure) by lia;
        destruct
          (IH continuation_path continuation_input continuation_rest
            body_step Hrecursive_measure Hcontinuation)
          as [recursive_source_fuel
            [recursive_closure_fuel
              [recursive_transfer_fuel [converted Hrecursive]]]];
        let source_fuel :=
          constr:(Nat.max body_source_fuel recursive_source_fuel) in
        let closure_fuel :=
          constr:(Nat.max body_closure_fuel recursive_closure_fuel) in
        pose proof
          (phase1_surface_normalize_recursive_body_one_step_session_spine_fuels_monotone
            body_source_fuel source_fuel
            body_closure_fuel closure_fuel
            shell body_step
            (Nat.le_max_l body_source_fuel recursive_source_fuel)
            (Nat.le_max_l body_closure_fuel recursive_closure_fuel)
            Hbody)
          as Hbody_lifted;
        pose proof
          (phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_body_monotone
            recursive_source_fuel source_fuel
            recursive_closure_fuel closure_fuel
            recursive_transfer_fuel body_step converted
            (Nat.le_max_r body_source_fuel recursive_source_fuel)
            (Nat.le_max_r body_closure_fuel recursive_closure_fuel)
            Hrecursive)
          as Hrecursive_lifted;
        exists source_fuel, closure_fuel, (S recursive_transfer_fuel), converted;
        cbn [phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels];
        rewrite Hshell, Hbody_lifted;
        exact Hrecursive_lifted.
      * exists 0, 0, 1.
        eexists.
        reflexivity.
      * exists 0, 0, 1.
        eexists.
        reflexivity.
      * exists 0, 0, 1.
        eexists.
        reflexivity.
      * exists 0, 0, 1.
        eexists.
        reflexivity.
      * exists 0, 0, 1.
        eexists.
        reflexivity.
    + exists 0, 0, 1.
      eexists.
      reflexivity.
Qed.

Theorem
  phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_total_from_derivation :
  forall path input rest session,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_recursive_body_one_step_session_spine_tree session) ->
    exists source_fuel closure_fuel transfer_fuel refined,
      phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels
        source_fuel closure_fuel transfer_fuel session = Some refined /\
      phase1_surface_recursive_body_transfer_recursive_session_spine_tree
        refined =
      phase1_surface_recursive_body_one_step_session_spine_tree session.
Proof.
  intros path input rest session Hderive.
  destruct
    (phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_total_measure
      (S (List.length input)) path input rest session
      (Nat.lt_succ_diag_r (List.length input)) Hderive)
    as [source_fuel
      [closure_fuel [transfer_fuel [refined Hnormalize]]]].
  exists source_fuel, closure_fuel, transfer_fuel, refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_recursive_body_transfer_recursive_session_spine_fuels_round_trip.
    exact Hnormalize.
Qed.
