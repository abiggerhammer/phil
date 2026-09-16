From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionContinueTransferRecursiveCarrierSpine
  GrammarAstSessionContinueOneStepCarrierTotality
  GrammarAstSessionTransferRecursiveClosureTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for transfer-recursive continue propagation from #1091.

  Recursion follows send/receive continuations only.  Select/offer choices
  remain at the already-certified end-refined choice boundary, so this theorem
  does not reopen mutual transfer/choice recursion.
*)

Theorem
  phase1_surface_normalize_continue_transfer_recursive_session_spine_total_from_derivation :
  forall path input rest session,
    Derives phase1_surface_rules path
      (ENonterminal "session_expression") input rest
      (phase1_surface_end_refined_recursive_session_spine_tree session) ->
    exists refined,
      phase1_surface_normalize_continue_transfer_recursive_session_spine
        session = Some refined.
Proof.
  fix IH 4.
  intros path input rest session Hderive.
  destruct session as [nonreference | reference_tree].
  - destruct nonreference as
      [direction parameter boundary guard continuation
      |choice
      |choice
      |terminal
      |selected_tree
      |selected_tree].
    + let transfer := constr:(
        {| phase1_guard_refined_transfer_direction := direction;
           phase1_guard_refined_transfer_parameter := parameter;
           phase1_guard_refined_transfer_boundary := boundary;
           phase1_guard_refined_transfer_guard := guard;
           phase1_guard_refined_transfer_continuation_tree :=
             phase1_surface_end_refined_recursive_session_spine_tree
               continuation |}) in
      assert (Htransfer_tree :
        phase1_surface_guard_refined_boundary_typed_transfer_session_spine_tree
          (Phase1GuardRefinedBoundaryTypedTransferNonreferenceSession
            (Phase1GuardRefinedBoundaryTypedTransferSession transfer)) =
        phase1_surface_end_refined_recursive_session_spine_tree
          (Phase1EndRefinedRecursiveNonreferenceSession
            (Phase1EndRefinedRecursiveTransferSession
              direction parameter boundary guard continuation)))
        by reflexivity;
      destruct
        (phase1_surface_guard_refined_transfer_continuation_derivation_shorter
          path input rest
          (phase1_surface_end_refined_recursive_session_spine_tree
            (Phase1EndRefinedRecursiveNonreferenceSession
              (Phase1EndRefinedRecursiveTransferSession
                direction parameter boundary guard continuation)))
          transfer Hderive Htransfer_tree)
        as [continuation_path
          [continuation_input [continuation_rest
            [Hcontinuation Hshort]]]];
      destruct
        (IH continuation_path continuation_input continuation_rest
          continuation Hcontinuation)
        as [refined_continuation Hcontinuation_normalize];
      exists
        (Phase1ContinueTransferRecursiveNonreferenceSession
          (Phase1ContinueTransferRecursiveTransferSession
            direction parameter boundary guard refined_continuation));
      cbn;
      rewrite Hcontinuation_normalize;
      reflexivity.
    + exists
        (Phase1ContinueTransferRecursiveNonreferenceSession
          (Phase1ContinueTransferRecursiveSelectSession choice)).
      reflexivity.
    + exists
        (Phase1ContinueTransferRecursiveNonreferenceSession
          (Phase1ContinueTransferRecursiveOfferSession choice)).
      reflexivity.
    + exists
        (Phase1ContinueTransferRecursiveNonreferenceSession
          (Phase1ContinueTransferRecursiveEndSession terminal)).
      reflexivity.
    + exists
        (Phase1ContinueTransferRecursiveNonreferenceSession
          (Phase1ContinueTransferRecursiveRecursiveSession selected_tree)).
      reflexivity.
    + cbn in Hderive.
      destruct
        (phase1_surface_selected_continue_derivation
          path input rest selected_tree Hderive)
        as [continue_path Hcontinue].
      destruct
        (phase1_surface_normalize_continue_session_payload_spine_total_from_derivation
          continue_path input rest selected_tree Hcontinue)
        as [payload [Hpayload Hpayload_tree]].
      exists
        (Phase1ContinueTransferRecursiveNonreferenceSession
          (Phase1ContinueTransferRecursiveContinueSession payload)).
      cbn.
      rewrite Hpayload.
      reflexivity.
  - exists
      (Phase1ContinueTransferRecursiveStaticReferenceSession reference_tree).
    reflexivity.
Qed.
