From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveIdentityEvidence.

Import ListNotations.
Open Scope string_scope.

(*
  Consume the ordered recursive-identity evidence stream into a structural
  identity overlay for the final recursive-session carrier.

  The source carrier remains authoritative for syntax and parse-tree
  reconstruction.  This overlay records only semantic recursive structure:
  each `recursive` binder and each `continue` occurrence carries the exact
  declaration-local ordinal allocated by GrammarAstSessionRecursiveIdentityEvidence.

  Keeping syntax and semantic identity separate mirrors Grammar-v1's existing
  resolver-evidence architecture.  Source spelling locates an event while the
  ordinal identifies it.  No second scope search is performed here.
*)

Inductive Phase1SurfaceRecursiveIdentitySessionSpine : Type :=
| Phase1RecursiveIdentityStaticReferenceSession
| Phase1RecursiveIdentityNonreferenceSession
    (session : Phase1SurfaceRecursiveIdentityNonreferenceSessionSpine)

with Phase1SurfaceRecursiveIdentityNonreferenceSessionSpine : Type :=
| Phase1RecursiveIdentityTransferSession
    (continuation : Phase1SurfaceRecursiveIdentitySessionSpine)
| Phase1RecursiveIdentitySelectSession
    (choice : Phase1SurfaceRecursiveIdentitySessionChoiceSpine)
| Phase1RecursiveIdentityOfferSession
    (choice : Phase1SurfaceRecursiveIdentitySessionChoiceSpine)
| Phase1RecursiveIdentityEndSession
| Phase1RecursiveIdentityRecursiveSession
    (ordinal : nat)
    (body : Phase1SurfaceRecursiveIdentitySessionSpine)
| Phase1RecursiveIdentityContinueSession
    (ordinal : nat)

with Phase1SurfaceRecursiveIdentitySessionChoiceSpine : Type :=
| Phase1RecursiveIdentityChoice
    (first_branch : Phase1SurfaceRecursiveIdentitySessionBranchSpine)
    (rest_branches : Phase1SurfaceRecursiveIdentitySessionBranchTailSpine)

with Phase1SurfaceRecursiveIdentitySessionBranchSpine : Type :=
| Phase1RecursiveIdentityBranch
    (continuation : Phase1SurfaceRecursiveIdentitySessionSpine)

with Phase1SurfaceRecursiveIdentitySessionBranchTailSpine : Type :=
| Phase1RecursiveIdentityBranchTailNil
| Phase1RecursiveIdentityBranchTailCons
    (branch : Phase1SurfaceRecursiveIdentitySessionBranchSpine)
    (rest : Phase1SurfaceRecursiveIdentitySessionBranchTailSpine).

Fixpoint phase1_surface_consume_recursive_identity_session
  (events : list Phase1SurfaceRecursiveIdentityEvent)
  (session : Phase1SurfaceRecursiveBodyTransitiveSessionSpine)
  : option
      (Phase1SurfaceRecursiveIdentitySessionSpine *
        list Phase1SurfaceRecursiveIdentityEvent) :=
  match session with
  | Phase1RecursiveBodyTransitiveStaticReferenceSession _ =>
      Some (Phase1RecursiveIdentityStaticReferenceSession, events)
  | Phase1RecursiveBodyTransitiveNonreferenceSession nonreference =>
      match
        phase1_surface_consume_recursive_identity_nonreference
          events nonreference
      with
      | Some (resolved, remaining) =>
          Some
            (Phase1RecursiveIdentityNonreferenceSession resolved, remaining)
      | None => None
      end
  end

with phase1_surface_consume_recursive_identity_nonreference
  (events : list Phase1SurfaceRecursiveIdentityEvent)
  (session : Phase1SurfaceRecursiveBodyTransitiveNonreferenceSessionSpine)
  : option
      (Phase1SurfaceRecursiveIdentityNonreferenceSessionSpine *
        list Phase1SurfaceRecursiveIdentityEvent) :=
  match session with
  | Phase1RecursiveBodyTransitiveTransferSession
      _ _ _ _ continuation =>
      match
        phase1_surface_consume_recursive_identity_session events continuation
      with
      | Some (resolved, remaining) =>
          Some (Phase1RecursiveIdentityTransferSession resolved, remaining)
      | None => None
      end
  | Phase1RecursiveBodyTransitiveSelectSession choice =>
      match phase1_surface_consume_recursive_identity_choice events choice with
      | Some (resolved, remaining) =>
          Some (Phase1RecursiveIdentitySelectSession resolved, remaining)
      | None => None
      end
  | Phase1RecursiveBodyTransitiveOfferSession choice =>
      match phase1_surface_consume_recursive_identity_choice events choice with
      | Some (resolved, remaining) =>
          Some (Phase1RecursiveIdentityOfferSession resolved, remaining)
      | None => None
      end
  | Phase1RecursiveBodyTransitiveEndSession _ =>
      Some (Phase1RecursiveIdentityEndSession, events)
  | Phase1RecursiveBodyTransitiveRecursiveSession name body =>
      match events with
      | Phase1RecursiveIdentityBinder event_name ordinal :: remaining =>
          if String.eqb name event_name
          then
            match
              phase1_surface_consume_recursive_identity_session remaining body
            with
            | Some (resolved_body, after_body) =>
                Some
                  ( Phase1RecursiveIdentityRecursiveSession ordinal resolved_body
                  , after_body
                  )
            | None => None
            end
          else None
      | _ => None
      end
  | Phase1RecursiveBodyTransitiveContinueSession payload =>
      match events with
      | Phase1RecursiveIdentityContinue event_name ordinal :: remaining =>
          if String.eqb (phase1_continue_session_name payload) event_name
          then
            Some
              (Phase1RecursiveIdentityContinueSession ordinal, remaining)
          else None
      | _ => None
      end
  end

with phase1_surface_consume_recursive_identity_choice
  (events : list Phase1SurfaceRecursiveIdentityEvent)
  (choice : Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine)
  : option
      (Phase1SurfaceRecursiveIdentitySessionChoiceSpine *
        list Phase1SurfaceRecursiveIdentityEvent) :=
  match choice with
  | Phase1RecursiveBodyTransitiveChoice _ first_branch rest_branches =>
      match
        phase1_surface_consume_recursive_identity_branch events first_branch
      with
      | Some (resolved_first, after_first) =>
          match
            phase1_surface_consume_recursive_identity_branch_tail
              after_first rest_branches
          with
          | Some (resolved_rest, after_rest) =>
              Some
                ( Phase1RecursiveIdentityChoice resolved_first resolved_rest
                , after_rest
                )
          | None => None
          end
      | None => None
      end
  end

with phase1_surface_consume_recursive_identity_branch
  (events : list Phase1SurfaceRecursiveIdentityEvent)
  (branch : Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine)
  : option
      (Phase1SurfaceRecursiveIdentitySessionBranchSpine *
        list Phase1SurfaceRecursiveIdentityEvent) :=
  match branch with
  | Phase1RecursiveBodyTransitiveBranch _ _ _ _ continuation =>
      match
        phase1_surface_consume_recursive_identity_session events continuation
      with
      | Some (resolved, remaining) =>
          Some (Phase1RecursiveIdentityBranch resolved, remaining)
      | None => None
      end
  end

with phase1_surface_consume_recursive_identity_branch_tail
  (events : list Phase1SurfaceRecursiveIdentityEvent)
  (branches : Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine)
  : option
      (Phase1SurfaceRecursiveIdentitySessionBranchTailSpine *
        list Phase1SurfaceRecursiveIdentityEvent) :=
  match branches with
  | Phase1RecursiveBodyTransitiveBranchTailNil =>
      Some (Phase1RecursiveIdentityBranchTailNil, events)
  | Phase1RecursiveBodyTransitiveBranchTailCons branch rest =>
      match phase1_surface_consume_recursive_identity_branch events branch with
      | Some (resolved_branch, after_branch) =>
          match
            phase1_surface_consume_recursive_identity_branch_tail
              after_branch rest
          with
          | Some (resolved_rest, after_rest) =>
              Some
                ( Phase1RecursiveIdentityBranchTailCons
                    resolved_branch resolved_rest
                , after_rest
                )
          | None => None
          end
      | None => None
      end
  end.

Record Phase1SurfaceRecursiveIdentityCarrier : Type := {
  phase1_recursive_identity_carrier_certificate :
    Phase1SurfaceRecursiveIdentityCertificate;
  phase1_recursive_identity_carrier_structure :
    Phase1SurfaceRecursiveIdentitySessionSpine;
  phase1_recursive_identity_carrier_consumed :
    phase1_surface_consume_recursive_identity_session
      (phase1_recursive_identity_events
        phase1_recursive_identity_carrier_certificate)
      (phase1_recursive_scope_certified_session
        (phase1_recursive_identity_scope_certificate
          phase1_recursive_identity_carrier_certificate)) =
      Some
        ( phase1_recursive_identity_carrier_structure
        , []
        )
}.

Definition phase1_surface_recursive_identity_carrier_tree
  (carrier : Phase1SurfaceRecursiveIdentityCarrier) : ParseTree :=
  phase1_surface_recursive_identity_certificate_tree
    (phase1_recursive_identity_carrier_certificate carrier).

Definition phase1_surface_normalize_recursive_identity_carrier
  (certificate : Phase1SurfaceRecursiveIdentityCertificate)
  : option Phase1SurfaceRecursiveIdentityCarrier.
Proof.
  destruct
    (phase1_surface_consume_recursive_identity_session
      (phase1_recursive_identity_events certificate)
      (phase1_recursive_scope_certified_session
        (phase1_recursive_identity_scope_certificate certificate)))
    as [[resolved remaining] |] eqn:Hconsume.
  - destruct remaining as [|event rest].
    + exact
        (Some
          {| phase1_recursive_identity_carrier_certificate := certificate;
             phase1_recursive_identity_carrier_structure := resolved;
             phase1_recursive_identity_carrier_consumed := Hconsume |}).
    + exact None.
  - exact None.
Defined.

Theorem phase1_surface_normalize_recursive_identity_carrier_round_trip :
  forall certificate carrier,
    phase1_surface_normalize_recursive_identity_carrier certificate =
      Some carrier ->
    phase1_surface_recursive_identity_carrier_tree carrier =
      phase1_surface_recursive_identity_certificate_tree certificate.
Proof.
  intros certificate carrier Hnormalize.
  unfold phase1_surface_normalize_recursive_identity_carrier in Hnormalize.
  destruct
    (phase1_surface_consume_recursive_identity_session
      (phase1_recursive_identity_events certificate)
      (phase1_recursive_scope_certified_session
        (phase1_recursive_identity_scope_certificate certificate)))
    as [[resolved remaining] |] eqn:Hconsume;
    try discriminate Hnormalize.
  destruct remaining as [|event rest]; try discriminate Hnormalize.
  inversion Hnormalize; subst carrier.
  reflexivity.
Qed.

Lemma phase1_surface_consume_recursive_identity_self :
  forall name,
    phase1_surface_consume_recursive_identity_session
      [ Phase1RecursiveIdentityBinder name 0;
        Phase1RecursiveIdentityContinue name 0
      ]
      (Phase1RecursiveBodyTransitiveNonreferenceSession
        (Phase1RecursiveBodyTransitiveRecursiveSession
          name
          (Phase1RecursiveBodyTransitiveNonreferenceSession
            (Phase1RecursiveBodyTransitiveContinueSession
              {| phase1_continue_session_name := name |})))) =
    Some
      ( Phase1RecursiveIdentityNonreferenceSession
          (Phase1RecursiveIdentityRecursiveSession
            0
            (Phase1RecursiveIdentityNonreferenceSession
              (Phase1RecursiveIdentityContinueSession 0)))
      , []
      ).
Proof.
  intros name.
  cbn.
  repeat rewrite String.eqb_refl.
  reflexivity.
Qed.

Lemma phase1_surface_consume_recursive_identity_rejects_wrong_event_name :
  forall source_name event_name,
    String.eqb source_name event_name = false ->
    phase1_surface_consume_recursive_identity_session
      [Phase1RecursiveIdentityContinue event_name 0]
      (Phase1RecursiveBodyTransitiveNonreferenceSession
        (Phase1RecursiveBodyTransitiveContinueSession
          {| phase1_continue_session_name := source_name |})) = None.
Proof.
  intros source_name event_name Hneq.
  cbn.
  rewrite Hneq.
  reflexivity.
Qed.
