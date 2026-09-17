From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveScopeCertificate.

Import ListNotations.
Open Scope string_scope.

(*
  Allocate declaration-local semantic identities for recursive-session binders.

  This mirrors Grammar-v1 BinderScope's identity discipline without duplicating
  Core naming here: each recursive binder receives a monotonically increasing
  ordinal, while source spelling remains diagnostic only.  A later consumer may
  pair this ordinal with the enclosing declaration identity.

  Active shadowing is rejected, matching the Phase 1 binder authority.  Sibling
  lexical regions may reuse a spelling because their binder is no longer active,
  but the global ordinal counter is never rolled back.  `continue` occurrences
  retain their display spelling and record the exact binder ordinal they resolve
  to.
*)

Inductive Phase1SurfaceRecursiveIdentityEvent : Type :=
| Phase1RecursiveIdentityBinder
    (display_name : string)
    (ordinal : nat)
| Phase1RecursiveIdentityContinue
    (display_name : string)
    (ordinal : nat).

Fixpoint phase1_surface_recursive_identity_lookup
  (name : string)
  (scope : list (string * nat)) : option nat :=
  match scope with
  | [] => None
  | (candidate, ordinal) :: rest =>
      if String.eqb name candidate
      then Some ordinal
      else phase1_surface_recursive_identity_lookup name rest
  end.

Fixpoint phase1_surface_recursive_identity_resolve_session
  (scope : list (string * nat))
  (next_ordinal : nat)
  (session : Phase1SurfaceRecursiveBodyTransitiveSessionSpine)
  : option (nat * list Phase1SurfaceRecursiveIdentityEvent) :=
  match session with
  | Phase1RecursiveBodyTransitiveStaticReferenceSession _ =>
      Some (next_ordinal, [])
  | Phase1RecursiveBodyTransitiveNonreferenceSession nonreference =>
      phase1_surface_recursive_identity_resolve_nonreference
        scope next_ordinal nonreference
  end

with phase1_surface_recursive_identity_resolve_nonreference
  (scope : list (string * nat))
  (next_ordinal : nat)
  (session : Phase1SurfaceRecursiveBodyTransitiveNonreferenceSessionSpine)
  : option (nat * list Phase1SurfaceRecursiveIdentityEvent) :=
  match session with
  | Phase1RecursiveBodyTransitiveTransferSession
      _ _ _ _ continuation =>
      phase1_surface_recursive_identity_resolve_session
        scope next_ordinal continuation
  | Phase1RecursiveBodyTransitiveSelectSession choice =>
      phase1_surface_recursive_identity_resolve_choice
        scope next_ordinal choice
  | Phase1RecursiveBodyTransitiveOfferSession choice =>
      phase1_surface_recursive_identity_resolve_choice
        scope next_ordinal choice
  | Phase1RecursiveBodyTransitiveEndSession _ =>
      Some (next_ordinal, [])
  | Phase1RecursiveBodyTransitiveRecursiveSession name body =>
      match phase1_surface_recursive_identity_lookup name scope with
      | Some _ => None
      | None =>
          match
            phase1_surface_recursive_identity_resolve_session
              ((name, next_ordinal) :: scope)
              (S next_ordinal)
              body
          with
          | Some (next_after_body, body_events) =>
              Some
                ( next_after_body
                , Phase1RecursiveIdentityBinder name next_ordinal
                    :: body_events
                )
          | None => None
          end
      end
  | Phase1RecursiveBodyTransitiveContinueSession payload =>
      let name := phase1_continue_session_name payload in
      match phase1_surface_recursive_identity_lookup name scope with
      | Some ordinal =>
          Some
            ( next_ordinal
            , [Phase1RecursiveIdentityContinue name ordinal]
            )
      | None => None
      end
  end

with phase1_surface_recursive_identity_resolve_choice
  (scope : list (string * nat))
  (next_ordinal : nat)
  (choice : Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine)
  : option (nat * list Phase1SurfaceRecursiveIdentityEvent) :=
  match choice with
  | Phase1RecursiveBodyTransitiveChoice _ first_branch rest_branches =>
      match
        phase1_surface_recursive_identity_resolve_branch
          scope next_ordinal first_branch
      with
      | Some (next_after_first, first_events) =>
          match
            phase1_surface_recursive_identity_resolve_branch_tail
              scope next_after_first rest_branches
          with
          | Some (next_after_rest, rest_events) =>
              Some (next_after_rest, first_events ++ rest_events)
          | None => None
          end
      | None => None
      end
  end

with phase1_surface_recursive_identity_resolve_branch
  (scope : list (string * nat))
  (next_ordinal : nat)
  (branch : Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine)
  : option (nat * list Phase1SurfaceRecursiveIdentityEvent) :=
  match branch with
  | Phase1RecursiveBodyTransitiveBranch _ _ _ _ continuation =>
      phase1_surface_recursive_identity_resolve_session
        scope next_ordinal continuation
  end

with phase1_surface_recursive_identity_resolve_branch_tail
  (scope : list (string * nat))
  (next_ordinal : nat)
  (branches : Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine)
  : option (nat * list Phase1SurfaceRecursiveIdentityEvent) :=
  match branches with
  | Phase1RecursiveBodyTransitiveBranchTailNil =>
      Some (next_ordinal, [])
  | Phase1RecursiveBodyTransitiveBranchTailCons branch rest =>
      match
        phase1_surface_recursive_identity_resolve_branch
          scope next_ordinal branch
      with
      | Some (next_after_branch, branch_events) =>
          match
            phase1_surface_recursive_identity_resolve_branch_tail
              scope next_after_branch rest
          with
          | Some (next_after_rest, rest_events) =>
              Some (next_after_rest, branch_events ++ rest_events)
          | None => None
          end
      | None => None
      end
  end.

Definition phase1_surface_recursive_identity_resolve
  (session : Phase1SurfaceRecursiveBodyTransitiveSessionSpine)
  : option (nat * list Phase1SurfaceRecursiveIdentityEvent) :=
  phase1_surface_recursive_identity_resolve_session [] 0 session.

Record Phase1SurfaceRecursiveIdentityCertificate : Type := {
  phase1_recursive_identity_scope_certificate :
    Phase1SurfaceRecursiveScopeCertificate;
  phase1_recursive_identity_next_ordinal : nat;
  phase1_recursive_identity_events :
    list Phase1SurfaceRecursiveIdentityEvent;
  phase1_recursive_identity_evidence :
    phase1_surface_recursive_identity_resolve
      (phase1_recursive_scope_certified_session
        phase1_recursive_identity_scope_certificate) =
      Some
        ( phase1_recursive_identity_next_ordinal
        , phase1_recursive_identity_events
        )
}.

Definition phase1_surface_recursive_identity_certificate_tree
  (certificate : Phase1SurfaceRecursiveIdentityCertificate) : ParseTree :=
  phase1_surface_recursive_scope_certificate_tree
    (phase1_recursive_identity_scope_certificate certificate).

Definition phase1_surface_certify_recursive_identity
  (certificate : Phase1SurfaceRecursiveScopeCertificate)
  : option Phase1SurfaceRecursiveIdentityCertificate.
Proof.
  destruct
    (phase1_surface_recursive_identity_resolve
      (phase1_recursive_scope_certified_session certificate))
    as [[next_ordinal events] |] eqn:Hresolve.
  - exact
      (Some
        {| phase1_recursive_identity_scope_certificate := certificate;
           phase1_recursive_identity_next_ordinal := next_ordinal;
           phase1_recursive_identity_events := events;
           phase1_recursive_identity_evidence := Hresolve |}).
  - exact None.
Defined.

Theorem phase1_surface_certify_recursive_identity_round_trip :
  forall certificate resolved,
    phase1_surface_certify_recursive_identity certificate = Some resolved ->
    phase1_surface_recursive_identity_certificate_tree resolved =
      phase1_surface_recursive_scope_certificate_tree certificate.
Proof.
  intros certificate resolved Hcertify.
  unfold phase1_surface_certify_recursive_identity in Hcertify.
  destruct
    (phase1_surface_recursive_identity_resolve
      (phase1_recursive_scope_certified_session certificate))
    as [[next_ordinal events] |] eqn:Hresolve;
    try discriminate Hcertify.
  inversion Hcertify; subst resolved.
  reflexivity.
Qed.

Lemma phase1_surface_recursive_identity_resolve_recursive_self :
  forall name,
    phase1_surface_recursive_identity_resolve_session [] 0
      (Phase1RecursiveBodyTransitiveNonreferenceSession
        (Phase1RecursiveBodyTransitiveRecursiveSession
          name
          (Phase1RecursiveBodyTransitiveNonreferenceSession
            (Phase1RecursiveBodyTransitiveContinueSession
              {| phase1_continue_session_name := name |})))) =
    Some
      ( 1
      , [ Phase1RecursiveIdentityBinder name 0;
          Phase1RecursiveIdentityContinue name 0
        ]
      ).
Proof.
  intros name.
  cbn.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Lemma phase1_surface_recursive_identity_rejects_active_shadowing :
  forall name,
    phase1_surface_recursive_identity_resolve_session [] 0
      (Phase1RecursiveBodyTransitiveNonreferenceSession
        (Phase1RecursiveBodyTransitiveRecursiveSession
          name
          (Phase1RecursiveBodyTransitiveNonreferenceSession
            (Phase1RecursiveBodyTransitiveRecursiveSession
              name
              (Phase1RecursiveBodyTransitiveNonreferenceSession
                (Phase1RecursiveBodyTransitiveContinueSession
                  {| phase1_continue_session_name := name |}))))))) =
    None.
Proof.
  intros name.
  cbn.
  rewrite String.eqb_refl.
  reflexivity.
Qed.
