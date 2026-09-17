From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveBodyTransitiveClosureSpine.

Import ListNotations.
Open Scope string_scope.

(*
  First semantic layer above the fully structured recursive-session carrier.

  This checker follows the lexical behavior already used by the Grammar-v1
  semantic session elaborator: entering `recursive x = body` makes x available
  throughout body; transfer and choice continuations preserve the current
  recursion scope; `continue x` is accepted only when x names an enclosing
  recursive binder.

  This slice deliberately validates source spelling only.  It does not yet
  assign a stable semantic identity to recursive binders or prove alpha-
  invariance.  Those are successor obligations.
*)

Fixpoint phase1_surface_recursive_scope_check_session
  (scope : list string)
  (session : Phase1SurfaceRecursiveBodyTransitiveSessionSpine) : bool :=
  match session with
  | Phase1RecursiveBodyTransitiveStaticReferenceSession _ => true
  | Phase1RecursiveBodyTransitiveNonreferenceSession nonreference =>
      phase1_surface_recursive_scope_check_nonreference scope nonreference
  end

with phase1_surface_recursive_scope_check_nonreference
  (scope : list string)
  (session : Phase1SurfaceRecursiveBodyTransitiveNonreferenceSessionSpine)
  : bool :=
  match session with
  | Phase1RecursiveBodyTransitiveTransferSession
      _ _ _ _ continuation =>
      phase1_surface_recursive_scope_check_session scope continuation
  | Phase1RecursiveBodyTransitiveSelectSession choice =>
      phase1_surface_recursive_scope_check_choice scope choice
  | Phase1RecursiveBodyTransitiveOfferSession choice =>
      phase1_surface_recursive_scope_check_choice scope choice
  | Phase1RecursiveBodyTransitiveEndSession _ => true
  | Phase1RecursiveBodyTransitiveRecursiveSession name body =>
      phase1_surface_recursive_scope_check_session (name :: scope) body
  | Phase1RecursiveBodyTransitiveContinueSession payload =>
      existsb
        (String.eqb (phase1_continue_session_name payload))
        scope
  end

with phase1_surface_recursive_scope_check_choice
  (scope : list string)
  (choice : Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine) : bool :=
  match choice with
  | Phase1RecursiveBodyTransitiveChoice _ first_branch rest_branches =>
      andb
        (phase1_surface_recursive_scope_check_branch scope first_branch)
        (phase1_surface_recursive_scope_check_branch_tail scope rest_branches)
  end

with phase1_surface_recursive_scope_check_branch
  (scope : list string)
  (branch : Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine) : bool :=
  match branch with
  | Phase1RecursiveBodyTransitiveBranch _ _ _ _ continuation =>
      phase1_surface_recursive_scope_check_session scope continuation
  end

with phase1_surface_recursive_scope_check_branch_tail
  (scope : list string)
  (branches : Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine) : bool :=
  match branches with
  | Phase1RecursiveBodyTransitiveBranchTailNil => true
  | Phase1RecursiveBodyTransitiveBranchTailCons branch rest =>
      andb
        (phase1_surface_recursive_scope_check_branch scope branch)
        (phase1_surface_recursive_scope_check_branch_tail scope rest)
  end.

Definition phase1_surface_recursive_scope_check
  (session : Phase1SurfaceRecursiveBodyTransitiveSessionSpine) : bool :=
  phase1_surface_recursive_scope_check_session [] session.

Record Phase1SurfaceRecursiveScopeCertificate : Type := {
  phase1_recursive_scope_certified_session :
    Phase1SurfaceRecursiveBodyTransitiveSessionSpine;
  phase1_recursive_scope_certified_evidence :
    phase1_surface_recursive_scope_check
      phase1_recursive_scope_certified_session = true
}.

Definition phase1_surface_recursive_scope_certificate_tree
  (certificate : Phase1SurfaceRecursiveScopeCertificate) : ParseTree :=
  phase1_surface_recursive_body_transitive_session_spine_tree
    (phase1_recursive_scope_certified_session certificate).

Definition phase1_surface_certify_recursive_scope
  (session : Phase1SurfaceRecursiveBodyTransitiveSessionSpine)
  : option Phase1SurfaceRecursiveScopeCertificate.
Proof.
  destruct (phase1_surface_recursive_scope_check session) eqn:Hscope.
  - exact
      (Some
        {| phase1_recursive_scope_certified_session := session;
           phase1_recursive_scope_certified_evidence := Hscope |}).
  - exact None.
Defined.

Theorem phase1_surface_certify_recursive_scope_round_trip :
  forall session certificate,
    phase1_surface_certify_recursive_scope session = Some certificate ->
    phase1_surface_recursive_scope_certificate_tree certificate =
      phase1_surface_recursive_body_transitive_session_spine_tree session.
Proof.
  intros session certificate Hcertify.
  unfold phase1_surface_certify_recursive_scope in Hcertify.
  destruct (phase1_surface_recursive_scope_check session)
    eqn:Hscope; try discriminate Hcertify.
  inversion Hcertify; subst certificate.
  reflexivity.
Qed.

Lemma phase1_surface_recursive_scope_check_continue_empty :
  forall payload,
    phase1_surface_recursive_scope_check_session []
      (Phase1RecursiveBodyTransitiveNonreferenceSession
        (Phase1RecursiveBodyTransitiveContinueSession payload)) = false.
Proof.
  intros payload.
  reflexivity.
Qed.

Lemma phase1_surface_recursive_scope_check_recursive_self :
  forall name,
    phase1_surface_recursive_scope_check_session []
      (Phase1RecursiveBodyTransitiveNonreferenceSession
        (Phase1RecursiveBodyTransitiveRecursiveSession
          name
          (Phase1RecursiveBodyTransitiveNonreferenceSession
            (Phase1RecursiveBodyTransitiveContinueSession
              {| phase1_continue_session_name := name |})))) = true.
Proof.
  intros name.
  cbn.
  rewrite String.eqb_refl.
  reflexivity.
Qed.
