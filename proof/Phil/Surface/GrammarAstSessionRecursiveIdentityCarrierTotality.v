From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveIdentityCarrier.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the ordered identity-evidence consumer from #1151.

  The key invariant is suffix preservation.  If #1150 resolves a source subtree
  to exactly the event stream [events], then #1151 may consume that stream in
  front of any later [suffix], producing the identity overlay for this subtree
  and leaving [suffix] untouched.  This is the composition law needed for
  select/offer branches and branch tails.

  Scope validity and ordinal allocation are not reproved here: they are already
  certified by the resolver equation carried by
  Phase1SurfaceRecursiveIdentityCertificate.
*)

Scheme Phase1SurfaceRecursiveBodyTransitiveSessionSpine_ind' :=
  Induction for Phase1SurfaceRecursiveBodyTransitiveSessionSpine Sort Prop
with Phase1SurfaceRecursiveBodyTransitiveNonreferenceSessionSpine_ind' :=
  Induction for Phase1SurfaceRecursiveBodyTransitiveNonreferenceSessionSpine Sort Prop
with Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine_ind' :=
  Induction for Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine Sort Prop
with Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine_ind' :=
  Induction for Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine Sort Prop
with Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine_ind' :=
  Induction for Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine Sort Prop.

Combined Scheme phase1_surface_recursive_body_transitive_identity_mutind
  from Phase1SurfaceRecursiveBodyTransitiveSessionSpine_ind',
       Phase1SurfaceRecursiveBodyTransitiveNonreferenceSessionSpine_ind',
       Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine_ind',
       Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine_ind',
       Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine_ind'.

Theorem phase1_surface_recursive_identity_resolve_consumes_suffix :
  (forall session,
    forall scope next_ordinal next_after events suffix,
      phase1_surface_recursive_identity_resolve_session
        scope next_ordinal session = Some (next_after, events) ->
      exists resolved,
        phase1_surface_consume_recursive_identity_session
          (events ++ suffix) session = Some (resolved, suffix)) /\
  (forall nonreference,
    forall scope next_ordinal next_after events suffix,
      phase1_surface_recursive_identity_resolve_nonreference
        scope next_ordinal nonreference = Some (next_after, events) ->
      exists resolved,
        phase1_surface_consume_recursive_identity_nonreference
          (events ++ suffix) nonreference = Some (resolved, suffix)) /\
  (forall choice,
    forall scope next_ordinal next_after events suffix,
      phase1_surface_recursive_identity_resolve_choice
        scope next_ordinal choice = Some (next_after, events) ->
      exists resolved,
        phase1_surface_consume_recursive_identity_choice
          (events ++ suffix) choice = Some (resolved, suffix)) /\
  (forall branch,
    forall scope next_ordinal next_after events suffix,
      phase1_surface_recursive_identity_resolve_branch
        scope next_ordinal branch = Some (next_after, events) ->
      exists resolved,
        phase1_surface_consume_recursive_identity_branch
          (events ++ suffix) branch = Some (resolved, suffix)) /\
  (forall branches,
    forall scope next_ordinal next_after events suffix,
      phase1_surface_recursive_identity_resolve_branch_tail
        scope next_ordinal branches = Some (next_after, events) ->
      exists resolved,
        phase1_surface_consume_recursive_identity_branch_tail
          (events ++ suffix) branches = Some (resolved, suffix)).
Proof.
  apply phase1_surface_recursive_body_transitive_identity_mutind.
  - intros reference_tree scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve.
    inversion Hresolve; subst.
    exists Phase1RecursiveIdentityStaticReferenceSession.
    reflexivity.
  - intros nonreference IH scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve |- *.
    destruct (IH scope next_ordinal next_after events suffix Hresolve)
      as [resolved Hconsume].
    rewrite Hconsume.
    eexists.
    reflexivity.
  - intros direction parameter boundary guard continuation IH
      scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve |- *.
    destruct (IH scope next_ordinal next_after events suffix Hresolve)
      as [resolved Hconsume].
    rewrite Hconsume.
    eexists.
    reflexivity.
  - intros choice IH scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve |- *.
    destruct (IH scope next_ordinal next_after events suffix Hresolve)
      as [resolved Hconsume].
    rewrite Hconsume.
    eexists.
    reflexivity.
  - intros choice IH scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve |- *.
    destruct (IH scope next_ordinal next_after events suffix Hresolve)
      as [resolved Hconsume].
    rewrite Hconsume.
    eexists.
    reflexivity.
  - intros terminal scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve.
    inversion Hresolve; subst.
    exists Phase1RecursiveIdentityEndSession.
    reflexivity.
  - intros name body IH scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve.
    destruct (phase1_surface_recursive_identity_lookup name scope)
      as [active |] eqn:Hlookup; try discriminate Hresolve.
    destruct
      (phase1_surface_recursive_identity_resolve_session
        ((name, next_ordinal) :: scope) (S next_ordinal) body)
      as [[body_next body_events] |] eqn:Hbody; try discriminate Hresolve.
    inversion Hresolve; subst.
    destruct
      (IH ((name, next_ordinal) :: scope) (S next_ordinal)
        body_next body_events suffix Hbody)
      as [resolved_body Hconsume].
    exists (Phase1RecursiveIdentityRecursiveSession next_ordinal resolved_body).
    cbn.
    rewrite String.eqb_refl.
    rewrite Hconsume.
    reflexivity.
  - intros payload scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve.
    destruct
      (phase1_surface_recursive_identity_lookup
        (phase1_continue_session_name payload) scope)
      as [ordinal |] eqn:Hlookup; try discriminate Hresolve.
    inversion Hresolve; subst.
    exists (Phase1RecursiveIdentityContinueSession ordinal).
    cbn.
    rewrite String.eqb_refl.
    reflexivity.
  - intros direction first_branch IHfirst rest_branches IHrest
      scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve.
    destruct
      (phase1_surface_recursive_identity_resolve_branch
        scope next_ordinal first_branch)
      as [[next_after_first first_events] |] eqn:Hfirst;
      try discriminate Hresolve.
    destruct
      (phase1_surface_recursive_identity_resolve_branch_tail
        scope next_after_first rest_branches)
      as [[next_after_rest rest_events] |] eqn:Hrest;
      try discriminate Hresolve.
    inversion Hresolve; subst.
    destruct
      (IHfirst scope next_ordinal next_after_first first_events
        (rest_events ++ suffix) Hfirst)
      as [resolved_first Hconsume_first].
    destruct
      (IHrest scope next_after_first next_after_rest rest_events suffix Hrest)
      as [resolved_rest Hconsume_rest].
    exists (Phase1RecursiveIdentityChoice resolved_first resolved_rest).
    cbn.
    rewrite app_assoc.
    rewrite Hconsume_first.
    rewrite Hconsume_rest.
    reflexivity.
  - intros label params boundary guard continuation IH
      scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve |- *.
    destruct (IH scope next_ordinal next_after events suffix Hresolve)
      as [resolved Hconsume].
    rewrite Hconsume.
    eexists.
    reflexivity.
  - intros scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve.
    inversion Hresolve; subst.
    exists Phase1RecursiveIdentityBranchTailNil.
    reflexivity.
  - intros branch IHbranch rest IHrest
      scope next_ordinal next_after events suffix Hresolve.
    cbn in Hresolve.
    destruct
      (phase1_surface_recursive_identity_resolve_branch
        scope next_ordinal branch)
      as [[next_after_branch branch_events] |] eqn:Hbranch;
      try discriminate Hresolve.
    destruct
      (phase1_surface_recursive_identity_resolve_branch_tail
        scope next_after_branch rest)
      as [[next_after_rest rest_events] |] eqn:Hrest;
      try discriminate Hresolve.
    inversion Hresolve; subst.
    destruct
      (IHbranch scope next_ordinal next_after_branch branch_events
        (rest_events ++ suffix) Hbranch)
      as [resolved_branch Hconsume_branch].
    destruct
      (IHrest scope next_after_branch next_after_rest rest_events suffix Hrest)
      as [resolved_rest Hconsume_rest].
    exists
      (Phase1RecursiveIdentityBranchTailCons resolved_branch resolved_rest).
    cbn.
    rewrite app_assoc.
    rewrite Hconsume_branch.
    rewrite Hconsume_rest.
    reflexivity.
Qed.

Theorem phase1_surface_normalize_recursive_identity_carrier_total :
  forall certificate,
    exists carrier,
      phase1_surface_normalize_recursive_identity_carrier certificate =
        Some carrier /\
      phase1_surface_recursive_identity_carrier_tree carrier =
        phase1_surface_recursive_identity_certificate_tree certificate.
Proof.
  intros certificate.
  destruct phase1_surface_recursive_identity_resolve_consumes_suffix
    as [Hsession _].
  pose proof (phase1_recursive_identity_evidence certificate) as Hresolve.
  destruct
    (Hsession
      (phase1_recursive_scope_certified_session
        (phase1_recursive_identity_scope_certificate certificate))
      [] 0
      (phase1_recursive_identity_next_ordinal certificate)
      (phase1_recursive_identity_events certificate)
      [] Hresolve)
    as [resolved Hconsume].
  rewrite app_nil_r in Hconsume.
  let carrier :=
    constr:(
      {| phase1_recursive_identity_carrier_certificate := certificate;
         phase1_recursive_identity_carrier_structure := resolved;
         phase1_recursive_identity_carrier_consumed := Hconsume |}) in
  assert (Hnormalize :
    phase1_surface_normalize_recursive_identity_carrier certificate =
      Some carrier).
  {
    unfold phase1_surface_normalize_recursive_identity_carrier.
    rewrite Hconsume.
    reflexivity.
  }
  exists carrier.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_recursive_identity_carrier_round_trip.
    exact Hnormalize.
Qed.
