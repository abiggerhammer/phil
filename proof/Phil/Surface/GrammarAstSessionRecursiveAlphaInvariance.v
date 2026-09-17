From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionRecursiveDeclarationIdentity.

Import ListNotations.
Open Scope string_scope.

(*
  Alpha-normal semantics for recursive session binders.

  Recursive binder and continue spellings are presentation.  Every other source
  distinction remains in the alpha shape, while exact binding links remain in
  the already-certified ordinal identity overlay from #1151/#1154.

  Two sources are alpha-equivalent exactly when they normalize to the same pair:

    (source tree with recursive spellings erased, resolved identity overlay).

  This permits independent sibling-local renaming because the presentation tree
  forgets each recursive spelling independently while the identity overlay keeps
  the exact declaration-local ordinal selected by every continue occurrence.
*)

Definition phase1_surface_recursive_alpha_name : string :=
  "__phil_recursive_alpha__".

Fixpoint phase1_surface_recursive_alpha_shape_session_tree
  (session : Phase1SurfaceRecursiveBodyTransitiveSessionSpine) : ParseTree :=
  match session with
  | Phase1RecursiveBodyTransitiveStaticReferenceSession reference_tree =>
      PTNonterminal "session_expression" (PTAlternative 1 reference_tree)
  | Phase1RecursiveBodyTransitiveNonreferenceSession nonreference =>
      PTNonterminal "session_expression"
        (PTAlternative 0
          (phase1_surface_recursive_alpha_shape_nonreference_tree nonreference))
  end

with phase1_surface_recursive_alpha_shape_nonreference_tree
  (session : Phase1SurfaceRecursiveBodyTransitiveNonreferenceSessionSpine)
  : ParseTree :=
  match session with
  | Phase1RecursiveBodyTransitiveTransferSession
      direction parameter boundary guard continuation =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative
          (phase1_surface_session_transfer_index direction)
          (PTSequence
            [ PTLiteral (phase1_surface_session_transfer_keyword direction);
              PTLiteral "(";
              phase1_surface_term_param_type_spine_tree parameter;
              PTLiteral ")";
              phase1_surface_boundary_refined_annotation_tree boundary;
              phase1_surface_guard_refined_annotation_tree guard;
              PTLiteral "then";
              phase1_surface_recursive_alpha_shape_session_tree continuation
            ]))
  | Phase1RecursiveBodyTransitiveSelectSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 2
          (phase1_surface_recursive_alpha_shape_choice_tree choice))
  | Phase1RecursiveBodyTransitiveOfferSession choice =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 3
          (phase1_surface_recursive_alpha_shape_choice_tree choice))
  | Phase1RecursiveBodyTransitiveEndSession terminal =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 4 (phase1_surface_end_session_spine_tree terminal))
  | Phase1RecursiveBodyTransitiveRecursiveSession _ body =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 5
          (PTSequence
            [ PTLiteral "recursive";
              phase1_surface_identifier_tree phase1_surface_recursive_alpha_name;
              PTLiteral "=";
              phase1_surface_recursive_alpha_shape_session_tree body
            ]))
  | Phase1RecursiveBodyTransitiveContinueSession _ =>
      PTNonterminal "nonreference_session_expression"
        (PTAlternative 6
          (phase1_surface_continue_session_payload_spine_tree
            {| phase1_continue_session_name :=
                 phase1_surface_recursive_alpha_name |}))
  end

with phase1_surface_recursive_alpha_shape_choice_tree
  (choice : Phase1SurfaceRecursiveBodyTransitiveSessionChoiceSpine) : ParseTree :=
  match choice with
  | Phase1RecursiveBodyTransitiveChoice direction first_branch rest_branches =>
      PTSequence
        [ PTLiteral (phase1_surface_session_choice_keyword direction);
          PTLiteral "{";
          phase1_surface_recursive_alpha_shape_branch_tree first_branch;
          PTRepetition
            (phase1_surface_recursive_alpha_shape_branch_tail_trees rest_branches);
          PTLiteral "}"
        ]
  end

with phase1_surface_recursive_alpha_shape_branch_tree
  (branch : Phase1SurfaceRecursiveBodyTransitiveSessionBranchSpine) : ParseTree :=
  match branch with
  | Phase1RecursiveBodyTransitiveBranch
      label params boundary guard continuation =>
      PTNonterminal "session_branch"
        (PTSequence
          [ phase1_surface_identifier_tree label;
            phase1_surface_session_branch_params_tree params;
            phase1_surface_boundary_refined_annotation_tree boundary;
            phase1_surface_guard_refined_annotation_tree guard;
            PTLiteral "=>";
            phase1_surface_recursive_alpha_shape_session_tree continuation
          ])
  end

with phase1_surface_recursive_alpha_shape_branch_tail_trees
  (branches : Phase1SurfaceRecursiveBodyTransitiveSessionBranchTailSpine)
  : list ParseTree :=
  match branches with
  | Phase1RecursiveBodyTransitiveBranchTailNil => []
  | Phase1RecursiveBodyTransitiveBranchTailCons branch rest =>
      phase1_surface_session_branch_suffix_tree
        (phase1_surface_recursive_alpha_shape_branch_tree branch)
      :: phase1_surface_recursive_alpha_shape_branch_tail_trees rest
  end.

Record Phase1SurfaceRecursiveAlphaNormalForm : Type := {
  phase1_recursive_alpha_shape : ParseTree;
  phase1_recursive_alpha_identity : Phase1SurfaceRecursiveIdentitySessionSpine
}.

Definition phase1_surface_recursive_alpha_normalize
  (session : Phase1SurfaceRecursiveBodyTransitiveSessionSpine)
  : option Phase1SurfaceRecursiveAlphaNormalForm :=
  match phase1_surface_recursive_identity_resolve session with
  | Some (_, events) =>
      match phase1_surface_consume_recursive_identity_session events session with
      | Some (identity, []) =>
          Some
            {| phase1_recursive_alpha_shape :=
                 phase1_surface_recursive_alpha_shape_session_tree session;
               phase1_recursive_alpha_identity := identity |}
      | _ => None
      end
  | None => None
  end.

Definition phase1_surface_recursive_alpha_valid
  (session : Phase1SurfaceRecursiveBodyTransitiveSessionSpine) : Prop :=
  exists normal,
    phase1_surface_recursive_alpha_normalize session = Some normal.

Definition phase1_surface_recursive_alpha_equivalent
  (left right : Phase1SurfaceRecursiveBodyTransitiveSessionSpine) : Prop :=
  exists normal,
    phase1_surface_recursive_alpha_normalize left = Some normal /\
    phase1_surface_recursive_alpha_normalize right = Some normal.

Theorem phase1_surface_recursive_alpha_normalize_total_from_resolution :
  forall session next_ordinal events,
    phase1_surface_recursive_identity_resolve session =
      Some (next_ordinal, events) ->
    exists normal,
      phase1_surface_recursive_alpha_normalize session = Some normal.
Proof.
  intros session next_ordinal events Hresolve.
  destruct phase1_surface_recursive_identity_resolve_consumes_suffix
    as [Hsession _].
  destruct
    (Hsession session [] 0 next_ordinal events [] Hresolve)
    as [identity Hconsume].
  rewrite app_nil_r in Hconsume.
  unfold phase1_surface_recursive_alpha_normalize.
  rewrite Hresolve, Hconsume.
  eexists.
  reflexivity.
Qed.

Theorem phase1_surface_recursive_alpha_normalize_total_from_certificate :
  forall certificate,
    exists normal,
      phase1_surface_recursive_alpha_normalize
        (phase1_recursive_scope_certified_session
          (phase1_recursive_identity_scope_certificate certificate)) =
        Some normal.
Proof.
  intros certificate.
  eapply phase1_surface_recursive_alpha_normalize_total_from_resolution.
  exact (phase1_recursive_identity_evidence certificate).
Qed.

Theorem phase1_surface_recursive_alpha_equivalent_refl :
  forall session,
    phase1_surface_recursive_alpha_valid session ->
    phase1_surface_recursive_alpha_equivalent session session.
Proof.
  intros session [normal Hnormal].
  exists normal.
  split; exact Hnormal.
Qed.

Theorem phase1_surface_recursive_alpha_equivalent_sym :
  forall left right,
    phase1_surface_recursive_alpha_equivalent left right ->
    phase1_surface_recursive_alpha_equivalent right left.
Proof.
  intros left right [normal [Hleft Hright]].
  exists normal.
  split; assumption.
Qed.

Theorem phase1_surface_recursive_alpha_equivalent_trans :
  forall left middle right,
    phase1_surface_recursive_alpha_equivalent left middle ->
    phase1_surface_recursive_alpha_equivalent middle right ->
    phase1_surface_recursive_alpha_equivalent left right.
Proof.
  intros left middle right
    [left_normal [Hleft Hmiddle_left]]
    [right_normal [Hmiddle_right Hright]].
  rewrite Hmiddle_left in Hmiddle_right.
  inversion Hmiddle_right; subst right_normal.
  exists left_normal.
  split; assumption.
Qed.

Definition phase1_surface_recursive_alpha_self
  (name : string) : Phase1SurfaceRecursiveBodyTransitiveSessionSpine :=
  Phase1RecursiveBodyTransitiveNonreferenceSession
    (Phase1RecursiveBodyTransitiveRecursiveSession
      name
      (Phase1RecursiveBodyTransitiveNonreferenceSession
        (Phase1RecursiveBodyTransitiveContinueSession
          {| phase1_continue_session_name := name |}))).

Definition phase1_surface_recursive_alpha_self_identity
  : Phase1SurfaceRecursiveIdentitySessionSpine :=
  Phase1RecursiveIdentityNonreferenceSession
    (Phase1RecursiveIdentityRecursiveSession
      0
      (Phase1RecursiveIdentityNonreferenceSession
        (Phase1RecursiveIdentityContinueSession 0))).

Definition phase1_surface_recursive_alpha_self_normal
  : Phase1SurfaceRecursiveAlphaNormalForm :=
  {| phase1_recursive_alpha_shape :=
       phase1_surface_recursive_alpha_shape_session_tree
         (phase1_surface_recursive_alpha_self
           phase1_surface_recursive_alpha_name);
     phase1_recursive_alpha_identity :=
       phase1_surface_recursive_alpha_self_identity |}.

Lemma phase1_surface_recursive_alpha_self_normalizes :
  forall name,
    phase1_surface_recursive_alpha_normalize
      (phase1_surface_recursive_alpha_self name) =
    Some phase1_surface_recursive_alpha_self_normal.
Proof.
  intros name.
  unfold phase1_surface_recursive_alpha_normalize,
    phase1_surface_recursive_alpha_self,
    phase1_surface_recursive_identity_resolve.
  cbn.
  repeat rewrite String.eqb_refl.
  reflexivity.
Qed.

Theorem phase1_surface_recursive_alpha_self_rename_invariant :
  forall old_name new_name,
    phase1_surface_recursive_alpha_equivalent
      (phase1_surface_recursive_alpha_self old_name)
      (phase1_surface_recursive_alpha_self new_name).
Proof.
  intros old_name new_name.
  exists phase1_surface_recursive_alpha_self_normal.
  split;
    apply phase1_surface_recursive_alpha_self_normalizes.
Qed.

Record Phase1SurfaceRecursiveRootedAlphaNormalForm : Type := {
  phase1_recursive_rooted_alpha_declaration_key : nat;
  phase1_recursive_rooted_alpha_normal : Phase1SurfaceRecursiveAlphaNormalForm
}.

Definition phase1_surface_recursive_rooted_alpha_normalize
  (declaration : DeclarationIdentity)
  (session : Phase1SurfaceRecursiveBodyTransitiveSessionSpine)
  : option Phase1SurfaceRecursiveRootedAlphaNormalForm :=
  match phase1_surface_recursive_alpha_normalize session with
  | Some normal =>
      Some
        {| phase1_recursive_rooted_alpha_declaration_key :=
             identityDeclarationKey declaration;
           phase1_recursive_rooted_alpha_normal := normal |}
  | None => None
  end.

Theorem phase1_surface_recursive_alpha_equivalent_rooted :
  forall declaration left right,
    phase1_surface_recursive_alpha_equivalent left right ->
    exists rooted,
      phase1_surface_recursive_rooted_alpha_normalize declaration left =
        Some rooted /\
      phase1_surface_recursive_rooted_alpha_normalize declaration right =
        Some rooted.
Proof.
  intros declaration left right [normal [Hleft Hright]].
  exists
    {| phase1_recursive_rooted_alpha_declaration_key :=
         identityDeclarationKey declaration;
       phase1_recursive_rooted_alpha_normal := normal |}.
  unfold phase1_surface_recursive_rooted_alpha_normalize.
  rewrite Hleft, Hright.
  split; reflexivity.
Qed.

Theorem phase1_surface_recursive_alpha_equivalent_preserves_semantic_key :
  forall declaration left right ordinal,
    phase1_surface_recursive_alpha_equivalent left right ->
    phase1_surface_recursive_semantic_key
      (identityDeclarationKey declaration) ordinal =
    phase1_surface_recursive_semantic_key
      (identityDeclarationKey declaration) ordinal.
Proof.
  intros.
  reflexivity.
Qed.
