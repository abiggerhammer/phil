From Stdlib Require Import Strings.String Lists.List Bool.Bool.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.

(*
  Proof-oriented model of the surface scope-pruning and metadata-join boundary.

  Core resource convergence itself is already proved by PHIL-CTX-JOIN-001.
  This file adds the surface obligations that sit around that Core join:

  - a continuing branch may not leave a branch-local linear binding live;
  - all branch-local metadata is removed before a continuing branch rejoins;
  - metadata retained after the Core join must correspond to a surviving Core
    binding and must agree across every continuing branch.

  The concrete implementation uses Data.Map and source Text names.  As in the
  existing Core proofs, maps are represented extensionally here.
*)

Record SurfaceBindingMeta : Type := mkSurfaceBindingMeta
  { surfaceMetaMode : Mode
  ; surfaceMetaType : Ty
  }.

Definition SurfaceMetadata := Name -> option SurfaceBindingMeta.
Definition IncomingNames := Name -> bool.

Definition pruneScopedMetadata
  (incoming : IncomingNames)
  (current : SurfaceMetadata) : SurfaceMetadata :=
  fun name => if incoming name then current name else None.

Definition NoLiveLocalLinear
  (incoming : IncomingNames)
  (current : SurfaceMetadata) : Prop :=
  forall (name : Name) (meta : SurfaceBindingMeta),
    incoming name = false ->
    current name = Some meta ->
    surfaceMetaMode meta <> Linear.

Inductive ScopePruneSuccess
  (incoming : IncomingNames)
  (current : SurfaceMetadata) : SurfaceMetadata -> Prop :=
| ScopePrune_ok :
    NoLiveLocalLinear incoming current ->
    ScopePruneSuccess incoming current (pruneScopedMetadata incoming current).

(* PHIL-SURFACE-SCOPE-001: live local linear bindings block scope exit. *)
Theorem successful_scope_exit_has_no_live_local_linear :
  forall incoming current pruned name meta,
    ScopePruneSuccess incoming current pruned ->
    incoming name = false ->
    current name = Some meta ->
    surfaceMetaMode meta <> Linear.
Proof.
  intros incoming current pruned name meta Hprune Hlocal Hmeta.
  inversion Hprune; subst pruned.
  eapply H; eauto.
Qed.

(* PHIL-SURFACE-SCOPE-001: no branch-local metadata survives pruning. *)
Theorem successful_scope_exit_removes_every_local_binding :
  forall incoming current pruned name,
    ScopePruneSuccess incoming current pruned ->
    incoming name = false ->
    pruned name = None.
Proof.
  intros incoming current pruned name Hprune Hlocal.
  inversion Hprune; subst pruned.
  unfold pruneScopedMetadata.
  rewrite Hlocal.
  reflexivity.
Qed.

(* Incoming metadata is not rewritten by lexical scope pruning. *)
Theorem successful_scope_exit_preserves_incoming_binding :
  forall incoming current pruned name,
    ScopePruneSuccess incoming current pruned ->
    incoming name = true ->
    pruned name = current name.
Proof.
  intros incoming current pruned name Hprune Hincoming.
  inversion Hprune; subst pruned.
  unfold pruneScopedMetadata.
  rewrite Hincoming.
  reflexivity.
Qed.

Definition bindingsForMode
  (mode : Mode)
  (context : ResourceContext) : BindingMap :=
  match mode with
  | Unrestricted => unrestrictedBindings context
  | Affine => affineBindings context
  | Linear => linearBindings context
  end.

Definition coreBindingPresent
  (context : ResourceContext)
  (name : Name)
  (meta : SurfaceBindingMeta) : bool :=
  bindingPresent name (bindingsForMode (surfaceMetaMode meta) context).

(* This is the proof-side analogue of Engine.bindingSurvives followed by the
   first-branch metadata projection. *)
Definition joinedSurfaceMetadata
  (first : SurfaceMetadata)
  (joinedCore : ResourceContext) : SurfaceMetadata :=
  fun name =>
    match first name with
    | None => None
    | Some meta =>
        if coreBindingPresent joinedCore name meta
        then Some meta
        else None
    end.

Definition JoinedMetadataAgrees
  (joined : SurfaceMetadata)
  (rest : list SurfaceMetadata) : Prop :=
  forall (name : Name) (meta : SurfaceBindingMeta),
    joined name = Some meta ->
    Forall (fun branch => branch name = Some meta) rest.

Inductive MetadataJoinSuccess
  (first : SurfaceMetadata)
  (rest : list SurfaceMetadata)
  (joinedCore : ResourceContext) : SurfaceMetadata -> Prop :=
| MetadataJoin_ok :
    JoinedMetadataAgrees
      (joinedSurfaceMetadata first joinedCore)
      rest ->
    MetadataJoinSuccess
      first rest joinedCore
      (joinedSurfaceMetadata first joinedCore).

(* PHIL-SURFACE-SCOPE-001: retained metadata is taken from the first branch and
   only when the corresponding structural Core zone survived the join. *)
Theorem joined_metadata_is_first_branch_core_survivor :
  forall first rest joinedCore joined name meta,
    MetadataJoinSuccess first rest joinedCore joined ->
    joined name = Some meta ->
    first name = Some meta /\
    coreBindingPresent joinedCore name meta = true.
Proof.
  intros first rest joinedCore joined name meta Hjoin Hjoined.
  inversion Hjoin; subst joined.
  unfold joinedSurfaceMetadata in Hjoined.
  destruct (first name) as [firstMeta |] eqn:Hfirst.
  - destruct (coreBindingPresent joinedCore name firstMeta) eqn:Hsurvives.
    + inversion Hjoined; subst firstMeta.
      split; assumption.
    + discriminate.
  - discriminate.
Qed.

(* PHIL-SURFACE-SCOPE-001: every other continuing branch must carry exactly the
   same metadata for every binding retained after the join. *)
Theorem joined_metadata_agrees_across_continuing_branches :
  forall first rest joinedCore joined name meta,
    MetadataJoinSuccess first rest joinedCore joined ->
    joined name = Some meta ->
    Forall (fun branch => branch name = Some meta) rest.
Proof.
  intros first rest joinedCore joined name meta Hjoin Hjoined.
  inversion Hjoin; subst joined.
  eapply H.
  exact Hjoined.
Qed.

Theorem non_surviving_core_binding_is_absent_from_joined_metadata :
  forall first joinedCore name meta,
    first name = Some meta ->
    coreBindingPresent joinedCore name meta = false ->
    joinedSurfaceMetadata first joinedCore name = None.
Proof.
  intros first joinedCore name meta Hfirst Habsent.
  unfold joinedSurfaceMetadata.
  rewrite Hfirst, Habsent.
  reflexivity.
Qed.

(* A complete successful surface join is the already-proved Core join plus the
   surface metadata convergence check. *)
Inductive SurfaceJoinSuccess
  (firstCore : ResourceContext)
  (firstMeta : SurfaceMetadata)
  (rest : list (ResourceContext * SurfaceMetadata))
  (joinedCore : ResourceContext)
  (joinedMeta : SurfaceMetadata) : Prop :=
| SurfaceJoin_ok :
    ContextJoinSuccess
      (firstCore :: map fst rest)
      joinedCore ->
    MetadataJoinSuccess
      firstMeta
      (map snd rest)
      joinedCore
      joinedMeta ->
    SurfaceJoinSuccess firstCore firstMeta rest joinedCore joinedMeta.

(* The surface layer does not weaken Core linear convergence. *)
Theorem successful_surface_join_preserves_core_linear_convergence :
  forall firstCore firstMeta rest joinedCore joinedMeta context,
    SurfaceJoinSuccess
      firstCore firstMeta rest joinedCore joinedMeta ->
    In context (firstCore :: map fst rest) ->
    SameBindingMap
      (linearBindings joinedCore)
      (linearBindings context).
Proof.
  intros firstCore firstMeta rest joinedCore joinedMeta context Hsurface Hin.
  inversion Hsurface; subst.
  eapply context_join_linear_converges; eauto.
Qed.

(* Likewise for unrestricted authority. *)
Theorem successful_surface_join_preserves_core_unrestricted_convergence :
  forall firstCore firstMeta rest joinedCore joinedMeta context,
    SurfaceJoinSuccess
      firstCore firstMeta rest joinedCore joinedMeta ->
    In context (firstCore :: map fst rest) ->
    SameBindingMap
      (unrestrictedBindings joinedCore)
      (unrestrictedBindings context).
Proof.
  intros firstCore firstMeta rest joinedCore joinedMeta context Hsurface Hin.
  inversion Hsurface; subst.
  eapply context_join_unrestricted_converges; eauto.
Qed.
