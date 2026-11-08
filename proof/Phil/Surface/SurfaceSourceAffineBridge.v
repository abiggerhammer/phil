From Stdlib Require Import Strings.String Bool.Bool.

From Phil.Core Require Import Syntax Context.
From Phil.Surface Require Import SurfaceFiniteContextFrame.

(*
  FSEM-01 SOURCE-AFFINE: an explicitly bounded source-mode gate and the
  existing all-zone finite-context frame relation.

  IMPORTANT: 'evidenceAdmitted' below is supplied by an external nominal
  justification authority. It is NOT proven by merely spelling mode affine,
  and it is NOT an implementation of the native nominal checker. Native
  correspondence is checked with executable source witnesses, not proved.
*)

Definition checkedSourceAffineMode
  (sourceMode : Syntax.Mode) (evidenceAdmitted : bool)
  : option Syntax.Mode :=
  match sourceMode with
  | Syntax.Affine => if evidenceAdmitted then Some Syntax.Affine else None
  | _ => None
  end.

Theorem source_affine_requires_admitted_evidence :
  forall mode evidence,
    checkedSourceAffineMode mode evidence = Some Syntax.Affine ->
    mode = Syntax.Affine /\ evidence = true.
Proof.
  intros mode evidence Hchecked.
  destruct mode; simpl in Hchecked; try discriminate.
  destruct evidence; simpl in Hchecked; try discriminate.
  split; reflexivity.
Qed.

Theorem source_affine_without_evidence_rejected :
  forall mode, checkedSourceAffineMode mode false = None.
Proof.
  destruct mode; reflexivity.
Qed.

Theorem source_affine_rejects_other_mode :
  forall evidence,
    checkedSourceAffineMode Syntax.Unrestricted evidence = None /\
    checkedSourceAffineMode Syntax.Linear evidence = None.
Proof.
  intros; split; reflexivity.
Qed.

Theorem admitted_source_affine_preserves_its_mode :
  checkedSourceAffineMode Syntax.Affine true = Some Syntax.Affine.
Proof. reflexivity. Qed.

(*
  Installation is the established Core model's exact per-name insertion.
  'insertBinding' additionally checks global freshness in all three zones.
  This theorem does not assume that a Haskell Map insert was extracted.
*)
Theorem admitted_source_affine_insert_frames_every_spectator :
  forall owner ty before after sourceMode admitted,
    checkedSourceAffineMode sourceMode admitted = Some Syntax.Affine ->
    Context.insertBinding Syntax.Affine owner ty before =
      Context.Inserted after ->
    SurfaceFiniteContextFrame.ForeignFrame owner before after /\
    Context.affineBindings after owner = Some ty /\
    Context.unrestrictedBindings after owner = None /\
    Context.linearBindings after owner = None.
Proof.
  intros owner ty before after sourceMode admitted Hmode Hinsert.
  pose proof
    (Context.insertBinding_success_exact Syntax.Affine owner ty
      before after Hinsert) as
      [_ [_ [_ [Hselected _]]]].
  simpl in Hselected.
  destruct Hselected as [Hunrestricted [Haffine Hlinear]].
  split.
  - exact
      (SurfaceFiniteContextFrame.successful_insert_frames_any_finite_context
        owner Syntax.Affine ty before after Hinsert).
  - exact (conj Haffine (conj Hunrestricted Hlinear)).
Qed.

(* A checked source affine owner that enters the loaned state cannot be
   consumed, independently of the number of unrelated bindings or loans. *)
Theorem source_affine_borrow_blocks_consumption :
  forall owner before borrowed,
    SurfaceFiniteContextFrame.startOwnedLoanModel owner before =
      Some borrowed ->
    Context.sharedLoans borrowed owner = true /\
    SurfaceFiniteContextFrame.consumeAffineModel owner borrowed = None /\
    SurfaceFiniteContextFrame.ForeignFrame owner before borrowed.
Proof.
  intros owner before borrowed Hstart.
  pose proof
    (SurfaceFiniteContextFrame.successful_loan_start_activates_exact_owner
      owner before borrowed Hstart) as Hactive.
  split.
  - exact Hactive.
  - split.
    + apply SurfaceFiniteContextFrame.borrowed_affine_owner_cannot_be_consumed.
      exact Hactive.
    + exact
        (SurfaceFiniteContextFrame.successful_loan_start_frames_any_finite_context
          owner before borrowed Hstart).
Qed.

Theorem source_affine_consume_preserves_every_spectator :
  forall owner ty before after,
    SurfaceFiniteContextFrame.consumeAffineModel owner before =
      Some (ty, after) ->
    SurfaceFiniteContextFrame.ForeignFrame owner before after /\
    Context.affineBindings after owner = None /\
    Context.linearBindings after = Context.linearBindings before /\
    Context.sharedLoans after = Context.sharedLoans before.
Proof.
  intros owner ty before after Hconsume.
  pose proof
    (SurfaceFiniteContextFrame.successful_affine_consume_frames_any_finite_context
      owner ty before after Hconsume) as Hframe.
  unfold SurfaceFiniteContextFrame.consumeAffineModel in Hconsume.
  destruct (Context.sharedLoans before owner) eqn:Hloan;
    try discriminate.
  destruct (Context.affineBindings before owner) as [found |] eqn:Hfound;
    try discriminate.
  inversion Hconsume; subst after; clear Hconsume.
  split.
  - exact Hframe.
  - split.
    + simpl. unfold Context.deleteBinding.
      now rewrite String.eqb_refl.
    + split; reflexivity.
Qed.

(*
  Affine discarding means that the owner does not create a mandatory linear
  completion debt. This bounded model explicitly removes one unloaned affine
  binding; real function-exit dropping in Haskell is checked separately.
*)
Definition discardUnloanedAffineModel
  (owner : Syntax.Name) (ctx : Context.ResourceContext)
  : option Context.ResourceContext :=
  if Context.sharedLoans ctx owner then None else
  match Context.affineBindings ctx owner with
  | Some _ => Some (Context.mkResourceContext
      (Context.unrestrictedBindings ctx)
      (Context.deleteBinding owner (Context.affineBindings ctx))
      (Context.linearBindings ctx)
      (Context.sharedLoans ctx))
  | None => None
  end.

Theorem successful_affine_discard_is_exact_and_frames :
  forall owner before after,
    discardUnloanedAffineModel owner before = Some after ->
    Context.affineBindings after owner = None /\
    Context.linearBindings after = Context.linearBindings before /\
    Context.sharedLoans after = Context.sharedLoans before /\
    SurfaceFiniteContextFrame.ForeignFrame owner before after.
Proof.
  intros owner before after Hdrop.
  unfold discardUnloanedAffineModel in Hdrop.
  destruct (Context.sharedLoans before owner) eqn:Hloan;
    try discriminate.
  destruct (Context.affineBindings before owner) as [found |] eqn:Hfound;
    try discriminate.
  inversion Hdrop; subst after; clear Hdrop.
  split.
  - simpl. unfold Context.deleteBinding.
    now rewrite String.eqb_refl.
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * intros other Hother.
        simpl.
        split; [reflexivity |].
        split.
        -- unfold Context.deleteBinding.
           now rewrite Hother.
        -- split; reflexivity.
Qed.

Theorem borrowed_affine_cannot_be_discarded :
  forall owner ctx,
    Context.sharedLoans ctx owner = true ->
    discardUnloanedAffineModel owner ctx = None.
Proof.
  intros owner ctx Hloan.
  unfold discardUnloanedAffineModel.
  now rewrite Hloan.
Qed.

(* Open: source-mode syntax -> native admitted justification attestation;
   Haskell Text/Map/Set -> Rocq String/extensional lookup universal refinement;
   recursive source bodies, captures/joins, exact native error-carrier proof.
   No Admitted, Axiom or Parameter declarations are introduced. *)
