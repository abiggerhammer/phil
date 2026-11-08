From Stdlib Require Import Strings.String Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context.

(*
  FSEM-01 finite-context lookup/frame model. Rocq Name is String and Ty is
  abstract; the Haskell Map/Set codec is NOT assumed definitionally equal.
  An independent Haskell test checks canonical finite-list snapshots of
  real Core.Context maps, including adversarial mutations.
*)

Record FiniteSnapshot : Type := mkFiniteSnapshot {
  finiteUnrestricted : list (Name * Ty);
  finiteAffine : list (Name * Ty);
  finiteLinear : list (Name * Ty);
  finiteLoans : list Name
}.

Fixpoint lookupFinite (entries : list (Name * Ty)) (query : Name) : option Ty :=
  match entries with
  | [] => None
  | (name, ty) :: rest =>
      if String.eqb query name then Some ty else lookupFinite rest query
  end.

Definition loanInFinite (loans : list Name) (query : Name) : bool :=
  existsb (fun candidate => String.eqb query candidate) loans.

Definition reifyFinite (snap : FiniteSnapshot) : Context.ResourceContext :=
  Context.mkResourceContext
    (lookupFinite (finiteUnrestricted snap))
    (lookupFinite (finiteAffine snap))
    (lookupFinite (finiteLinear snap))
    (loanInFinite (finiteLoans snap)).

Definition ExactFiniteRelation (snap : FiniteSnapshot)
  (context : Context.ResourceContext) : Prop :=
  forall query,
    Context.unrestrictedBindings context query =
      lookupFinite (finiteUnrestricted snap) query /\
    Context.affineBindings context query =
      lookupFinite (finiteAffine snap) query /\
    Context.linearBindings context query =
      lookupFinite (finiteLinear snap) query /\
    Context.sharedLoans context query =
      loanInFinite (finiteLoans snap) query.

Theorem reify_finite_has_exact_four_lookup_projections :
  forall snap, ExactFiniteRelation snap (reifyFinite snap).
Proof.
  intros snap query.
  repeat split; reflexivity.
Qed.

Definition finiteNames (snap : FiniteSnapshot) : list Name :=
  map fst (finiteUnrestricted snap) ++
  map fst (finiteAffine snap) ++ map fst (finiteLinear snap).

(* The Haskell test checks sorted, unique binding lists, disjoint structural
   zones and loans owned by affine/linear bindings. These assumptions are
   stated, not axiomatized or inferred from arbitrary user-supplied snapshots. *)
Definition ValidFinite (snap : FiniteSnapshot) : Prop :=
  NoDup (finiteNames snap) /\
  NoDup (finiteLoans snap) /\
  (forall name, In name (finiteLoans snap) ->
    exists ty,
      lookupFinite (finiteAffine snap) name = Some ty \/
      lookupFinite (finiteLinear snap) name = Some ty).

Theorem valid_finite_loan_has_a_restricted_owner :
  forall snap owner,
    ValidFinite snap -> In owner (finiteLoans snap) ->
    exists ty,
      lookupFinite (finiteAffine snap) owner = Some ty \/
      lookupFinite (finiteLinear snap) owner = Some ty.
Proof.
  intros snap owner [_ [_ Hloans]] Hin.
  now apply Hloans.
Qed.

Lemma finite_lookup_cons_target :
  forall name ty entries,
    lookupFinite ((name, ty) :: entries) name = Some ty.
Proof.
  intros name ty entries.
  simpl.
  now rewrite String.eqb_refl.
Qed.

Lemma finite_lookup_cons_foreign :
  forall owner other ty entries,
    String.eqb other owner = false ->
    lookupFinite ((owner, ty) :: entries) other =
      lookupFinite entries other.
Proof.
  intros owner other ty entries Hother.
  simpl.
  now rewrite Hother.
Qed.

(* All four entire resource domains frame across single-name updates.
   No bound on the number of spectators or their modes is imposed. *)
Definition ForeignFrame (owner : Name)
  (before after : Context.ResourceContext) : Prop :=
  forall query,
    String.eqb query owner = false ->
    Context.unrestrictedBindings after query =
      Context.unrestrictedBindings before query /\
    Context.affineBindings after query =
      Context.affineBindings before query /\
    Context.linearBindings after query =
      Context.linearBindings before query /\
    Context.sharedLoans after query =
      Context.sharedLoans before query.

Theorem foreign_frame_is_transitive :
  forall owner first second third,
    ForeignFrame owner first second ->
    ForeignFrame owner second third ->
    ForeignFrame owner first third.
Proof.
  intros owner first second third Hfirst Hsecond query Hneq.
  specialize (Hfirst query Hneq).
  specialize (Hsecond query Hneq).
  destruct Hfirst as [Hu1 [Ha1 [Hl1 Hloan1]]].
  destruct Hsecond as [Hu2 [Ha2 [Hl2 Hloan2]]].
  repeat split; congruence.
Qed.

Theorem successful_insert_frames_any_finite_context :
  forall owner mode ty before after,
    Context.insertBinding mode owner ty before = Context.Inserted after ->
    ForeignFrame owner before after.
Proof.
  intros owner mode ty before after Hinsert query Hneq.
  pose proof (Context.insertBinding_success_exact
    mode owner ty before after Hinsert) as
    [_ [_ [_ [_ [Hothers Hloans]]]]].
  specialize (Hothers query Hneq).
  destruct Hothers as [Hu [Ha Hl]].
  repeat split; try assumption.
  now rewrite Hloans.
Qed.

Theorem successful_linear_consume_frames_any_finite_context :
  forall owner ty before after,
    Context.consumeLinear owner before = Context.Consumed ty after ->
    ForeignFrame owner before after.
Proof.
  intros owner ty before after Hconsume query Hneq.
  pose proof (Context.consumeLinear_success_exact
    owner before after ty Hconsume) as
    [_ [_ [Hlinear [Hunrestricted [Haffine Hloans]]]]].
  specialize (Hlinear query Hneq).
  repeat split; try assumption; congruence.
Qed.

(* The following affine/loan functions are extensional models. In particular,
   None is coarser than the native Haskell CheckError constructors. No full
   native-to-model error simulation theorem is claimed. *)
Definition readUnrestricted (owner : Name)
  (context : Context.ResourceContext) : option (Ty * Context.ResourceContext) :=
  match Context.unrestrictedBindings context owner with
  | Some ty => Some (ty, context)
  | None => None
  end.

Theorem successful_unrestricted_read_is_exact_identity :
  forall owner before ty after,
    readUnrestricted owner before = Some (ty, after) ->
    after = before.
Proof.
  intros owner before ty after Hread.
  unfold readUnrestricted in Hread.
  destruct (Context.unrestrictedBindings before owner) as [found |];
    try discriminate.
  now inversion Hread.
Qed.

Definition consumeAffineModel (owner : Name)
  (ctx : Context.ResourceContext) : option (Ty * Context.ResourceContext) :=
  if Context.sharedLoans ctx owner then None else
  match Context.affineBindings ctx owner with
  | None => None
  | Some ty => Some (ty, Context.mkResourceContext
      (Context.unrestrictedBindings ctx)
      (Context.deleteBinding owner (Context.affineBindings ctx))
      (Context.linearBindings ctx)
      (Context.sharedLoans ctx))
  end.

Theorem successful_affine_consume_frames_any_finite_context :
  forall owner ty before after,
    consumeAffineModel owner before = Some (ty, after) ->
    ForeignFrame owner before after.
Proof.
  intros owner ty before after Hconsume.
  unfold consumeAffineModel in Hconsume.
  destruct (Context.sharedLoans before owner) eqn:Hborrow;
    try discriminate.
  destruct (Context.affineBindings before owner) as [found |] eqn:Hfound;
    try discriminate.
  inversion Hconsume; subst after; clear Hconsume.
  intros query Hneq; simpl.
  repeat split; try reflexivity.
  unfold Context.deleteBinding.
  now rewrite Hneq.
Qed.

Theorem borrowed_affine_owner_cannot_be_consumed :
  forall owner ctx,
    Context.sharedLoans ctx owner = true ->
    consumeAffineModel owner ctx = None.
Proof.
  intros owner ctx Hloan.
  unfold consumeAffineModel.
  now rewrite Hloan.
Qed.

Theorem borrowed_linear_owner_cannot_be_consumed :
  forall owner ctx,
    Context.sharedLoans ctx owner = true ->
    Context.consumeLinear owner ctx =
      Context.ConsumeError (Context.OwnerBorrowed owner).
Proof.
  intros owner ctx Hloan.
  unfold Context.consumeLinear.
  now rewrite Hloan.
Qed.

Definition setOwnerLoan (owner : Name) (active : bool)
  (ctx : Context.ResourceContext) : Context.ResourceContext :=
  Context.mkResourceContext
    (Context.unrestrictedBindings ctx)
    (Context.affineBindings ctx)
    (Context.linearBindings ctx)
    (fun query => if String.eqb query owner
      then active else Context.sharedLoans ctx query).

Definition startOwnedLoanModel (owner : Name)
  (ctx : Context.ResourceContext) : option Context.ResourceContext :=
  if Context.sharedLoans ctx owner then None else
  if (Context.bindingPresent owner (Context.affineBindings ctx)
    || Context.bindingPresent owner (Context.linearBindings ctx))%bool
  then Some (setOwnerLoan owner true ctx) else None.

Definition endOwnedLoanModel (owner : Name)
  (ctx : Context.ResourceContext) : option Context.ResourceContext :=
  if Context.sharedLoans ctx owner
  then Some (setOwnerLoan owner false ctx) else None.

Theorem setting_loan_frames_any_finite_context :
  forall owner active ctx,
    ForeignFrame owner ctx (setOwnerLoan owner active ctx).
Proof.
  intros owner active ctx query Hneq.
  unfold setOwnerLoan; simpl.
  repeat split; try reflexivity.
  now rewrite Hneq.
Qed.

Theorem successful_loan_start_frames_any_finite_context :
  forall owner before after,
    startOwnedLoanModel owner before = Some after ->
    ForeignFrame owner before after.
Proof.
  intros owner before after Hstart.
  unfold startOwnedLoanModel in Hstart.
  destruct (Context.sharedLoans before owner) eqn:Hactive;
    try discriminate.
  destruct ((Context.bindingPresent owner (Context.affineBindings before)
    || Context.bindingPresent owner (Context.linearBindings before))%bool)
      eqn:Hpresent; try discriminate.
  inversion Hstart; subst after; clear Hstart.
  apply setting_loan_frames_any_finite_context.
Qed.

Theorem successful_loan_end_frames_any_finite_context :
  forall owner before after,
    endOwnedLoanModel owner before = Some after ->
    ForeignFrame owner before after.
Proof.
  intros owner before after Hend.
  unfold endOwnedLoanModel in Hend.
  destruct (Context.sharedLoans before owner) eqn:Hactive;
    try discriminate.
  inversion Hend; subst after; clear Hend.
  apply setting_loan_frames_any_finite_context.
Qed.

Theorem successful_loan_start_activates_exact_owner :
  forall owner before after,
    startOwnedLoanModel owner before = Some after ->
    Context.sharedLoans after owner = true.
Proof.
  intros owner before after Hstart.
  unfold startOwnedLoanModel in Hstart.
  destruct (Context.sharedLoans before owner) eqn:Hactive;
    try discriminate.
  destruct ((Context.bindingPresent owner (Context.affineBindings before)
    || Context.bindingPresent owner (Context.linearBindings before))%bool)
      eqn:Hpresent; try discriminate.
  inversion Hstart; subst after; clear Hstart.
  unfold setOwnerLoan; simpl.
  now rewrite String.eqb_refl.
Qed.

Theorem successful_loan_end_clears_exact_owner :
  forall owner before after,
    endOwnedLoanModel owner before = Some after ->
    Context.sharedLoans after owner = false.
Proof.
  intros owner before after Hend.
  unfold endOwnedLoanModel in Hend.
  destruct (Context.sharedLoans before owner) eqn:Hactive;
    try discriminate.
  inversion Hend; subst after; clear Hend.
  unfold setOwnerLoan; simpl.
  now rewrite String.eqb_refl.
Qed.

Theorem loan_start_rejects_borrowed_owner :
  forall owner ctx,
    Context.sharedLoans ctx owner = true ->
    startOwnedLoanModel owner ctx = None.
Proof.
  intros owner ctx Hactive.
  unfold startOwnedLoanModel.
  now rewrite Hactive.
Qed.

Theorem loan_start_rejects_unrestricted_only_owner :
  forall owner ctx,
    Context.sharedLoans ctx owner = false ->
    Context.affineBindings ctx owner = None ->
    Context.linearBindings ctx owner = None ->
    startOwnedLoanModel owner ctx = None.
Proof.
  intros owner ctx Hloan Haffine Hlinear.
  unfold startOwnedLoanModel.
  rewrite Hloan.
  unfold Context.bindingPresent.
  now rewrite Haffine, Hlinear.
Qed.

(* These hold for arbitrary finite-context *models*, independently of list
   length, including unrelated active loans. They are not a proof of Haskell
   Map/Set semantics, source typing, join transitions, or full error paths. *)
