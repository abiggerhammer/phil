From Stdlib Require Import Strings.String Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context.
From Phil.Surface Require Import SurfaceFiniteContextFrame.

(*
  FSEM-01 CORR-4: computed finite Linear consume/insert decisions
  have exact outcomes under the extensional Context.ResourceContext model.
  The relation from an arbitrary native Haskell source cut to the model
  remains an independently TESTED finite premise, not a universal proof.
  Rocq UnknownLinearBinding is coarser than native WrongStructuralMode.
*)

Module Finite := SurfaceFiniteContextFrame.

Fixpoint dropFinite
  (owner : Syntax.Name) (entries : list (Syntax.Name * Syntax.Ty))
  : list (Syntax.Name * Syntax.Ty) :=
  match entries with
  | [] => []
  | (name, ty) :: tail =>
      if String.eqb name owner then dropFinite owner tail
      else (name, ty) :: dropFinite owner tail
  end.

Lemma drop_finite_lookup_exact :
  forall entries owner query,
    Finite.lookupFinite (dropFinite owner entries) query =
      if String.eqb query owner then None
      else Finite.lookupFinite entries query.
Proof.
  induction entries as [| [key value] tail IH]; intros owner query.
  - simpl. now destruct (String.eqb query owner).
  - simpl.
    destruct (String.eqb key owner) eqn:Hkey.
    + apply String.eqb_eq in Hkey. subst key.
      rewrite (IH owner query).
      now destruct (String.eqb query owner).
    + simpl.
      destruct (String.eqb query key) eqn:Hquery.
      * apply String.eqb_eq in Hquery. subst query.
        rewrite Hkey. simpl. reflexivity.
      * rewrite (IH owner query).
        now destruct (String.eqb query owner).
Qed.

Inductive FiniteLinearConsume : Type :=
| FiniteConsumed : Syntax.Ty -> Finite.FiniteSnapshot -> FiniteLinearConsume
| FiniteBorrowed : FiniteLinearConsume
| FiniteMissing : FiniteLinearConsume.

Definition consumeFiniteLinear
  (owner : Syntax.Name) (before : Finite.FiniteSnapshot)
  : FiniteLinearConsume :=
  if Finite.loanInFinite (Finite.finiteLoans before) owner
  then FiniteBorrowed
  else match Finite.lookupFinite (Finite.finiteLinear before) owner with
       | Some ty => FiniteConsumed ty
           (Finite.mkFiniteSnapshot
             (Finite.finiteUnrestricted before)
             (Finite.finiteAffine before)
             (dropFinite owner (Finite.finiteLinear before))
             (Finite.finiteLoans before))
       | None => FiniteMissing
       end.

Theorem corr4_finite_linear_consume_exact_decision :
  forall snap ctx owner,
    Finite.ExactFiniteRelation snap ctx ->
    match consumeFiniteLinear owner snap with
    | FiniteBorrowed =>
        Context.consumeLinear owner ctx =
          Context.ConsumeError (Context.OwnerBorrowed owner)
    | FiniteMissing =>
        Context.consumeLinear owner ctx =
          Context.ConsumeError (Context.UnknownLinearBinding owner)
    | FiniteConsumed ty successor =>
        exists next,
          Context.consumeLinear owner ctx = Context.Consumed ty next /\
          Finite.ExactFiniteRelation successor next
    end.
Proof.
  intros snap ctx owner Hrel.
  destruct (Hrel owner) as [_ [_ [Hlinear Hloan]]].
  unfold consumeFiniteLinear.
  rewrite <- Hloan.
  destruct (Context.sharedLoans ctx owner) eqn:Hactive.
  - unfold Context.consumeLinear. now rewrite Hactive.
  - rewrite <- Hlinear.
    destruct (Context.linearBindings ctx owner) as [found |] eqn:Hfound.
    + exists (Context.mkResourceContext
        (Context.unrestrictedBindings ctx)
        (Context.affineBindings ctx)
        (Context.deleteBinding owner (Context.linearBindings ctx))
        (Context.sharedLoans ctx)).
      split.
      * unfold Context.consumeLinear.
        now rewrite Hactive, Hfound.
      * intros query.
        destruct (Hrel query) as [Hu [Ha [Hl Hloans]]].
        simpl.
        repeat split.
        -- exact Hu.
        -- exact Ha.
        -- unfold Context.deleteBinding.
           rewrite (drop_finite_lookup_exact
             (Finite.finiteLinear snap) owner query).
           destruct (String.eqb query owner);
             [reflexivity | exact Hl].
        -- exact Hloans.
    + unfold Context.consumeLinear.
      now rewrite Hactive, Hfound.
Qed.

Definition presentFinite (value : option Syntax.Ty) : bool :=
  match value with
  | Some _ => true
  | None => false
  end.

Definition occupiedFinite (snap : Finite.FiniteSnapshot)
  (owner : Syntax.Name) : bool :=
  (presentFinite (Finite.lookupFinite (Finite.finiteUnrestricted snap) owner)
   || presentFinite (Finite.lookupFinite (Finite.finiteAffine snap) owner)
   || presentFinite (Finite.lookupFinite (Finite.finiteLinear snap) owner))%bool.

Inductive FiniteLinearInsert : Type :=
| FiniteInserted : Finite.FiniteSnapshot -> FiniteLinearInsert
| FiniteDuplicate : FiniteLinearInsert.

Definition insertFiniteLinear
  (owner : Syntax.Name) (ty : Syntax.Ty)
  (before : Finite.FiniteSnapshot) : FiniteLinearInsert :=
  if occupiedFinite before owner
  then FiniteDuplicate
  else FiniteInserted
    (Finite.mkFiniteSnapshot
      (Finite.finiteUnrestricted before)
      (Finite.finiteAffine before)
      ((owner, ty) :: Finite.finiteLinear before)
      (Finite.finiteLoans before)).

Lemma corr4_occupied_finite_matches_context :
  forall snap ctx owner,
    Finite.ExactFiniteRelation snap ctx ->
    Context.bindingExists owner ctx = occupiedFinite snap owner.
Proof.
  intros snap ctx owner Hrel.
  destruct (Hrel owner) as [Hu [Ha [Hl _]]].
  unfold Context.bindingExists, Context.bindingPresent,
    occupiedFinite, presentFinite.
  now rewrite Hu, Ha, Hl.
Qed.

Theorem corr4_finite_linear_insert_exact_decision :
  forall snap ctx owner ty,
    Finite.ExactFiniteRelation snap ctx ->
    match insertFiniteLinear owner ty snap with
    | FiniteDuplicate =>
        Context.insertBinding Syntax.Linear owner ty ctx =
          Context.InsertError (Context.DuplicateBinding owner)
    | FiniteInserted successor =>
        exists next,
          Context.insertBinding Syntax.Linear owner ty ctx =
            Context.Inserted next /\
          Finite.ExactFiniteRelation successor next
    end.
Proof.
  intros snap ctx owner ty Hrel.
  unfold insertFiniteLinear.
  rewrite <- (corr4_occupied_finite_matches_context
    snap ctx owner Hrel).
  destruct (Context.bindingExists owner ctx) eqn:Hexists.
  - unfold Context.insertBinding.
    now rewrite Hexists.
  - exists (Context.mkResourceContext
      (Context.unrestrictedBindings ctx)
      (Context.affineBindings ctx)
      (Context.insertBindingMap owner ty (Context.linearBindings ctx))
      (Context.sharedLoans ctx)).
    split.
    + unfold Context.insertBinding.
      now rewrite Hexists.
    + intros query.
      destruct (Hrel query) as [Hu [Ha [Hl Hloans]]].
      simpl.
      repeat split.
      * exact Hu.
      * exact Ha.
      * unfold Context.insertBindingMap.
        destruct (String.eqb query owner);
          [reflexivity | exact Hl].
      * exact Hloans.
Qed.

Theorem corr4_loan_precedes_present_linear_owner :
  forall snap owner ty,
    Finite.loanInFinite (Finite.finiteLoans snap) owner = true ->
    Finite.lookupFinite (Finite.finiteLinear snap) owner = Some ty ->
    consumeFiniteLinear owner snap = FiniteBorrowed.
Proof.
  intros snap owner ty Hloan _.
  unfold consumeFiniteLinear.
  now rewrite Hloan.
Qed.

Theorem corr4_duplicate_precedes_linear_insertion :
  forall snap owner ty,
    occupiedFinite snap owner = true ->
    insertFiniteLinear owner ty snap = FiniteDuplicate.
Proof.
  intros snap owner ty Hoccupied.
  unfold insertFiniteLinear.
  now rewrite Hoccupied.
Qed.

Print Assumptions drop_finite_lookup_exact.
Print Assumptions corr4_finite_linear_consume_exact_decision.
Print Assumptions corr4_occupied_finite_matches_context.
Print Assumptions corr4_finite_linear_insert_exact_decision.
Print Assumptions corr4_loan_precedes_present_linear_owner.
Print Assumptions corr4_duplicate_precedes_linear_insertion.
