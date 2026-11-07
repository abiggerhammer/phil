From Stdlib Require Import Bool.Bool Strings.String Lists.List.

From Phil.Core Require Import Syntax Context BindingSemantics.
From Phil.Surface Require Import
  SurfaceBinderNameEncoding SurfaceDeclarationIdentityBridge
  SurfaceBorrowLoanStateCorrespondence.

Import ListNotations.

(*
  FSEM-01: represented owner identity and observable loan checkpoints.

  #1631 proves canonical name injection over Rocq ASCII strings; #1632
  relates a normalized BinderKey to a concrete (root string, ordinal)
  under a finite, NoDup catalog. #1627 provides *model* start/end
  and Context.consumeLinear proofs. This module composes those models
  into two precisely bounded checkpoint shapes.

  These are not the Haskell evaluator's transition proofs. The actual
  #1626 production checkpoints are tested against these shapes by the
  paired Haskell trace test, using the real Grammar-v1 parser, binder
  encoder/decoder and checker. Unicode Text/Rocq String representation,
  catalog provenance, runtime-value escape detection, and the Haskell
  Map/Set implementation remain explicit TCB/refinement obligations.
*)

Inductive ModeledBorrowPhase : Type :=
| ModelBeforeLoan
| ModelLoanStarted
| ModelBodyResult (escaped : bool)
| ModelLoanClosed
| ModelOwnerReturned
| ModelEscapeRejected.

Definition admittedPositivePhases : list ModeledBorrowPhase :=
  [ModelBeforeLoan; ModelLoanStarted; ModelBodyResult false;
   ModelLoanClosed; ModelOwnerReturned].

Definition admittedEscapePhases : list ModeledBorrowPhase :=
  [ModelBeforeLoan; ModelLoanStarted; ModelBodyResult true;
   ModelEscapeRejected].

Definition linearOwnerPresent
  (owner : Syntax.Name) (ctx : Context.ResourceContext) : bool :=
  match Context.linearBindings ctx owner with
  | Some _ => true
  | None => false
  end.

Definition ownerLoanState
  (owner : Syntax.Name) (ctx : Context.ResourceContext) : bool * bool :=
  (linearOwnerPresent owner ctx, Context.sharedLoans ctx owner).

Theorem represented_positive_borrow_checkpoint_model :
  forall
    (catalog : list string)
    (normalized : BindingSemantics.BinderKey)
    (concrete : SurfaceBinderNameEncoding.TextBinderKey)
    (context : Context.ResourceContext) (ty : Syntax.Ty),
    NoDup catalog ->
    SurfaceDeclarationIdentityBridge.representsBinderKey
      catalog normalized concrete ->
    Context.linearBindings context
      (SurfaceBinderNameEncoding.encodeTextBinderKey concrete) = Some ty ->
    Context.sharedLoans context
      (SurfaceBinderNameEncoding.encodeTextBinderKey concrete) = false ->
    exists started closed returned,
      SurfaceBorrowLoanStateCorrespondence.startLinearSharedLoan
        (SurfaceBinderNameEncoding.encodeTextBinderKey concrete) context =
        Some started /\
      SurfaceBorrowLoanStateCorrespondence.endLinearSharedLoan
        (SurfaceBinderNameEncoding.encodeTextBinderKey concrete) started =
        Some closed /\
      Context.consumeLinear
        (SurfaceBinderNameEncoding.encodeTextBinderKey concrete) closed =
        Context.Consumed ty returned /\
      [ownerLoanState (SurfaceBinderNameEncoding.encodeTextBinderKey concrete)
         context;
       ownerLoanState (SurfaceBinderNameEncoding.encodeTextBinderKey concrete)
         started;
       ownerLoanState (SurfaceBinderNameEncoding.encodeTextBinderKey concrete)
         started;
       ownerLoanState (SurfaceBinderNameEncoding.encodeTextBinderKey concrete)
         closed;
       ownerLoanState (SurfaceBinderNameEncoding.encodeTextBinderKey concrete)
         returned] =
      [(true, false); (true, true); (true, true);
       (true, false); (false, false)] /\
      SurfaceDeclarationIdentityBridge.representsBinderKey
        catalog normalized concrete.
Proof.
  intros catalog normalized concrete context ty Hnod Hrepresented Hty Hfree.
  set (owner := SurfaceBinderNameEncoding.encodeTextBinderKey concrete).
  pose proof
    (SurfaceBorrowLoanStateCorrespondence.end_after_start_restores_loan_membership
      owner context ty Hfree Hty)
    as (started & closed & Hstart & Hend & HrestoredLoans & HrestoredBindings).
  pose proof
    (SurfaceBorrowLoanStateCorrespondence.start_linear_loan_requires_present_unloaned_owner
      owner context started Hstart) as
    [_ [_ [HstartedLoan HstartedBindings]]].
  pose proof
    (SurfaceBorrowLoanStateCorrespondence.end_linear_loan_requires_active_owner
      owner started closed Hend) as
    [_ [HclosedLoan HclosedBindings]].
  assert (HstartedTy : Context.linearBindings started owner = Some ty).
  { rewrite HstartedBindings. exact Hty. }
  assert (HclosedTy : Context.linearBindings closed owner = Some ty).
  { rewrite HclosedBindings. exact HstartedTy. }
  set (returned := Context.mkResourceContext
    (Context.unrestrictedBindings closed)
    (Context.affineBindings closed)
    (Context.deleteBinding owner (Context.linearBindings closed))
    (Context.sharedLoans closed)).
  assert (Hconsume : Context.consumeLinear owner closed =
                     Context.Consumed ty returned).
  { unfold Context.consumeLinear.
    rewrite HclosedLoan, HclosedTy.
    reflexivity. }
  pose proof (Context.consumeLinear_success_exact
    owner closed returned ty Hconsume) as
    [_ [HreturnedAbsent [_ [_ [_ HreturnedLoans]]]]].
  assert (HreturnedFree : Context.sharedLoans returned owner = false).
  { rewrite HreturnedLoans. exact HclosedLoan. }
  assert (HclosedFree : Context.sharedLoans closed owner = false)
    by exact HclosedLoan.
  exists started, closed, returned.
  split; [exact Hstart|].
  split; [exact Hend|].
  split; [exact Hconsume|].
  split; [|exact Hrepresented].
  unfold ownerLoanState, linearOwnerPresent.
  rewrite Hty, Hfree.
  rewrite HstartedTy, HstartedLoan.
  rewrite HclosedTy, HclosedFree.
  rewrite HreturnedAbsent, HreturnedFree.
  reflexivity.
Qed.

Theorem represented_escape_rejection_prefix_model :
  forall
    (catalog : list string)
    (normalized : BindingSemantics.BinderKey)
    (concrete : SurfaceBinderNameEncoding.TextBinderKey)
    (context started : Context.ResourceContext)
    (ty : Syntax.Ty),
    NoDup catalog ->
    SurfaceDeclarationIdentityBridge.representsBinderKey
      catalog normalized concrete ->
    Context.linearBindings context
      (SurfaceBinderNameEncoding.encodeTextBinderKey concrete) = Some ty ->
    Context.sharedLoans context
      (SurfaceBinderNameEncoding.encodeTextBinderKey concrete) = false ->
    SurfaceBorrowLoanStateCorrespondence.startLinearSharedLoan
      (SurfaceBinderNameEncoding.encodeTextBinderKey concrete)
      context = Some started ->
    [ownerLoanState (SurfaceBinderNameEncoding.encodeTextBinderKey concrete)
        context;
     ownerLoanState (SurfaceBinderNameEncoding.encodeTextBinderKey concrete)
        started;
     ownerLoanState (SurfaceBinderNameEncoding.encodeTextBinderKey concrete)
        started;
     ownerLoanState (SurfaceBinderNameEncoding.encodeTextBinderKey concrete)
        started] =
    [(true, false); (true, true); (true, true); (true, true)] /\
    SurfaceDeclarationIdentityBridge.representsBinderKey
      catalog normalized concrete.
Proof.
  intros catalog normalized concrete context started ty
    Hnod Hrepresented Hty Hfree Hstart.
  set (owner := SurfaceBinderNameEncoding.encodeTextBinderKey concrete).
  pose proof
    (SurfaceBorrowLoanStateCorrespondence.start_linear_loan_requires_present_unloaned_owner
      owner context started Hstart) as
    [_ [_ [HstartedLoan HstartedBindings]]].
  assert (HstartedTy : Context.linearBindings started owner = Some ty).
  { rewrite HstartedBindings. exact Hty. }
  split; [|exact Hrepresented].
  unfold ownerLoanState, linearOwnerPresent.
  rewrite Hty, Hfree.
  rewrite HstartedTy, HstartedLoan.
  reflexivity.
Qed.

Theorem rejected_trace_has_no_loan_close :
  ~ In ModelLoanClosed admittedEscapePhases.
Proof.
  simpl.
  intros [H | [H | [H | [H | []]]]];
    discriminate.
Qed.

Theorem rejected_trace_has_no_terminal_owner_return :
  ~ In ModelOwnerReturned admittedEscapePhases.
Proof.
  simpl.
  intros [H | [H | [H | [H | []]]]];
    discriminate.
Qed.

Theorem successful_trace_closes_before_terminal_return :
  forall first second,
    admittedPositivePhases ++ [first; second] =
    [ModelBeforeLoan; ModelLoanStarted; ModelBodyResult false;
     ModelLoanClosed; ModelOwnerReturned; first; second].
Proof. reflexivity. Qed.

(*
  The negative model is a PREFIX: it does not pretend to have executed
  endSharedLoan or a terminal return. Its actual error classification
  and non-mutating error snapshot are executable Haskell observations,
  not an extracted small-step semantics or an Haskell-refinement theorem.
*)
