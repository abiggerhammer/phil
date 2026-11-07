From Stdlib Require Import Strings.String Bool.Bool Arith.PeanoNat Lia.

From Phil.Core Require Import
  Syntax Context BindingSemantics ResourceJoin ResourceScope.
From Phil.Surface Require Import
  SurfaceBinderScopeCore SurfaceLetPatternScope SurfaceBorrowViewScope.

(*
  FSEM-01: first bounded source-binder / resource-loan model bridge.

  Core.Context.v models the Name-keyed resource maps as lookup functions.
  ResourceScope.v models loan membership over abstract nat ResourceOwners.
  This file relates the two *under explicitly supplied injective encodings*
  of existing BinderKeys to the two carriers.

  The candidate start/end operations below reproduce the LINEAR-OWNER branch
  of Phil.Core.Context.startSharedLoan/endSharedLoan (Haskell). This is an
  extensional Rocq model, not extraction, a proof about Haskell Map/Set, or a
  parser/elaborator simulation. In particular, this module does not prove
  runtime value non-escape or discharge source "satisfies C".
*)

Definition setCoreLoan
  (owner : Syntax.Name) (active : bool)
  (context : Context.ResourceContext) : Context.ResourceContext :=
  Context.mkResourceContext
    (Context.unrestrictedBindings context)
    (Context.affineBindings context)
    (Context.linearBindings context)
    (fun candidate : Syntax.Name =>
       if String.eqb candidate owner
       then active
       else Context.sharedLoans context candidate).

(* The admitted FSEM-01 Bytes[N] owner has intrinsic Linear mode.
   An already-loaned or absent linear owner is outside the success result. *)
Definition startLinearSharedLoan
  (owner : Syntax.Name) (context : Context.ResourceContext)
  : option Context.ResourceContext :=
  if Context.sharedLoans context owner then None
  else
    match Context.linearBindings context owner with
    | Some _ => Some (setCoreLoan owner true context)
    | None => None
    end.

Definition endLinearSharedLoan
  (owner : Syntax.Name) (context : Context.ResourceContext)
  : option Context.ResourceContext :=
  if Context.sharedLoans context owner
  then Some (setCoreLoan owner false context)
  else None.

Definition setAbstractLoan
  (owner : ResourceJoin.ResourceOwner) (active : bool)
  (loans : ResourceScope.LoanSet) : ResourceScope.LoanSet :=
  fun candidate : ResourceJoin.ResourceOwner =>
    if Nat.eqb candidate owner then active else loans candidate.

Theorem set_core_loan_has_exact_target :
  forall owner active context,
    Context.sharedLoans (setCoreLoan owner active context) owner = active.
Proof.
  intros owner active context.
  unfold setCoreLoan; simpl.
  now rewrite String.eqb_refl.
Qed.

Theorem set_core_loan_preserves_other_names :
  forall owner other active context,
    String.eqb other owner = false ->
    Context.sharedLoans (setCoreLoan owner active context) other =
    Context.sharedLoans context other.
Proof.
  intros owner other active context Hother.
  unfold setCoreLoan; simpl.
  now rewrite Hother.
Qed.

Theorem set_core_loan_preserves_all_binding_maps :
  forall owner active context,
    Context.unrestrictedBindings (setCoreLoan owner active context) =
      Context.unrestrictedBindings context /\
    Context.affineBindings (setCoreLoan owner active context) =
      Context.affineBindings context /\
    Context.linearBindings (setCoreLoan owner active context) =
      Context.linearBindings context.
Proof.
  intros; repeat split; reflexivity.
Qed.

Theorem start_linear_loan_requires_present_unloaned_owner :
  forall owner context next,
    startLinearSharedLoan owner context = Some next ->
    Context.sharedLoans context owner = false /\
    (exists ty, Context.linearBindings context owner = Some ty) /\
    Context.sharedLoans next owner = true /\
    Context.linearBindings next owner = Context.linearBindings context owner.
Proof.
  intros owner context next Hstart.
  unfold startLinearSharedLoan in Hstart.
  destruct (Context.sharedLoans context owner) eqn:Hfree;
    try discriminate.
  destruct (Context.linearBindings context owner) as [ty |] eqn:Hlinear;
    try discriminate.
  inversion Hstart; subst next; clear Hstart.
  repeat split.
  - exact Hfree.
  - exists ty. exact Hlinear.
  - apply set_core_loan_has_exact_target.
  - reflexivity.
Qed.

Theorem end_linear_loan_requires_active_owner :
  forall owner context next,
    endLinearSharedLoan owner context = Some next ->
    Context.sharedLoans context owner = true /\
    Context.sharedLoans next owner = false /\
    Context.linearBindings next = Context.linearBindings context.
Proof.
  intros owner context next Hend.
  unfold endLinearSharedLoan in Hend.
  destruct (Context.sharedLoans context owner) eqn:Hactive;
    try discriminate.
  inversion Hend; subst next; clear Hend.
  repeat split.
  - exact Hactive.
  - apply set_core_loan_has_exact_target.
  - reflexivity.
Qed.

Theorem started_linear_loan_blocks_owner_consumption :
  forall owner context next,
    startLinearSharedLoan owner context = Some next ->
    Context.consumeLinear owner next =
      Context.ConsumeError (Context.OwnerBorrowed owner).
Proof.
  intros owner context next Hstart.
  pose proof
    (start_linear_loan_requires_present_unloaned_owner
      owner context next Hstart) as [_ [_ [Hactive _]]].
  unfold Context.consumeLinear.
  now rewrite Hactive.
Qed.

Theorem end_after_start_restores_loan_membership :
  forall owner context ty,
    Context.sharedLoans context owner = false ->
    Context.linearBindings context owner = Some ty ->
    exists started ended,
      startLinearSharedLoan owner context = Some started /\
      endLinearSharedLoan owner started = Some ended /\
      (forall candidate,
        Context.sharedLoans ended candidate =
          Context.sharedLoans context candidate) /\
      Context.linearBindings ended = Context.linearBindings context.
Proof.
  intros owner context ty Hfree Hlinear.
  exists (setCoreLoan owner true context).
  exists (setCoreLoan owner false (setCoreLoan owner true context)).
  repeat split.
  - unfold startLinearSharedLoan.
    rewrite Hfree, Hlinear.
    reflexivity.
  - unfold endLinearSharedLoan.
    rewrite set_core_loan_has_exact_target.
    reflexivity.
  - intro candidate.
    unfold setCoreLoan; simpl.
    destruct (String.eqb candidate owner) eqn:Heq.
    + apply String.eqb_eq in Heq. subst candidate.
      exact Hfree.
    + reflexivity.
  - reflexivity.
Qed.

Section EncodedOwnerRelation.

  (* Both mappings are hypotheses. The Haskell $phil.local Text encoding,
     and the conversion of source owners to ResourceOwner nat, are not yet
     implemented/certified as this pair of Rocq functions. *)
  Variable nameOf : BindingSemantics.BinderKey -> Syntax.Name.
  Variable abstractOwnerOf :
    BindingSemantics.BinderKey -> ResourceJoin.ResourceOwner.
  Hypothesis nameOf_injective :
    forall first second, nameOf first = nameOf second -> first = second.
  Hypothesis abstractOwnerOf_injective :
    forall first second,
      abstractOwnerOf first = abstractOwnerOf second -> first = second.

  Definition ExactLoanRelation
    (context : Context.ResourceContext) (loans : ResourceScope.LoanSet)
    : Prop :=
    forall key,
      Context.sharedLoans context (nameOf key) =
        loans (abstractOwnerOf key).

  Lemma both_owner_encodings_agree_on_equality :
    forall first second,
      String.eqb (nameOf first) (nameOf second) =
      Nat.eqb (abstractOwnerOf first) (abstractOwnerOf second).
  Proof.
    intros first second.
    destruct (String.eqb (nameOf first) (nameOf second)) eqn:Hname;
    destruct (Nat.eqb (abstractOwnerOf first) (abstractOwnerOf second))
      eqn:Howner; try reflexivity.
    - apply String.eqb_eq in Hname.
      apply nameOf_injective in Hname.
      subst second.
      rewrite Nat.eqb_refl in Howner.
      discriminate.
    - apply Nat.eqb_eq in Howner.
      apply abstractOwnerOf_injective in Howner.
      subst second.
      rewrite String.eqb_refl in Hname.
      discriminate.
  Qed.

  Theorem exact_loan_relation_preserved_by_one_name_update :
    forall context loans target active,
      ExactLoanRelation context loans ->
      ExactLoanRelation
        (setCoreLoan (nameOf target) active context)
        (setAbstractLoan (abstractOwnerOf target) active loans).
  Proof.
    intros context loans target active Hrelated query.
    unfold setCoreLoan, setAbstractLoan; simpl.
    rewrite <- (both_owner_encodings_agree_on_equality query target).
    destruct (String.eqb (nameOf query) (nameOf target)).
    - reflexivity.
    - apply Hrelated.
  Qed.

  Theorem start_linear_loan_preserves_exact_owner_relation :
    forall context loans target ty,
      ExactLoanRelation context loans ->
      Context.sharedLoans context (nameOf target) = false ->
      Context.linearBindings context (nameOf target) = Some ty ->
      exists next,
        startLinearSharedLoan (nameOf target) context = Some next /\
        ExactLoanRelation
          next (setAbstractLoan (abstractOwnerOf target) true loans) /\
        Context.linearBindings next (nameOf target) = Some ty /\
        Context.sharedLoans next (nameOf target) = true.
  Proof.
    intros context loans target ty Hrelated Hfree Hlinear.
    exists (setCoreLoan (nameOf target) true context).
    repeat split.
    - unfold startLinearSharedLoan.
      now rewrite Hfree, Hlinear.
    - apply exact_loan_relation_preserved_by_one_name_update.
      exact Hrelated.
    - exact Hlinear.
    - apply set_core_loan_has_exact_target.
  Qed.

  Theorem end_linear_loan_preserves_exact_owner_relation :
    forall context loans target,
      ExactLoanRelation context loans ->
      Context.sharedLoans context (nameOf target) = true ->
      exists next,
        endLinearSharedLoan (nameOf target) context = Some next /\
        ExactLoanRelation
          next (setAbstractLoan (abstractOwnerOf target) false loans) /\
        Context.linearBindings next = Context.linearBindings context /\
        Context.sharedLoans next (nameOf target) = false.
  Proof.
    intros context loans target Hrelated Hactive.
    exists (setCoreLoan (nameOf target) false context).
    repeat split.
    - unfold endLinearSharedLoan.
      now rewrite Hactive.
    - apply exact_loan_relation_preserved_by_one_name_update.
      exact Hrelated.
    - reflexivity.
    - apply set_core_loan_has_exact_target.
  Qed.

  Theorem admitted_view_name_differs_from_exact_owner :
    forall declaration ownerOrdinal viewOrdinal bodyBinderCount,
      ownerOrdinal < viewOrdinal ->
      let ownerKey := BindingSemantics.semanticBinderKey
        declaration ownerOrdinal in
      let checkedBorrow := SurfaceBorrowViewScope.checkSurfaceBorrowView
        declaration viewOrdinal (Some ownerKey) bodyBinderCount in
      nameOf (SurfaceBorrowViewScope.surfaceBorrowViewBinder checkedBorrow) <>
        nameOf ownerKey.
  Proof.
    intros declaration ownerOrdinal viewOrdinal bodyBinderCount Hlt.
    simpl.
    intro Heq.
    apply nameOf_injective in Heq.
    unfold BindingSemantics.semanticBinderKey in Heq.
    inversion Heq.
    lia.
  Qed.

  Theorem admitted_borrow_resolves_the_same_exact_owner_key :
    forall declaration ownerOrdinal viewOrdinal bodyBinderCount,
      SurfaceBorrowViewScope.surfaceBorrowOwnerDecision
        (SurfaceBorrowViewScope.checkSurfaceBorrowView
          declaration viewOrdinal
          (Some (BindingSemantics.semanticBinderKey
            declaration ownerOrdinal)) bodyBinderCount) =
      SurfaceBorrowViewScope.SurfaceBorrowOwnerResolved
        (BindingSemantics.semanticBinderKey declaration ownerOrdinal).
  Proof.
    reflexivity.
  Qed.

End EncodedOwnerRelation.

(* The existing ResourceScope.v theorem applies ONLY to normalized ordinary
   joins and loop backedges, not directly to the borrow-expression exit above.
   A checked source-to-model simulation and the exact Haskell encodings remain
   separate, open obligations. No admitted or axiomatized theorems here. *)
