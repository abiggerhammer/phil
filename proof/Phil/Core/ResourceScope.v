From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List.

Import ListNotations.

From Phil.Core Require Import ResourceJoin.

(*
  PHIL-RES-SCOPE-001 — branch-local scope, affine asymmetry, lexical-loan
  exclusion, and terminal-arm exclusion.

  PHIL-RES-JOIN-001 already certifies exact conservation of continuing linear
  owners and exact subject/slot correspondence.  This theorem family adds the
  branch/scope discipline exercised by RES-005--008 without rebuilding that
  join theorem:

  - a live branch-local linear owner cannot disappear at reconvergence;
  - affine asymmetry is represented by an explicit post-state carrier rather
    than hidden maybe-possession;
  - lexical scoped loans are closed before ordinary joins and loop backedges;
  - terminal arms are not continuing predecessors and contribute no projection.
*)

Definition OwnerAbsentFromProjection
  (projection : ResourceProjection)
  (owner : ResourceOwner) : Prop :=
  forall slot, projectionBindings projection slot <> Some owner.

Theorem live_branch_local_linear_owner_cannot_disappear :
  forall succession projection owner,
    ResourceProjectionSuccess succession projection ->
    projectionIncomingLinear projection owner = true ->
    OwnerAbsentFromProjection projection owner ->
    False.
Proof.
  intros succession projection owner Hsuccess Hlive Habsent.
  eapply resource_projection_rejects_linear_omission.
  - exact Hsuccess.
  - exact Hlive.
  - exact Habsent.
Qed.

Theorem disposed_branch_local_owner_is_outside_live_linear_coverage :
  forall projection owner,
    projectionIncomingLinear projection owner = false ->
    projectionIncomingLinear projection owner <> true.
Proof.
  intros projection owner Hdisposed Hlive.
  rewrite Hdisposed in Hlive.
  discriminate.
Qed.

(* Explicit affine state.  [AffineAbsent] is an ordinary explicit value in the
   post-state carrier; absence of the slot itself is not interpreted as hidden
   maybe-possession. *)

Definition AffineSlotDeclared : Type := ResourceSlot -> bool.

Inductive AffineCarrier : Type :=
| AffineAbsent : AffineCarrier
| AffinePresent (owner : ResourceOwner) : AffineCarrier.

Definition AffinePostState : Type :=
  ResourceSlot -> option AffineCarrier.

Definition ExplicitAffineProjection
  (declared : AffineSlotDeclared)
  (state : AffinePostState) : Prop :=
  forall slot,
    declared slot = true ->
    exists carrier, state slot = Some carrier.

Theorem hidden_affine_maybe_possession_rejects :
  forall declared state slot,
    declared slot = true ->
    state slot = None ->
    ~ ExplicitAffineProjection declared state.
Proof.
  intros declared state slot Hdeclared Hnone Hexplicit.
  destruct (Hexplicit slot Hdeclared) as [carrier Hcarrier].
  rewrite Hnone in Hcarrier.
  discriminate.
Qed.

Definition singletonAffineDeclaration
  (slot : ResourceSlot) : AffineSlotDeclared :=
  fun query => Nat.eqb query slot.

Definition singletonAffineState
  (slot : ResourceSlot)
  (carrier : AffineCarrier) : AffinePostState :=
  fun query =>
    if Nat.eqb query slot then Some carrier else None.

Theorem explicit_affine_carrier_satisfies_singleton_projection :
  forall slot carrier,
    ExplicitAffineProjection
      (singletonAffineDeclaration slot)
      (singletonAffineState slot carrier).
Proof.
  intros slot carrier query Hdeclared.
  unfold singletonAffineDeclaration in Hdeclared.
  apply Nat.eqb_eq in Hdeclared.
  subst query.
  exists carrier.
  unfold singletonAffineState.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Corollary explicit_affine_absence_is_representable :
  forall slot,
    ExplicitAffineProjection
      (singletonAffineDeclaration slot)
      (singletonAffineState slot AffineAbsent).
Proof.
  intros slot.
  apply explicit_affine_carrier_satisfies_singleton_projection.
Qed.

Corollary explicit_affine_possession_is_representable :
  forall slot owner,
    ExplicitAffineProjection
      (singletonAffineDeclaration slot)
      (singletonAffineState slot (AffinePresent owner)).
Proof.
  intros slot owner.
  apply explicit_affine_carrier_satisfies_singleton_projection.
Qed.

(* Lexical loans are deliberately not lifetime-polymorphic in Phase 1.  A
   continuing control boundary is safe only when every lexical loan is closed
   before the edge. *)

Inductive ContinuingBoundaryKind : Type :=
| OrdinaryJoinBoundary : ContinuingBoundaryKind
| LoopBackedgeBoundary : ContinuingBoundaryKind.

Definition LoanSet : Type := ResourceOwner -> bool.

Definition LexicalLoansClosedAtBoundary
  (loans : LoanSet) : Prop :=
  forall loan, loans loan = false.

Record ScopedBoundaryProjection : Type := {
  scopedResourceProjection : ResourceProjection;
  scopedLexicalLoans : LoanSet
}.

Definition ScopedBoundaryProjectionSuccess
  (succession : SuccessionEvidence)
  (_kind : ContinuingBoundaryKind)
  (projection : ScopedBoundaryProjection) : Prop :=
  ResourceProjectionSuccess succession (scopedResourceProjection projection) /\
  LexicalLoansClosedAtBoundary (scopedLexicalLoans projection).

Theorem successful_continuing_boundary_has_no_scoped_loan :
  forall succession kind projection loan,
    ScopedBoundaryProjectionSuccess succession kind projection ->
    scopedLexicalLoans projection loan = false.
Proof.
  intros succession kind projection loan Hsuccess.
  destruct Hsuccess as [_ Hclosed].
  apply Hclosed.
Qed.

Theorem scoped_loan_cannot_cross_continuing_boundary :
  forall succession kind projection loan,
    ScopedBoundaryProjectionSuccess succession kind projection ->
    scopedLexicalLoans projection loan = true ->
    False.
Proof.
  intros succession kind projection loan Hsuccess Hlive.
  pose proof
    (successful_continuing_boundary_has_no_scoped_loan
      succession kind projection loan Hsuccess) as Hclosed.
  rewrite Hclosed in Hlive.
  discriminate.
Qed.

Corollary scoped_loan_cannot_cross_ordinary_join :
  forall succession projection loan,
    ScopedBoundaryProjectionSuccess
      succession OrdinaryJoinBoundary projection ->
    scopedLexicalLoans projection loan = true ->
    False.
Proof.
  intros succession projection loan Hsuccess Hlive.
  eapply scoped_loan_cannot_cross_continuing_boundary.
  - exact Hsuccess.
  - exact Hlive.
Qed.

Corollary scoped_loan_cannot_cross_loop_backedge :
  forall succession projection loan,
    ScopedBoundaryProjectionSuccess
      succession LoopBackedgeBoundary projection ->
    scopedLexicalLoans projection loan = true ->
    False.
Proof.
  intros succession projection loan Hsuccess Hlive.
  eapply scoped_loan_cannot_cross_continuing_boundary.
  - exact Hsuccess.
  - exact Hlive.
Qed.

(* Terminal arms do not denote an empty continuing predecessor.  They are
   outside the continuing-projection relation altogether. *)

Inductive BranchDisposition : Type :=
| ContinuingArm (projection : ResourceProjection) : BranchDisposition
| TerminalArm : BranchDisposition.

Definition ContributesContinuingProjection
  (disposition : BranchDisposition)
  (projection : ResourceProjection) : Prop :=
  disposition = ContinuingArm projection.

Theorem terminal_arm_contributes_no_continuing_projection :
  forall projection,
    ~ ContributesContinuingProjection TerminalArm projection.
Proof.
  intros projection Hcontributes.
  unfold ContributesContinuingProjection in Hcontributes.
  discriminate.
Qed.

Theorem continuing_arm_contribution_is_exact :
  forall actual reported,
    ContributesContinuingProjection (ContinuingArm actual) reported ->
    actual = reported.
Proof.
  intros actual reported Hcontributes.
  unfold ContributesContinuingProjection in Hcontributes.
  inversion Hcontributes.
  reflexivity.
Qed.

Theorem terminal_arm_cannot_be_forced_into_join_projection :
  forall projection,
    ContributesContinuingProjection TerminalArm projection ->
    False.
Proof.
  intros projection Hcontributes.
  eapply terminal_arm_contributes_no_continuing_projection.
  exact Hcontributes.
Qed.
