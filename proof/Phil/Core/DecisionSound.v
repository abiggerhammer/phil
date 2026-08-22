From Stdlib Require Import QArith.QArith Lists.List micromega.Lqa.
Import ListNotations.

Open Scope Q_scope.

(*
  Mathematical kernel beneath Phil.Core.Decision.checkLinearCertificate.

  The Haskell checker reduces normalized arithmetic propositions and bases to
  affine rational forms. At that point a basis denotes either an equality
  (value = 0) or an inequality (value >= 0). The certificate supplies rational
  weights and slack. This file proves the ordered-field fact that makes the
  checker trustworthy: arbitrary linear combinations of equalities remain zero,
  while inequalities may contribute only with nonnegative weights and
  nonnegative slack.
*)

Inductive GoalKind : Type :=
| EqualityGoal : GoalKind
| InequalityGoal : GoalKind.

Inductive BasisKind : Type :=
| EqualityBasis : BasisKind
| InequalityBasis : BasisKind.

Record Basis : Type := mkBasis
  { basisKind : BasisKind
  ; basisValue : Q
  }.

Definition BasisValid (basis : Basis) : Prop :=
  match basisKind basis with
  | EqualityBasis => basisValue basis == 0
  | InequalityBasis => 0 <= basisValue basis
  end.

Definition WeightedTerm := (Basis * Q)%type.

Definition TermValidFor (goal : GoalKind) (term : WeightedTerm) : Prop :=
  let '(basis, coefficient) := term in
  BasisValid basis /\
  match goal, basisKind basis with
  | EqualityGoal, EqualityBasis => True
  | EqualityGoal, InequalityBasis => False
  | InequalityGoal, EqualityBasis => True
  | InequalityGoal, InequalityBasis => 0 <= coefficient
  end.

Definition weightedTermValue (term : WeightedTerm) : Q :=
  let '(basis, coefficient) := term in
  coefficient * basisValue basis.

Fixpoint weightedSum (terms : list WeightedTerm) : Q :=
  match terms with
  | [] => 0
  | term :: rest => weightedTermValue term + weightedSum rest
  end.

Definition GoalSatisfied (goal : GoalKind) (target : Q) : Prop :=
  match goal with
  | EqualityGoal => target == 0
  | InequalityGoal => 0 <= target
  end.

Definition CertificateAccepted
  (goal : GoalKind)
  (terms : list WeightedTerm)
  (slack target : Q) : Prop :=
  Forall (TermValidFor goal) terms /\
  (match goal with
   | EqualityGoal => slack == 0
   | InequalityGoal => 0 <= slack
   end) /\
  target == weightedSum terms + slack.

Lemma equality_term_is_zero :
  forall term,
    TermValidFor EqualityGoal term ->
    weightedTermValue term == 0.
Proof.
  intros [basis coefficient] Hvalid.
  destruct basis as [kind value].
  destruct kind; simpl in *.
  - destruct Hvalid as [Hvalue _].
    setoid_replace value with 0 by exact Hvalue.
    ring.
  - destruct Hvalid as [_ Hfalse]. contradiction.
Qed.

Lemma inequality_term_is_nonnegative :
  forall term,
    TermValidFor InequalityGoal term ->
    0 <= weightedTermValue term.
Proof.
  intros [basis coefficient] Hvalid.
  destruct basis as [kind value].
  destruct kind; simpl in *.
  - destruct Hvalid as [Hvalue _].
    setoid_replace value with 0 by exact Hvalue.
    apply Qle_refl.
  - destruct Hvalid as [Hvalue Hcoefficient].
    apply Qmult_le_0_compat; assumption.
Qed.

Lemma equality_weighted_sum_is_zero :
  forall terms,
    Forall (TermValidFor EqualityGoal) terms ->
    weightedSum terms == 0.
Proof.
  induction terms as [| term rest IH]; intros Hvalid.
  - simpl. ring.
  - inversion Hvalid as [| head tail Hterm Hrest]; subst.
    simpl.
    pose proof (equality_term_is_zero term Hterm) as Hzero.
    pose proof (IH Hrest) as HrestZero.
    setoid_replace (weightedTermValue term) with 0 by exact Hzero.
    setoid_replace (weightedSum rest) with 0 by exact HrestZero.
    ring.
Qed.

Lemma inequality_weighted_sum_is_nonnegative :
  forall terms,
    Forall (TermValidFor InequalityGoal) terms ->
    0 <= weightedSum terms.
Proof.
  induction terms as [| term rest IH]; intros Hvalid.
  - simpl. apply Qle_refl.
  - inversion Hvalid as [| head tail Hterm Hrest]; subst.
    simpl.
    pose proof (inequality_term_is_nonnegative term Hterm) as HtermNonnegative.
    pose proof (IH Hrest) as HrestNonnegative.
    lra.
Qed.

(* PHIL-DECISION-LINEAR-001 *)
Theorem accepted_linear_certificate_is_sound :
  forall goal terms slack target,
    CertificateAccepted goal terms slack target ->
    GoalSatisfied goal target.
Proof.
  intros goal terms slack target Haccepted.
  destruct Haccepted as [Hterms [Hslack Htarget]].
  destruct goal.
  - simpl in *.
    pose proof (equality_weighted_sum_is_zero terms Hterms) as Hsum.
    eapply Qeq_trans.
    + exact Htarget.
    + setoid_replace (weightedSum terms) with 0 by exact Hsum.
      setoid_replace slack with 0 by exact Hslack.
      ring.
  - simpl in *.
    pose proof (inequality_weighted_sum_is_nonnegative terms Hterms) as Hsum.
    setoid_replace target with (weightedSum terms + slack).
    + lra.
    + exact Htarget.
Qed.

Parameter Prerequisite : Type.

Definition PrerequisitesSatisfied
  (required available : list Prerequisite) : Prop :=
  forall prerequisite,
    In prerequisite required -> In prerequisite available.

Inductive CheckedLinearCertificate
  (goal : GoalKind)
  (terms : list WeightedTerm)
  (slack target : Q)
  (required available : list Prerequisite) : Prop :=
| CheckedLinearCertificate_intro :
    PrerequisitesSatisfied required available ->
    CertificateAccepted goal terms slack target ->
    CheckedLinearCertificate goal terms slack target required available.

Theorem checked_certificate_requires_all_partial_prerequisites :
  forall goal terms slack target required available,
    CheckedLinearCertificate goal terms slack target required available ->
    PrerequisitesSatisfied required available.
Proof.
  intros goal terms slack target required available Hchecked.
  inversion Hchecked; assumption.
Qed.

Corollary checked_linear_certificate_semantically_sound :
  forall goal terms slack target required available,
    CheckedLinearCertificate goal terms slack target required available ->
    GoalSatisfied goal target.
Proof.
  intros goal terms slack target required available Hchecked.
  inversion Hchecked as [Hprerequisites Hcertificate].
  now apply accepted_linear_certificate_is_sound with
    (terms := terms) (slack := slack).
Qed.
