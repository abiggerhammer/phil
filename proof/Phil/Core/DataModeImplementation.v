From Stdlib Require Import Bool.Bool Lists.List Lia.
Import ListNotations.

From Phil.Core Require Import DataMode.

(*
  PHIL-DATA-MODE-001 — executable implementation-refinement staging.

  The Certified DataMode model already owns record/sum strongest-mode
  derivation, generic mode propagation, nominal no-weakening/justification,
  and restricted-occurrence uniqueness.  This file exposes only bounded
  executable decisions over those exact facts.  Concrete Haskell names,
  nested ModeExpr normalization, Context operations, source ordering, and
  justification provenance remain explicit correspondence boundaries for the
  later production-binding tranche.
*)

Definition modeEqb (left right : Mode) : bool :=
  match left, right with
  | Unrestricted, Unrestricted => true
  | Affine, Affine => true
  | Linear, Linear => true
  | _, _ => false
  end.

Theorem modeEqb_true_iff :
  forall left right,
    modeEqb left right = true <-> left = right.
Proof.
  intros left right.
  destruct left; destruct right; cbn; split; intro H; congruence.
Qed.

Theorem modeEqb_false_iff :
  forall left right,
    modeEqb left right = false <-> left <> right.
Proof.
  intros left right.
  destruct left; destruct right; cbn; split; intro H; congruence.
Qed.

Definition modeLeb (left right : Mode) : bool :=
  match left, right with
  | Unrestricted, _ => true
  | Affine, Affine => true
  | Affine, Linear => true
  | Linear, Linear => true
  | _, _ => false
  end.

Theorem modeLeb_sound :
  forall left right,
    modeLeb left right = true ->
    modeLe left right.
Proof.
  intros left right Hle.
  destruct left; destruct right; cbn in Hle; try discriminate Hle;
    unfold modeLe, modeRank; cbn; lia.
Qed.

Theorem modeLeb_complete :
  forall left right,
    modeLe left right ->
    modeLeb left right = true.
Proof.
  intros left right Hle.
  destruct left; destruct right; cbn;
    unfold modeLe, modeRank in Hle; cbn in Hle; try reflexivity; lia.
Qed.

Inductive AggregateModeDecision : Type :=
| AggregateModeAcceptedDecision
| AggregateModeMismatchDecision.

Definition decideRecordModeByCandidate
  (fieldModes : list Mode)
  (candidate : Mode) : AggregateModeDecision :=
  if modeEqb (deriveRecordMode fieldModes) candidate
  then AggregateModeAcceptedDecision
  else AggregateModeMismatchDecision.

Definition decideSumModeByCandidate
  (constructorPayloadModes : list (list Mode))
  (candidate : Mode) : AggregateModeDecision :=
  if modeEqb (deriveSumMode constructorPayloadModes) candidate
  then AggregateModeAcceptedDecision
  else AggregateModeMismatchDecision.

Theorem record_mode_decision_accept_iff_certified :
  forall fieldModes candidate,
    decideRecordModeByCandidate fieldModes candidate =
      AggregateModeAcceptedDecision <->
    deriveRecordMode fieldModes = candidate.
Proof.
  intros fieldModes candidate.
  unfold decideRecordModeByCandidate.
  destruct (modeEqb (deriveRecordMode fieldModes) candidate) eqn:Heq.
  - split; intro H.
    + exact ((proj1
        (modeEqb_true_iff (deriveRecordMode fieldModes) candidate)) Heq).
    + reflexivity.
  - split; intro H.
    + discriminate.
    + pose proof
        ((proj2 (modeEqb_true_iff (deriveRecordMode fieldModes) candidate)) H)
        as Htrue.
      rewrite Htrue in Heq.
      discriminate.
Qed.

Theorem sum_mode_decision_accept_iff_certified :
  forall constructorPayloadModes candidate,
    decideSumModeByCandidate constructorPayloadModes candidate =
      AggregateModeAcceptedDecision <->
    deriveSumMode constructorPayloadModes = candidate.
Proof.
  intros constructorPayloadModes candidate.
  unfold decideSumModeByCandidate.
  destruct (modeEqb (deriveSumMode constructorPayloadModes) candidate) eqn:Heq.
  - split; intro H.
    + exact ((proj1
        (modeEqb_true_iff (deriveSumMode constructorPayloadModes) candidate)) Heq).
    + reflexivity.
  - split; intro H.
    + discriminate.
    + pose proof
        ((proj2 (modeEqb_true_iff (deriveSumMode constructorPayloadModes) candidate)) H)
        as Htrue.
      rewrite Htrue in Heq.
      discriminate.
Qed.

(*
  Production ModeExpr syntax may be nested and parameter names are concrete
  Text/String values.  The certified model normalizes that syntax to a list of
  atoms.  Once each atom is resolved to Some mode or None, this fold is exactly
  instantiateStrongest; source flattening/name resolution remain native facts.
*)
Fixpoint resolvedStrongestMode
  (resolvedModes : list (option Mode)) : option Mode :=
  match resolvedModes with
  | [] => Some Unrestricted
  | None :: _ => None
  | Some mode :: rest =>
      match resolvedStrongestMode rest with
      | Some tailMode => Some (modeLub mode tailMode)
      | None => None
      end
  end.

Theorem resolved_strongest_mode_is_certified :
  forall environment atoms,
    resolvedStrongestMode (map (instantiateAtom environment) atoms) =
    instantiateStrongest environment atoms.
Proof.
  intros environment atoms.
  induction atoms as [| atom rest IH].
  - reflexivity.
  - cbn.
    rewrite IH.
    destruct (instantiateAtom environment atom) as [headMode |];
      destruct (instantiateStrongest environment rest) as [tailMode |];
      reflexivity.
Qed.

Inductive NominalModeDecision : Type :=
| NominalModeAcceptedDecision (accepted : Mode)
| NominalModeWeakeningDecision
| NominalModeJustificationDecision.

Definition decideNominalModeByFact
  (derived : Mode)
  (declared : option Mode)
  (strictJustificationAccepted : bool) : NominalModeDecision :=
  match declared with
  | None => NominalModeAcceptedDecision derived
  | Some declaredMode =>
      if modeEqb derived declaredMode then
        NominalModeAcceptedDecision declaredMode
      else if modeLeb derived declaredMode then
        if strictJustificationAccepted then
          NominalModeAcceptedDecision declaredMode
        else
          NominalModeJustificationDecision
      else
        NominalModeWeakeningDecision
  end.

Theorem nominal_mode_decision_accepted_never_weakens :
  forall derived declared strictJustificationAccepted accepted,
    decideNominalModeByFact derived declared strictJustificationAccepted =
      NominalModeAcceptedDecision accepted ->
    modeLe derived accepted.
Proof.
  intros derived declared strictJustificationAccepted accepted Hdecision.
  destruct declared as [declaredMode |].
  - cbn in Hdecision.
    destruct (modeEqb derived declaredMode) eqn:Heq.
    + inversion Hdecision; subst accepted.
      pose proof ((proj1 (modeEqb_true_iff derived declaredMode)) Heq) as Hequal.
      subst declaredMode.
      apply modeLe_refl.
    + destruct (modeLeb derived declaredMode) eqn:Hle.
      * destruct strictJustificationAccepted.
        -- inversion Hdecision; subst accepted.
           apply modeLeb_sound.
           exact Hle.
        -- discriminate.
      * discriminate.
  - cbn in Hdecision.
    inversion Hdecision; subst accepted.
    apply modeLe_refl.
Qed.

Theorem nominal_mode_strict_acceptance_requires_justification_fact :
  forall derived declared strictJustificationAccepted accepted,
    decideNominalModeByFact derived declared strictJustificationAccepted =
      NominalModeAcceptedDecision accepted ->
    derived <> accepted ->
    strictJustificationAccepted = true.
Proof.
  intros derived declared strictJustificationAccepted accepted Hdecision Hstrict.
  destruct declared as [declaredMode |].
  - cbn in Hdecision.
    destruct (modeEqb derived declaredMode) eqn:Heq.
    + inversion Hdecision; subst accepted.
      pose proof ((proj1 (modeEqb_true_iff derived declaredMode)) Heq) as Hequal.
      subst declaredMode.
      exfalso.
      apply Hstrict.
      reflexivity.
    + destruct (modeLeb derived declaredMode) eqn:Hle.
      * destruct strictJustificationAccepted.
        -- reflexivity.
        -- discriminate.
      * discriminate.
  - cbn in Hdecision.
    inversion Hdecision; subst accepted.
    exfalso.
    apply Hstrict.
    reflexivity.
Qed.

Theorem strict_nominal_mode_decision_is_exact_fact :
  forall derived declared strictJustificationAccepted,
    modeLe derived declared ->
    derived <> declared ->
    (decideNominalModeByFact
       derived (Some declared) strictJustificationAccepted =
       NominalModeAcceptedDecision declared <->
     strictJustificationAccepted = true).
Proof.
  intros derived declared strictJustificationAccepted Hle Hneq.
  pose proof ((proj2 (modeEqb_false_iff derived declared)) Hneq) as Heq.
  pose proof (modeLeb_complete derived declared Hle) as Hleb.
  cbn.
  rewrite Heq, Hleb.
  destruct strictJustificationAccepted.
  - cbn. split; intro H; reflexivity.
  - cbn. split; intro H; discriminate.
Qed.

Theorem justified_strict_nominal_mode_is_certified :
  forall derived declared witness,
    modeLe derived declared ->
    derived <> declared ->
    justificationAdmitted witness ->
    decideNominalModeByFact derived (Some declared) true =
      NominalModeAcceptedDecision declared /\
    NominalModeAccepted derived (Some declared) (Some witness) declared.
Proof.
  intros derived declared witness Hle Hneq Hadmitted.
  split.
  - apply (proj2
      (strict_nominal_mode_decision_is_exact_fact
        derived declared true Hle Hneq)).
    reflexivity.
  - apply NominalStrengthened.
    + exact Hle.
    + exact Hneq.
    + exact Hadmitted.
Qed.

Inductive AggregateFormationDecision : Type :=
| AggregateFormationAcceptedDecision
| AggregateFormationDuplicateRestrictedDecision.

Definition decideAggregateFormationByFact
  (restrictedOccurrencesUnique : bool) : AggregateFormationDecision :=
  if restrictedOccurrencesUnique
  then AggregateFormationAcceptedDecision
  else AggregateFormationDuplicateRestrictedDecision.

Theorem aggregate_formation_decision_corresponds_certified :
  forall sources restrictedOccurrencesUnique,
    (restrictedOccurrencesUnique = true <->
      AggregateFormationAccepted sources) ->
    (decideAggregateFormationByFact restrictedOccurrencesUnique =
       AggregateFormationAcceptedDecision <->
     AggregateFormationAccepted sources).
Proof.
  intros sources restrictedOccurrencesUnique Hreflect.
  destruct restrictedOccurrencesUnique.
  - cbn.
    split; intro H.
    + apply (proj1 Hreflect).
      reflexivity.
    + reflexivity.
  - cbn.
    split; intro H.
    + discriminate.
    + pose proof ((proj2 Hreflect) H) as Htrue.
      discriminate.
Qed.
