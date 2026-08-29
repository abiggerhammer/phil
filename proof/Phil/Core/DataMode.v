From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

From Phil.Core Require Import Syntax Context.

(*
  PHIL-DATA-MODE-001 — aggregate structural mode and construction.

  This file proves the data-specific layer over the already mechanized Core
  resource context. Records and sums use the strongest structural mode of
  their owned contents; normalized generic mode atoms instantiate through the
  same strongest-mode operation; explicit nominal declarations may only keep
  or strengthen the derived mode, and strict strengthening requires separately
  admitted semantic justification.

  Construction itself is represented as a source-position spine. Restricted
  occurrence identity may appear in at most one owning position. Concrete
  one-shot linear removal is imported from Context.v rather than reproved here.
*)

Definition modeRank (mode : Mode) : nat :=
  match mode with
  | Unrestricted => 0
  | Affine => 1
  | Linear => 2
  end.

Definition modeLe (left right : Mode) : Prop :=
  modeRank left <= modeRank right.

Definition modeLub (left right : Mode) : Mode :=
  match left, right with
  | Linear, _ => Linear
  | _, Linear => Linear
  | Affine, _ => Affine
  | _, Affine => Affine
  | Unrestricted, Unrestricted => Unrestricted
  end.

Fixpoint deriveRecordMode (modes : list Mode) : Mode :=
  match modes with
  | [] => Unrestricted
  | mode :: rest => modeLub mode (deriveRecordMode rest)
  end.

Fixpoint deriveSumMode (constructors : list (list Mode)) : Mode :=
  match constructors with
  | [] => Unrestricted
  | payloadModes :: rest =>
      modeLub (deriveRecordMode payloadModes) (deriveSumMode rest)
  end.

Lemma modeLe_refl :
  forall mode, modeLe mode mode.
Proof.
  intros mode.
  unfold modeLe.
  lia.
Qed.

Lemma modeLe_trans :
  forall first second third,
    modeLe first second ->
    modeLe second third ->
    modeLe first third.
Proof.
  intros first second third Hfirst Hsecond.
  unfold modeLe in *.
  lia.
Qed.

Lemma modeLub_left_upper :
  forall left right,
    modeLe left (modeLub left right).
Proof.
  intros left right.
  destruct left; destruct right; unfold modeLe, modeRank, modeLub; simpl; lia.
Qed.

Lemma modeLub_right_upper :
  forall left right,
    modeLe right (modeLub left right).
Proof.
  intros left right.
  destruct left; destruct right; unfold modeLe, modeRank, modeLub; simpl; lia.
Qed.

(* Every owned record field contributes monotonically to the aggregate mode. *)
Theorem record_mode_bounds_every_field :
  forall modes fieldMode,
    In fieldMode modes ->
    modeLe fieldMode (deriveRecordMode modes).
Proof.
  induction modes as [| head tail IH]; intros fieldMode Hin.
  - inversion Hin.
  - simpl in Hin.
    simpl.
    destruct Hin as [Heq | Hin].
    + subst fieldMode.
      apply modeLub_left_upper.
    + eapply modeLe_trans.
      * apply IH.
        exact Hin.
      * apply modeLub_right_upper.
Qed.

(* Every payload mode of every constructor contributes to the conservative sum mode. *)
Theorem sum_mode_bounds_every_payload :
  forall constructors payloadModes fieldMode,
    In payloadModes constructors ->
    In fieldMode payloadModes ->
    modeLe fieldMode (deriveSumMode constructors).
Proof.
  induction constructors as [| head rest IH]; intros payloadModes fieldMode Hpayload Hfield.
  - inversion Hpayload.
  - simpl in Hpayload.
    simpl.
    destruct Hpayload as [Heq | Hpayload].
    + subst payloadModes.
      eapply modeLe_trans.
      * apply record_mode_bounds_every_field.
        exact Hfield.
      * apply modeLub_left_upper.
    + eapply modeLe_trans.
      * eapply IH.
        -- exact Hpayload.
        -- exact Hfield.
      * apply modeLub_right_upper.
Qed.

(*
  Generic mode expressions are normalized to a strongest-mode list of fixed
  modes and generic parameters. This is semantically sufficient because LUB is
  associative/idempotent; concrete syntax nesting remains correspondence.
*)
Inductive ModeAtom : Type :=
| FixedMode (mode : Mode)
| ParameterMode (parameter : nat).

Definition ModeEnvironment : Type := nat -> option Mode.

Definition instantiateAtom
  (environment : ModeEnvironment)
  (atom : ModeAtom) : option Mode :=
  match atom with
  | FixedMode mode => Some mode
  | ParameterMode parameter => environment parameter
  end.

Fixpoint instantiateStrongest
  (environment : ModeEnvironment)
  (atoms : list ModeAtom) : option Mode :=
  match atoms with
  | [] => Some Unrestricted
  | atom :: rest =>
      match instantiateAtom environment atom,
            instantiateStrongest environment rest with
      | Some mode, Some tailMode => Some (modeLub mode tailMode)
      | _, _ => None
      end
  end.

Theorem generic_actual_is_not_weakened :
  forall environment atoms parameter actual aggregate,
    environment parameter = Some actual ->
    In (ParameterMode parameter) atoms ->
    instantiateStrongest environment atoms = Some aggregate ->
    modeLe actual aggregate.
Proof.
  intros environment atoms.
  induction atoms as [| atom rest IH]; intros parameter actual aggregate Henv Hin Hinst.
  - inversion Hin.
  - simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst atom.
      simpl in Hinst.
      rewrite Henv in Hinst.
      destruct (instantiateStrongest environment rest) as [tailMode |] eqn:Htail.
      * inversion Hinst; subst aggregate.
        apply modeLub_left_upper.
      * discriminate.
    + simpl in Hinst.
      destruct (instantiateAtom environment atom) as [headMode |] eqn:Hhead.
      * destruct (instantiateStrongest environment rest) as [tailMode |] eqn:Htail.
        -- inversion Hinst; subst aggregate.
           eapply modeLe_trans.
           ++ eapply (IH parameter actual tailMode).
              ** exact Henv.
              ** exact Hin.
              ** reflexivity.
           ++ apply modeLub_right_upper.
        -- discriminate.
      * discriminate.
Qed.

Theorem unbound_generic_actual_fails_closed :
  forall environment atoms parameter,
    environment parameter = None ->
    In (ParameterMode parameter) atoms ->
    instantiateStrongest environment atoms = None.
Proof.
  intros environment atoms.
  induction atoms as [| atom rest IH]; intros parameter Henv Hin.
  - inversion Hin.
  - simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst atom.
      simpl.
      rewrite Henv.
      reflexivity.
    + simpl.
      destruct (instantiateAtom environment atom) as [headMode |] eqn:Hhead.
      * rewrite (IH parameter Henv Hin).
        reflexivity.
      * reflexivity.
Qed.

Parameter NominalJustification : Type.
Parameter justificationAdmitted : NominalJustification -> Prop.

Inductive NominalModeAccepted :
  Mode -> option Mode -> option NominalJustification -> Mode -> Prop :=
| NominalDerived :
    forall derived justification,
      NominalModeAccepted derived None justification derived
| NominalExplicitEqual :
    forall derived justification,
      NominalModeAccepted derived (Some derived) justification derived
| NominalStrengthened :
    forall derived declared justification,
      modeLe derived declared ->
      derived <> declared ->
      justificationAdmitted justification ->
      NominalModeAccepted
        derived (Some declared) (Some justification) declared.

Theorem accepted_nominal_mode_never_weakens :
  forall derived declared justification accepted,
    NominalModeAccepted derived declared justification accepted ->
    modeLe derived accepted.
Proof.
  intros derived declared justification accepted Haccepted.
  inversion Haccepted; subst.
  - apply modeLe_refl.
  - apply modeLe_refl.
  - assumption.
Qed.

Theorem strict_nominal_strengthening_requires_admitted_justification :
  forall derived declared justification accepted,
    NominalModeAccepted derived (Some declared) justification accepted ->
    derived <> accepted ->
    exists witness,
      justification = Some witness /\
      justificationAdmitted witness.
Proof.
  intros derived declared justification accepted Haccepted Hstrict.
  inversion Haccepted; subst.
  - contradiction.
  - eexists.
    split; eauto.
Qed.

Record AggregateSource : Type := mkAggregateSource {
  sourceOccurrence : nat;
  sourceMode : Mode
}.

Definition RestrictedSource (source : AggregateSource) : Prop :=
  sourceMode source = Affine \/ sourceMode source = Linear.

Inductive AtPosition : nat -> AggregateSource -> list AggregateSource -> Prop :=
| AtPositionHere :
    forall source rest,
      AtPosition 0 source (source :: rest)
| AtPositionThere :
    forall index source head rest,
      AtPosition index source rest ->
      AtPosition (S index) source (head :: rest).

Definition AggregateFormationAccepted
  (sources : list AggregateSource) : Prop :=
  forall firstIndex secondIndex firstSource secondSource,
    AtPosition firstIndex firstSource sources ->
    AtPosition secondIndex secondSource sources ->
    RestrictedSource firstSource ->
    RestrictedSource secondSource ->
    sourceOccurrence firstSource = sourceOccurrence secondSource ->
    firstIndex = secondIndex.

(* An admitted construction has exactly one owning position for a restricted occurrence. *)
Theorem accepted_formation_transfers_restricted_occurrence_once :
  forall sources index source,
    AggregateFormationAccepted sources ->
    AtPosition index source sources ->
    RestrictedSource source ->
    forall otherIndex otherSource,
      AtPosition otherIndex otherSource sources ->
      RestrictedSource otherSource ->
      sourceOccurrence otherSource = sourceOccurrence source ->
      otherIndex = index.
Proof.
  intros sources index source Haccepted Hposition Hrestricted
    otherIndex otherSource Hother HotherRestricted Hsame.
  eapply Haccepted.
  - exact Hother.
  - exact Hposition.
  - exact HotherRestricted.
  - exact Hrestricted.
  - exact Hsame.
Qed.

(* Supplying one affine/linear occurrence to two owning positions is impossible. *)
Theorem duplicate_restricted_occurrence_rejects :
  forall source rest,
    RestrictedSource source ->
    ~ AggregateFormationAccepted (source :: source :: rest).
Proof.
  intros source rest Hrestricted Haccepted.
  assert (Hfirst : AtPosition 0 source (source :: source :: rest)).
  { constructor. }
  assert (Hsecond : AtPosition 1 source (source :: source :: rest)).
  { constructor. constructor. }
  pose proof
    (Haccepted 0 1 source source
      Hfirst Hsecond Hrestricted Hrestricted eq_refl) as Heq.
  discriminate.
Qed.

(* Imported Core consumption makes a successfully transferred linear source one-shot. *)
Theorem core_linear_source_not_reusable_after_transfer :
  forall name context next ty,
    consumeLinear name context = Consumed ty next ->
    forall laterTy later,
      consumeLinear name next <> Consumed laterTy later.
Proof.
  intros name context next ty Hfirst laterTy later Hsecond.
  pose proof
    (consumeLinear_success_consumes_owner name context next ty Hfirst)
    as Hgone.
  pose proof
    (consumeLinear_success_exact name next later laterTy Hsecond)
    as Hlater.
  destruct Hlater as [Hpresent _].
  rewrite Hgone in Hpresent.
  discriminate.
Qed.
