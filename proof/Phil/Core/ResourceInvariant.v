From Stdlib Require Import Lists.List Bool.Bool.
Import ListNotations.

From Phil.Core Require Import ResourceJoin ResourceLoop ResourceObligation.

(*
  PHIL-RES-INVARIANT-001 — explicit join/loop invariants must be established
  independently by every relevant predecessor.

  PHIL-RES-JOIN-001 and PHIL-RES-LOOP-001 already own structural resource/state
  compatibility.  This theorem deliberately layers logical authority on top of
  that structure rather than treating a compatible state projection as proof of
  an arbitrary proposition.

  The concrete RES-013 checker first validates the structural state boundary,
  checks exact state-slot witnesses, instantiates the declared invariant for one
  predecessor, and then establishes that exact instantiated proposition using
  only that predecessor's CheckState.  The normalized model below preserves
  those separations.
*)

Parameter InvariantProposition : Type.
Parameter StateWitness : Type.

Inductive InvariantPredecessorKind : Type :=
| JoinContinuingPredecessor
| LoopInitialPredecessor
| LoopBackedgePredecessor.

Record InvariantPredecessor : Type := {
  invariantPredecessorKind : InvariantPredecessorKind;
  invariantPredecessorProjection : ResourceProjection;
  invariantPredecessorWitness : ResourceSlot -> option StateWitness
}.

(* One declared post/header state telescope. *)
Parameter DeclaredInvariantSlot : ResourceSlot -> bool.

(* Exact predecessor-specific instantiation and proof authority. *)
Parameter instantiateInvariant : InvariantPredecessor -> InvariantProposition.
Parameter invariantEstablished :
  InvariantPredecessor -> InvariantProposition -> Prop.

Definition ExactInvariantWitnessDomain
  (predecessor : InvariantPredecessor) : Prop :=
  forall slot,
    DeclaredInvariantSlot slot = true <->
    exists witness,
      invariantPredecessorWitness predecessor slot = Some witness.

Definition ExactInvariantEstablished
  (predecessor : InvariantPredecessor) : Prop :=
  invariantEstablished predecessor (instantiateInvariant predecessor).

Record InvariantBoundarySuccess
  (succession : SuccessionEvidence)
  (predecessors : list InvariantPredecessor) : Prop := {
  invariantBoundaryPredecessorsDistinct : NoDup predecessors;
  invariantBoundaryStructural :
    forall predecessor,
      In predecessor predecessors ->
      ResourceProjectionSuccess
        succession
        (invariantPredecessorProjection predecessor);
  invariantBoundaryWitnessesExact :
    forall predecessor,
      In predecessor predecessors ->
      ExactInvariantWitnessDomain predecessor;
  invariantBoundaryEstablished :
    forall predecessor,
      In predecessor predecessors ->
      ExactInvariantEstablished predecessor
}.

Theorem invariant_boundary_requires_structural_projection :
  forall succession predecessors predecessor,
    InvariantBoundarySuccess succession predecessors ->
    In predecessor predecessors ->
    ResourceProjectionSuccess
      succession
      (invariantPredecessorProjection predecessor).
Proof.
  intros succession predecessors predecessor Hsuccess Hin.
  destruct Hsuccess as [Hdistinct Hstructural Hwitnesses Hestablished].
  eapply Hstructural.
  exact Hin.
Qed.

Theorem invariant_boundary_requires_exact_witness_domain :
  forall succession predecessors predecessor,
    InvariantBoundarySuccess succession predecessors ->
    In predecessor predecessors ->
    ExactInvariantWitnessDomain predecessor.
Proof.
  intros succession predecessors predecessor Hsuccess Hin.
  destruct Hsuccess as [Hdistinct Hstructural Hwitnesses Hestablished].
  eapply Hwitnesses.
  exact Hin.
Qed.

Theorem every_declared_invariant_slot_has_exact_predecessor_witness :
  forall succession predecessors predecessor slot,
    InvariantBoundarySuccess succession predecessors ->
    In predecessor predecessors ->
    DeclaredInvariantSlot slot = true ->
    exists witness,
      invariantPredecessorWitness predecessor slot = Some witness.
Proof.
  intros succession predecessors predecessor slot Hsuccess Hin Hdeclared.
  pose proof
    (invariant_boundary_requires_exact_witness_domain
      succession predecessors predecessor Hsuccess Hin)
    as Hdomain.
  apply (proj1 (Hdomain slot)).
  exact Hdeclared.
Qed.

Theorem undeclared_invariant_slot_cannot_be_synthesized :
  forall succession predecessors predecessor slot witness,
    InvariantBoundarySuccess succession predecessors ->
    In predecessor predecessors ->
    DeclaredInvariantSlot slot = false ->
    invariantPredecessorWitness predecessor slot = Some witness ->
    False.
Proof.
  intros succession predecessors predecessor slot witness
    Hsuccess Hin Habsent Hfound.
  pose proof
    (invariant_boundary_requires_exact_witness_domain
      succession predecessors predecessor Hsuccess Hin)
    as Hdomain.
  assert (Hdeclared : DeclaredInvariantSlot slot = true).
  {
    apply (proj2 (Hdomain slot)).
    exists witness.
    exact Hfound.
  }
  rewrite Habsent in Hdeclared.
  discriminate.
Qed.

Theorem every_relevant_predecessor_establishes_exact_invariant :
  forall succession predecessors predecessor,
    InvariantBoundarySuccess succession predecessors ->
    In predecessor predecessors ->
    ExactInvariantEstablished predecessor.
Proof.
  intros succession predecessors predecessor Hsuccess Hin.
  destruct Hsuccess as [Hdistinct Hstructural Hwitnesses Hestablished].
  eapply Hestablished.
  exact Hin.
Qed.

(*
  Structural compatibility and exact slot witnesses are still insufficient when
  the exact predecessor-specific invariant is not established.
*)
Theorem structural_compatibility_alone_cannot_establish_invariant :
  forall succession predecessors predecessor,
    In predecessor predecessors ->
    ResourceProjectionSuccess
      succession
      (invariantPredecessorProjection predecessor) ->
    ExactInvariantWitnessDomain predecessor ->
    ~ ExactInvariantEstablished predecessor ->
    ~ InvariantBoundarySuccess succession predecessors.
Proof.
  intros succession predecessors predecessor Hin
    Hstructural Hwitnesses Hmissing Hsuccess.
  apply Hmissing.
  eapply every_relevant_predecessor_establishes_exact_invariant.
  - exact Hsuccess.
  - exact Hin.
Qed.

(* Evidence on one branch cannot substitute for missing evidence on another. *)
Theorem path_local_invariant_evidence_does_not_leak :
  forall succession predecessors source target,
    source <> target ->
    In source predecessors ->
    In target predecessors ->
    ExactInvariantEstablished source ->
    ~ ExactInvariantEstablished target ->
    ~ InvariantBoundarySuccess succession predecessors.
Proof.
  intros succession predecessors source target Hdifferent
    HsourceIn HtargetIn HsourceEstablished HtargetMissing Hsuccess.
  apply HtargetMissing.
  eapply every_relevant_predecessor_establishes_exact_invariant.
  - exact Hsuccess.
  - exact HtargetIn.
Qed.

(* Loop initial entry and every accepted backedge face the same logical gate. *)
Theorem loop_initial_and_backedge_each_establish_invariant :
  forall succession predecessors initial backedge,
    InvariantBoundarySuccess succession predecessors ->
    In initial predecessors ->
    In backedge predecessors ->
    invariantPredecessorKind initial = LoopInitialPredecessor ->
    invariantPredecessorKind backedge = LoopBackedgePredecessor ->
    ExactInvariantEstablished initial /\
    ExactInvariantEstablished backedge.
Proof.
  intros succession predecessors initial backedge Hsuccess
    HinitialIn HbackedgeIn HinitialKind HbackedgeKind.
  split.
  - eapply every_relevant_predecessor_establishes_exact_invariant.
    + exact Hsuccess.
    + exact HinitialIn.
  - eapply every_relevant_predecessor_establishes_exact_invariant.
    + exact Hsuccess.
    + exact HbackedgeIn.
Qed.

(* Join predecessors are gated independently in exactly the same way. *)
Theorem two_join_predecessors_each_establish_invariant :
  forall succession predecessors left right,
    InvariantBoundarySuccess succession predecessors ->
    In left predecessors ->
    In right predecessors ->
    invariantPredecessorKind left = JoinContinuingPredecessor ->
    invariantPredecessorKind right = JoinContinuingPredecessor ->
    ExactInvariantEstablished left /\
    ExactInvariantEstablished right.
Proof.
  intros succession predecessors left right Hsuccess
    HleftIn HrightIn HleftKind HrightKind.
  split.
  - eapply every_relevant_predecessor_establishes_exact_invariant.
    + exact Hsuccess.
    + exact HleftIn.
  - eapply every_relevant_predecessor_establishes_exact_invariant.
    + exact Hsuccess.
    + exact HrightIn.
Qed.
