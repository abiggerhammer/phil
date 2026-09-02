From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ResourceJoin.

(*
  PHIL-RES-JOIN-001 implementation correspondence.

  ResourceProjectionSuccess is exactly three representation-neutral facts:

  - every incoming linear owner is represented exactly once;
  - every post-state binding names an incoming owner; and
  - every bound owner satisfies the slot's semantic-subject requirement.

  Concrete owner/slot enumeration, Map/Set representation, CFG validation, and
  construction/truth of explicit succession evidence remain correspondence or
  predecessor boundaries.  ContextJoin/ProcessJoin conservation stays in the
  already-Certified predecessor theorem rather than being duplicated here.
*)

Definition EveryIncomingLinearExactlyOnceBound
  (projection : ResourceProjection) : Prop :=
  forall owner,
    projectionIncomingLinear projection owner = true ->
    ExactlyOnceBound (projectionBindings projection) owner.

Definition NoInventedProjectionOwner
  (projection : ResourceProjection) : Prop :=
  forall slot owner,
    projectionBindings projection slot = Some owner ->
    projectionIncomingLinear projection owner = true.

Definition EveryProjectionSubjectAdmissible
  (succession : SuccessionEvidence)
  (projection : ResourceProjection) : Prop :=
  forall slot owner,
    projectionBindings projection slot = Some owner ->
    subjectAdmissible
      succession
      (projectionSubjectOf projection)
      (projectionRequirements projection slot)
      owner.

Theorem resource_projection_success_is_exact_facts :
  forall succession projection,
    ResourceProjectionSuccess succession projection <->
    EveryIncomingLinearExactlyOnceBound projection /\
    NoInventedProjectionOwner projection /\
    EveryProjectionSubjectAdmissible succession projection.
Proof.
  intros succession projection.
  unfold ResourceProjectionSuccess,
    EveryIncomingLinearExactlyOnceBound,
    NoInventedProjectionOwner,
    EveryProjectionSubjectAdmissible.
  reflexivity.
Qed.

Inductive ResourceProjectionDecision : Type :=
| ResourceProjectionAcceptedDecision
| ResourceProjectionLinearCoverageDecision
| ResourceProjectionInventedOwnerDecision
| ResourceProjectionSubjectAdmissionDecision.

Definition decideResourceProjectionByFacts
  (allIncomingLinearExactlyOnceBound : bool)
  (noInventedOwners : bool)
  (allBoundSubjectsAdmissible : bool)
  : ResourceProjectionDecision :=
  if allIncomingLinearExactlyOnceBound then
    if noInventedOwners then
      if allBoundSubjectsAdmissible then
        ResourceProjectionAcceptedDecision
      else ResourceProjectionSubjectAdmissionDecision
    else ResourceProjectionInventedOwnerDecision
  else ResourceProjectionLinearCoverageDecision.

Theorem resource_projection_decision_accepted_iff :
  forall allIncomingLinearExactlyOnceBound noInventedOwners allBoundSubjectsAdmissible,
    decideResourceProjectionByFacts
      allIncomingLinearExactlyOnceBound
      noInventedOwners
      allBoundSubjectsAdmissible = ResourceProjectionAcceptedDecision <->
    allIncomingLinearExactlyOnceBound = true /\
    noInventedOwners = true /\
    allBoundSubjectsAdmissible = true.
Proof.
  intros allIncomingLinearExactlyOnceBound noInventedOwners allBoundSubjectsAdmissible.
  destruct allIncomingLinearExactlyOnceBound,
    noInventedOwners,
    allBoundSubjectsAdmissible;
    simpl; intuition discriminate.
Qed.

Theorem resource_projection_decision_corresponds_success :
  forall succession projection
    allIncomingLinearExactlyOnceBound noInventedOwners allBoundSubjectsAdmissible,
    (allIncomingLinearExactlyOnceBound = true <->
      EveryIncomingLinearExactlyOnceBound projection) ->
    (noInventedOwners = true <->
      NoInventedProjectionOwner projection) ->
    (allBoundSubjectsAdmissible = true <->
      EveryProjectionSubjectAdmissible succession projection) ->
    (decideResourceProjectionByFacts
      allIncomingLinearExactlyOnceBound
      noInventedOwners
      allBoundSubjectsAdmissible = ResourceProjectionAcceptedDecision <->
      ResourceProjectionSuccess succession projection).
Proof.
  intros succession projection
    allIncomingLinearExactlyOnceBound noInventedOwners allBoundSubjectsAdmissible
    Hlinear HnoInvented Hsubjects.
  rewrite resource_projection_decision_accepted_iff.
  rewrite resource_projection_success_is_exact_facts.
  split.
  - intros [HlinearBool [HnoInventedBool HsubjectsBool]].
    split.
    + apply (proj1 Hlinear).
      exact HlinearBool.
    + split.
      * apply (proj1 HnoInvented).
        exact HnoInventedBool.
      * apply (proj1 Hsubjects).
        exact HsubjectsBool.
  - intros [HlinearProp [HnoInventedProp HsubjectsProp]].
    split.
    + apply (proj2 Hlinear).
      exact HlinearProp.
    + split.
      * apply (proj2 HnoInvented).
        exact HnoInventedProp.
      * apply (proj2 Hsubjects).
        exact HsubjectsProp.
Qed.
