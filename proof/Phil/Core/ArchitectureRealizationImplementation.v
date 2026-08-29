From Phil.Core Require Import ArchitectureIdentity ArchitectureRealization.

Set Implicit Arguments.

(*
  PHIL-ARCH-REALIZE-001 — representation-neutral realization-construction plan.

  The Certified architecture-realization model fixes exactly three coordinates
  for one realization revision: the abstract architecture InstanceKey, its exact
  InstanceRevision, and the selected realization semantics. Concrete Text and
  SemanticForm serialization remain a native representation boundary.

  Provider-replacement qualification is deliberately not reimplemented here.
  Its Certified invariants remain a separate implementation-refinement
  dependency of the broader ARCH-REALIZE obligation.
*)

Record ArchitectureRealizationPlan
  (Key Revision Semantics : Type) : Type :=
  mkArchitectureRealizationPlan {
    architectureRealizationPlanInstanceKey : Key;
    architectureRealizationPlanInstanceRevision : Revision;
    architectureRealizationPlanSemantics : Semantics
  }.

Definition planArchitectureRealization
  {Key Revision Semantics : Type}
  (instanceKey : Key)
  (instanceRevision : Revision)
  (semantics : Semantics)
  : ArchitectureRealizationPlan Key Revision Semantics :=
  {| architectureRealizationPlanInstanceKey := instanceKey;
     architectureRealizationPlanInstanceRevision := instanceRevision;
     architectureRealizationPlanSemantics := semantics |}.

Theorem architecture_realization_plan_corresponds_certified_revision :
  forall instance semantics,
    let certified := deriveArchitectureRealizationRevision instance semantics in
    let plan := planArchitectureRealization
      (identityInstanceKey instance)
      (identityInstanceRevision instance)
      semantics in
    architectureRealizationPlanInstanceKey plan =
      realizationRevisionInstanceKey certified /\
    architectureRealizationPlanInstanceRevision plan =
      realizationRevisionInstance certified /\
    architectureRealizationPlanSemantics plan =
      realizationRevisionSemantics certified.
Proof.
  intros [instanceKey instanceRevision] semantics.
  cbn.
  repeat split; reflexivity.
Qed.

Theorem realization_semantics_difference_revises_plan :
  forall (Key Revision Semantics : Type)
         (instanceKey : Key)
         (instanceRevision : Revision)
         (prior replacement : Semantics),
    prior <> replacement ->
    planArchitectureRealization instanceKey instanceRevision prior <>
    planArchitectureRealization instanceKey instanceRevision replacement.
Proof.
  intros Key Revision Semantics instanceKey instanceRevision
    prior replacement Hneq Heq.
  apply Hneq.
  exact (f_equal
    (fun plan : ArchitectureRealizationPlan Key Revision Semantics =>
      architectureRealizationPlanSemantics plan)
    Heq).
Qed.

Theorem realization_instance_key_difference_revises_plan :
  forall (Key Revision Semantics : Type)
         (priorKey replacementKey : Key)
         (instanceRevision : Revision)
         (semantics : Semantics),
    priorKey <> replacementKey ->
    planArchitectureRealization priorKey instanceRevision semantics <>
    planArchitectureRealization replacementKey instanceRevision semantics.
Proof.
  intros Key Revision Semantics priorKey replacementKey
    instanceRevision semantics Hneq Heq.
  apply Hneq.
  exact (f_equal
    (fun plan : ArchitectureRealizationPlan Key Revision Semantics =>
      architectureRealizationPlanInstanceKey plan)
    Heq).
Qed.

Theorem realization_instance_revision_difference_revises_plan :
  forall (Key Revision Semantics : Type)
         (instanceKey : Key)
         (priorRevision replacementRevision : Revision)
         (semantics : Semantics),
    priorRevision <> replacementRevision ->
    planArchitectureRealization instanceKey priorRevision semantics <>
    planArchitectureRealization instanceKey replacementRevision semantics.
Proof.
  intros Key Revision Semantics instanceKey priorRevision replacementRevision
    semantics Hneq Heq.
  apply Hneq.
  exact (f_equal
    (fun plan : ArchitectureRealizationPlan Key Revision Semantics =>
      architectureRealizationPlanInstanceRevision plan)
    Heq).
Qed.
