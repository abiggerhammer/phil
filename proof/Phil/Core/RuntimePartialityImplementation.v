From Stdlib Require Import Bool.Bool.
From Phil.Core Require Import RuntimePartiality.

(*
  PHIL-SYS-PARTIALITY-001 — finite executable correspondence.

  The production checker first validates the target-strengthening stage, then
  checks that every classified precondition is known, every hazard identity is
  valid, the exact hazard/disposition domains match, and every disposition is
  competent.  This file certifies that fail-closed conjunction without
  reimplementing concrete Map/Set/Text traversal.
*)

Inductive RuntimePartialityDecision : Type :=
| RuntimePartialityAccepted
| RuntimePartialityRejected.

Definition runtimePartialityFactsb
  (targetStageValid preconditionsKnown hazardKindsValid
    dispositionDomainExact dispositionsValid : bool) : bool :=
  andb targetStageValid
    (andb preconditionsKnown
      (andb hazardKindsValid
        (andb dispositionDomainExact dispositionsValid))).

Definition decideRuntimePartiality
  (targetStageValid preconditionsKnown hazardKindsValid
    dispositionDomainExact dispositionsValid : bool)
  : RuntimePartialityDecision :=
  if runtimePartialityFactsb
      targetStageValid preconditionsKnown hazardKindsValid
      dispositionDomainExact dispositionsValid
  then RuntimePartialityAccepted
  else RuntimePartialityRejected.

Theorem runtime_partiality_facts_true_iff_all_gates :
  forall targetStageValid preconditionsKnown hazardKindsValid
         dispositionDomainExact dispositionsValid,
    runtimePartialityFactsb
      targetStageValid preconditionsKnown hazardKindsValid
      dispositionDomainExact dispositionsValid = true <->
    targetStageValid = true /\
    preconditionsKnown = true /\
    hazardKindsValid = true /\
    dispositionDomainExact = true /\
    dispositionsValid = true.
Proof.
  intros.
  unfold runtimePartialityFactsb.
  repeat rewrite andb_true_iff.
  tauto.
Qed.

Theorem runtime_partiality_accept_iff_facts_true :
  forall targetStageValid preconditionsKnown hazardKindsValid
         dispositionDomainExact dispositionsValid,
    decideRuntimePartiality
      targetStageValid preconditionsKnown hazardKindsValid
      dispositionDomainExact dispositionsValid =
      RuntimePartialityAccepted <->
    runtimePartialityFactsb
      targetStageValid preconditionsKnown hazardKindsValid
      dispositionDomainExact dispositionsValid = true.
Proof.
  intros targetStageValid preconditionsKnown hazardKindsValid
    dispositionDomainExact dispositionsValid.
  unfold decideRuntimePartiality.
  destruct (runtimePartialityFactsb
    targetStageValid preconditionsKnown hazardKindsValid
    dispositionDomainExact dispositionsValid) eqn:Hfacts.
  - split; intros; reflexivity.
  - split.
    + intros Haccepted.
      discriminate Haccepted.
    + intros Htrue.
      discriminate Htrue.
Qed.

Theorem invalid_target_strengthening_stage_rejects :
  forall preconditionsKnown hazardKindsValid dispositionDomainExact dispositionsValid,
    decideRuntimePartiality
      false preconditionsKnown hazardKindsValid
      dispositionDomainExact dispositionsValid =
      RuntimePartialityRejected.
Proof.
  reflexivity.
Qed.

Theorem unknown_target_precondition_rejects :
  forall hazardKindsValid dispositionDomainExact dispositionsValid,
    decideRuntimePartiality
      true false hazardKindsValid dispositionDomainExact dispositionsValid =
      RuntimePartialityRejected.
Proof.
  reflexivity.
Qed.

Theorem invalid_capacity_or_partiality_identity_rejects :
  forall dispositionDomainExact dispositionsValid,
    decideRuntimePartiality
      true true false dispositionDomainExact dispositionsValid =
      RuntimePartialityRejected.
Proof.
  reflexivity.
Qed.

Theorem missing_or_substituted_hazard_disposition_rejects :
  forall dispositionsValid,
    decideRuntimePartiality true true true false dispositionsValid =
      RuntimePartialityRejected.
Proof.
  reflexivity.
Qed.

Theorem incompetent_partiality_disposition_rejects :
  decideRuntimePartiality true true true true false =
    RuntimePartialityRejected.
Proof.
  reflexivity.
Qed.

Theorem exact_partiality_relation_accepts :
  decideRuntimePartiality true true true true true =
    RuntimePartialityAccepted.
Proof.
  reflexivity.
Qed.

Inductive RuntimeDispositionKernelKind : Type :=
| RuntimeDispositionMappedSource
| RuntimeDispositionProvedSatisfied
| RuntimeDispositionEnforced
| RuntimeDispositionAssumption
| RuntimeDispositionDeployment.

Definition runtimeDispositionKernelFactsb
  (identityPresent payloadAdmitted retainedObligationWhenRequired : bool)
  : bool :=
  andb identityPresent
    (andb payloadAdmitted retainedObligationWhenRequired).

Theorem runtime_disposition_requires_nonempty_identity :
  forall payloadAdmitted retained,
    runtimeDispositionKernelFactsb false payloadAdmitted retained = false.
Proof.
  reflexivity.
Qed.

Theorem runtime_disposition_requires_admitted_payload :
  forall retained,
    runtimeDispositionKernelFactsb true false retained = false.
Proof.
  reflexivity.
Qed.

Theorem retained_obligation_gate_is_explicit :
  runtimeDispositionKernelFactsb true true false = false.
Proof.
  reflexivity.
Qed.
