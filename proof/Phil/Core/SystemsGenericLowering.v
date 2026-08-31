From Stdlib Require Import Arith.PeanoNat.

From Phil.Core Require Import
  ArchitectureIdentity
  ArchitectureInstantiation
  ArchitectureRealization
  SystemsStageClosure.

(*
  PHIL-SYS-GENERIC-001 — witness-neutral checked-Core -> Systems lowering.

  The executable implementation computes content-bound identities using concrete
  canonical serialization, Maps/Sets/Text, SHA-256-like digest wrappers, and a
  concrete GenericRealizationContext.  This proof models those identities by
  structural records.  The correspondence workflow checks the unchanged Haskell
  producer and both witness adapters against this normalized theorem boundary.

  Crucially, no witness/program discriminator occurs in the lowering input or
  result.  A presentation label exists only at the adapter boundary and is
  erased before generic lowering.
*)

Record GenericCoreInput : Type := mkGenericCoreInput {
  genericCoreArchitectureInstance : ArchitectureInstanceIdentity;
  genericCoreSemanticRevision : nat
}.

Record GenericRealizationContextFacts : Type := mkGenericRealizationContextFacts {
  genericContextRevision : nat;
  genericContextSemanticRevision : nat;
  genericContextVerifierProfileRevision : nat;
  genericContextRealizationRefsRevision : nat;
  genericContextDecisionRevision : nat;
  genericContextRuntimeSiteRevision : nat;
  genericContextRealizationSemanticRevision : nat
}.

Definition GenericRealizationContextValid
  (context : GenericRealizationContextFacts) : Prop :=
  genericContextRevision context <> 0 /\
  genericContextVerifierProfileRevision context <> 0 /\
  genericContextRealizationRefsRevision context <> 0 /\
  genericContextRealizationSemanticRevision context <> 0.

Record GenericSourceRevision : Type := mkGenericSourceRevision {
  genericSourceInstanceRevision : InstanceRevision;
  genericSourceCoreSemanticRevision : nat
}.

Record GenericSystemsRevision : Type := mkGenericSystemsRevision {
  genericSystemsSourceRevision : GenericSourceRevision;
  genericSystemsContextSemanticRevision : nat;
  genericSystemsDecisionRevision : nat;
  genericSystemsRuntimeSiteRevision : nat
}.

Record GenericStageContractRevision : Type := mkGenericStageContractRevision {
  genericStageInstanceRevision : InstanceRevision;
  genericStageRealizationRevision : ArchitectureRealizationRevision;
  genericStageSystemsRevision : GenericSystemsRevision;
  genericStageVerifierProfileRevision : nat
}.

Record GenericLoweringResult : Type := mkGenericLoweringResult {
  genericResultSourceRevision : GenericSourceRevision;
  genericResultArchitectureRealization : ArchitectureRealizationRevision;
  genericResultSystemsRevision : GenericSystemsRevision;
  genericResultStageContractRevision : GenericStageContractRevision;
  genericResultVerifierProfileRevision : nat
}.

Definition deriveGenericSourceRevision
  (input : GenericCoreInput) : GenericSourceRevision :=
  {| genericSourceInstanceRevision :=
       identityInstanceRevision (genericCoreArchitectureInstance input);
     genericSourceCoreSemanticRevision := genericCoreSemanticRevision input |}.

Definition deriveGenericSystemsRevision
  (input : GenericCoreInput)
  (context : GenericRealizationContextFacts) : GenericSystemsRevision :=
  {| genericSystemsSourceRevision := deriveGenericSourceRevision input;
     genericSystemsContextSemanticRevision :=
       genericContextSemanticRevision context;
     genericSystemsDecisionRevision := genericContextDecisionRevision context;
     genericSystemsRuntimeSiteRevision := genericContextRuntimeSiteRevision context |}.

Definition lowerGenericSystemsModel
  (input : GenericCoreInput)
  (context : GenericRealizationContextFacts) : GenericLoweringResult :=
  let sourceRevision := deriveGenericSourceRevision input in
  let realization := deriveArchitectureRealizationRevision
    (genericCoreArchitectureInstance input)
    (genericContextRealizationSemanticRevision context) in
  let systemsRevision := deriveGenericSystemsRevision input context in
  let stageRevision :=
    {| genericStageInstanceRevision :=
         identityInstanceRevision (genericCoreArchitectureInstance input);
       genericStageRealizationRevision := realization;
       genericStageSystemsRevision := systemsRevision;
       genericStageVerifierProfileRevision :=
         genericContextVerifierProfileRevision context |} in
  {| genericResultSourceRevision := sourceRevision;
     genericResultArchitectureRealization := realization;
     genericResultSystemsRevision := systemsRevision;
     genericResultStageContractRevision := stageRevision;
     genericResultVerifierProfileRevision :=
       genericContextVerifierProfileRevision context |}.

Definition GenericLoweringAccepted
  (input : GenericCoreInput)
  (context : GenericRealizationContextFacts)
  (result : GenericLoweringResult) : Prop :=
  GenericRealizationContextValid context /\
  result = lowerGenericSystemsModel input context.

(* Presentation belongs to witness adaptation, not generic lowering. *)
Record GenericWitnessAdapter : Type := mkGenericWitnessAdapter {
  genericWitnessPresentationLabel : nat;
  genericWitnessCoreInput : GenericCoreInput
}.

Definition adaptGenericWitness
  (adapter : GenericWitnessAdapter) : GenericCoreInput :=
  genericWitnessCoreInput adapter.

Theorem generic_lowering_is_deterministic :
  forall input context,
    lowerGenericSystemsModel input context =
    lowerGenericSystemsModel input context.
Proof.
  reflexivity.
Qed.

Theorem witness_presentation_rename_is_nonsemantic :
  forall oldLabel newLabel input context,
    lowerGenericSystemsModel
      (adaptGenericWitness
        {| genericWitnessPresentationLabel := oldLabel;
           genericWitnessCoreInput := input |})
      context =
    lowerGenericSystemsModel
      (adaptGenericWitness
        {| genericWitnessPresentationLabel := newLabel;
           genericWitnessCoreInput := input |})
      context.
Proof.
  reflexivity.
Qed.

Theorem generic_lowering_preserves_exact_architecture_instance_revision :
  forall input context,
    genericSourceInstanceRevision
      (genericResultSourceRevision
        (lowerGenericSystemsModel input context)) =
    identityInstanceRevision (genericCoreArchitectureInstance input).
Proof.
  reflexivity.
Qed.

Theorem generic_lowering_realization_preserves_exact_architecture_instance :
  forall input context,
    realizationRevisionInstance
      (genericResultArchitectureRealization
        (lowerGenericSystemsModel input context)) =
    identityInstanceRevision (genericCoreArchitectureInstance input).
Proof.
  reflexivity.
Qed.

Theorem explicit_realization_change_revises_only_realization_identity :
  forall input prior replacement,
    genericContextRealizationSemanticRevision prior <>
      genericContextRealizationSemanticRevision replacement ->
    genericResultArchitectureRealization
      (lowerGenericSystemsModel input prior) <>
    genericResultArchitectureRealization
      (lowerGenericSystemsModel input replacement).
Proof.
  intros input prior replacement Hneq.
  cbn.
  apply selected_realization_change_revises_realization.
  exact Hneq.
Qed.

Theorem explicit_realization_change_preserves_source_instance_revision :
  forall input prior replacement,
    genericSourceInstanceRevision
      (genericResultSourceRevision
        (lowerGenericSystemsModel input prior)) =
    genericSourceInstanceRevision
      (genericResultSourceRevision
        (lowerGenericSystemsModel input replacement)).
Proof.
  reflexivity.
Qed.

Theorem core_semantic_change_revises_systems_identity :
  forall instance priorCore replacementCore context,
    priorCore <> replacementCore ->
    genericResultSystemsRevision
      (lowerGenericSystemsModel
        {| genericCoreArchitectureInstance := instance;
           genericCoreSemanticRevision := priorCore |}
        context) <>
    genericResultSystemsRevision
      (lowerGenericSystemsModel
        {| genericCoreArchitectureInstance := instance;
           genericCoreSemanticRevision := replacementCore |}
        context).
Proof.
  intros instance priorCore replacementCore context Hneq Heq.
  apply Hneq.
  exact
    (f_equal
      (fun revision =>
        genericSourceCoreSemanticRevision
          (genericSystemsSourceRevision revision))
      Heq).
Qed.

Theorem realization_context_semantic_change_revises_systems_identity :
  forall input prior replacement,
    genericContextSemanticRevision prior <>
      genericContextSemanticRevision replacement ->
    genericResultSystemsRevision
      (lowerGenericSystemsModel input prior) <>
    genericResultSystemsRevision
      (lowerGenericSystemsModel input replacement).
Proof.
  intros input prior replacement Hneq Heq.
  apply Hneq.
  exact
    (f_equal genericSystemsContextSemanticRevision Heq).
Qed.

Theorem decision_change_revises_systems_identity :
  forall input prior replacement,
    genericContextDecisionRevision prior <>
      genericContextDecisionRevision replacement ->
    genericResultSystemsRevision
      (lowerGenericSystemsModel input prior) <>
    genericResultSystemsRevision
      (lowerGenericSystemsModel input replacement).
Proof.
  intros input prior replacement Hneq Heq.
  apply Hneq.
  exact (f_equal genericSystemsDecisionRevision Heq).
Qed.

Theorem runtime_site_change_revises_systems_identity :
  forall input prior replacement,
    genericContextRuntimeSiteRevision prior <>
      genericContextRuntimeSiteRevision replacement ->
    genericResultSystemsRevision
      (lowerGenericSystemsModel input prior) <>
    genericResultSystemsRevision
      (lowerGenericSystemsModel input replacement).
Proof.
  intros input prior replacement Hneq Heq.
  apply Hneq.
  exact (f_equal genericSystemsRuntimeSiteRevision Heq).
Qed.

Theorem missing_realization_refs_cannot_be_accepted :
  forall input context result,
    genericContextRealizationRefsRevision context = 0 ->
    ~ GenericLoweringAccepted input context result.
Proof.
  intros input context result Hmissing [Hvalid _].
  destruct Hvalid as [_ [_ [Href _]]].
  apply Href.
  exact Hmissing.
Qed.

Theorem empty_verifier_profile_cannot_be_accepted :
  forall input context result,
    genericContextVerifierProfileRevision context = 0 ->
    ~ GenericLoweringAccepted input context result.
Proof.
  intros input context result Hmissing [Hvalid _].
  destruct Hvalid as [_ [Hprofile _]].
  apply Hprofile.
  exact Hmissing.
Qed.

(* Certified composition: generic production does not replace the already
   Certified StageClosure theorem.  A certified generic result must be both an
   accepted generic-lowering result and an exact bidirectional StageClosure. *)
Record CertifiedGenericSystemsLowering
  (input : GenericCoreInput)
  (context : GenericRealizationContextFacts)
  (result : GenericLoweringResult)
  (factModel : StageFactModel)
  (live : SourceResponsibilitySet)
  (mechanisms : TargetMechanismSet)
  (dispositions : SourceDispositionEnvironment)
  (kinds : TargetMechanismKindEnvironment)
  (justifications : TargetJustificationEnvironment)
  (scope effective : ValidityMap)
  (identity : StageClosureIdentityFacts) : Prop :=
  mkCertifiedGenericSystemsLowering {
    certifiedGenericLoweringAccepted :
      GenericLoweringAccepted input context result;
    certifiedGenericStageClosure :
      SystemsStageClosurePreserved
        factModel live mechanisms dispositions kinds justifications
        scope effective identity
  }.

Theorem certified_generic_lowering_preserves_stage_closure :
  forall input context result factModel live mechanisms dispositions kinds
         justifications scope effective identity,
    CertifiedGenericSystemsLowering
      input context result factModel live mechanisms dispositions kinds
      justifications scope effective identity ->
    SystemsStageClosurePreserved
      factModel live mechanisms dispositions kinds justifications
      scope effective identity.
Proof.
  intros input context result factModel live mechanisms dispositions kinds
    justifications scope effective identity Hcertified.
  destruct Hcertified as [_ Hclosure].
  exact Hclosure.
Qed.

Theorem certified_generic_lowering_is_witness_neutral :
  forall oldLabel newLabel input context result factModel live mechanisms
         dispositions kinds justifications scope effective identity,
    CertifiedGenericSystemsLowering
      input context result factModel live mechanisms dispositions kinds
      justifications scope effective identity ->
    lowerGenericSystemsModel
      (adaptGenericWitness
        {| genericWitnessPresentationLabel := oldLabel;
           genericWitnessCoreInput := input |}) context =
    lowerGenericSystemsModel
      (adaptGenericWitness
        {| genericWitnessPresentationLabel := newLabel;
           genericWitnessCoreInput := input |}) context.
Proof.
  intros.
  apply witness_presentation_rename_is_nonsemantic.
Qed.
