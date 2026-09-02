From Phil.Core Require Import SystemsRevisionCanonicalization.

Set Implicit Arguments.

(*
  PHIL-SYS-REV-001 implementation correspondence.

  The Certified theorem fixes exactly which semantic coordinates determine the
  abstract SystemsArtifactRevision and Phase1StageContractRevision.  Concrete
  SemanticForm/Text encoding and SHA-256 remain the explicit ADR-019 bridge.

  This layer therefore extracts polymorphic construction plans: Rocq owns the
  dependency structure and namespace, while production may instantiate the
  coordinates with its native representation values.
*)

Inductive SystemsRevisionNamespace : Type :=
| SystemsArtifactRevisionNamespace
| Phase1StageContractRevisionNamespace.

Record SystemsArtifactRevisionPlan
  (Source Program StageContract Lowering : Type) : Type :=
  mkSystemsArtifactRevisionPlan {
    systemsArtifactRevisionPlanNamespace : SystemsRevisionNamespace;
    systemsArtifactRevisionPlanSource : Source;
    systemsArtifactRevisionPlanProgram : Program;
    systemsArtifactRevisionPlanStageContract : StageContract;
    systemsArtifactRevisionPlanLowering : Lowering
  }.

Definition planSystemsArtifactRevision
  {Source Program StageContract Lowering : Type}
  (source : Source)
  (program : Program)
  (stageContract : StageContract)
  (lowering : Lowering)
  : SystemsArtifactRevisionPlan Source Program StageContract Lowering :=
  {| systemsArtifactRevisionPlanNamespace := SystemsArtifactRevisionNamespace;
     systemsArtifactRevisionPlanSource := source;
     systemsArtifactRevisionPlanProgram := program;
     systemsArtifactRevisionPlanStageContract := stageContract;
     systemsArtifactRevisionPlanLowering := lowering |}.

Record Phase1StageContractRevisionPlan
  (Instance Realization Systems Profile Facts Dispositions Mechanisms Justifications : Type)
  : Type :=
  mkPhase1StageContractRevisionPlan {
    phase1StageContractRevisionPlanNamespace : SystemsRevisionNamespace;
    phase1StageContractRevisionPlanInstance : Instance;
    phase1StageContractRevisionPlanRealization : Realization;
    phase1StageContractRevisionPlanSystems : Systems;
    phase1StageContractRevisionPlanProfile : Profile;
    phase1StageContractRevisionPlanFacts : Facts;
    phase1StageContractRevisionPlanDispositions : Dispositions;
    phase1StageContractRevisionPlanMechanisms : Mechanisms;
    phase1StageContractRevisionPlanJustifications : Justifications
  }.

Definition planPhase1StageContractRevision
  {Instance Realization Systems Profile Facts Dispositions Mechanisms Justifications : Type}
  (instanceValue : Instance)
  (realization : Realization)
  (systems : Systems)
  (profile : Profile)
  (facts : Facts)
  (dispositions : Dispositions)
  (mechanisms : Mechanisms)
  (justifications : Justifications)
  : Phase1StageContractRevisionPlan
      Instance Realization Systems Profile Facts Dispositions Mechanisms Justifications :=
  {| phase1StageContractRevisionPlanNamespace := Phase1StageContractRevisionNamespace;
     phase1StageContractRevisionPlanInstance := instanceValue;
     phase1StageContractRevisionPlanRealization := realization;
     phase1StageContractRevisionPlanSystems := systems;
     phase1StageContractRevisionPlanProfile := profile;
     phase1StageContractRevisionPlanFacts := facts;
     phase1StageContractRevisionPlanDispositions := dispositions;
     phase1StageContractRevisionPlanMechanisms := mechanisms;
     phase1StageContractRevisionPlanJustifications := justifications |}.

Theorem systems_revision_plan_corresponds_certified_revision :
  forall input,
    let certified := deriveSystemsCanonicalRevision input in
    let plan := planSystemsArtifactRevision
      (systemsRevisionSourceSemantics input)
      (systemsRevisionProgramSemantics input)
      (systemsRevisionStageContractSemantics input)
      (systemsRevisionLoweringSemantics input) in
    systemsArtifactRevisionPlanNamespace plan = SystemsArtifactRevisionNamespace /\
    systemsArtifactRevisionPlanSource plan = canonicalSystemsSourceSemantics certified /\
    systemsArtifactRevisionPlanProgram plan = canonicalSystemsProgramSemantics certified /\
    systemsArtifactRevisionPlanStageContract plan =
      canonicalSystemsStageContractSemantics certified /\
    systemsArtifactRevisionPlanLowering plan = canonicalSystemsLoweringSemantics certified.
Proof.
  intros [source program stage lowering sourceFormatting diagnosticPresentation containerOrder backendSymbols].
  cbn.
  repeat split; reflexivity.
Qed.

Theorem stage_revision_plan_corresponds_certified_revision :
  forall input,
    let certified := deriveStageCanonicalRevision input in
    let plan := planPhase1StageContractRevision
      (stageRevisionArchitectureInstance input)
      (stageRevisionRealization input)
      (stageRevisionSystems input)
      (stageRevisionVerifierProfile input)
      (stageRevisionSourceFacts input)
      (stageRevisionDispositions input)
      (stageRevisionMechanisms input)
      (stageRevisionJustifications input) in
    phase1StageContractRevisionPlanNamespace plan = Phase1StageContractRevisionNamespace /\
    phase1StageContractRevisionPlanInstance plan =
      canonicalStageArchitectureInstance certified /\
    phase1StageContractRevisionPlanRealization plan = canonicalStageRealization certified /\
    phase1StageContractRevisionPlanSystems plan = canonicalStageSystems certified /\
    phase1StageContractRevisionPlanProfile plan = canonicalStageVerifierProfile certified /\
    phase1StageContractRevisionPlanFacts plan = canonicalStageSourceFacts certified /\
    phase1StageContractRevisionPlanDispositions plan = canonicalStageDispositions certified /\
    phase1StageContractRevisionPlanMechanisms plan = canonicalStageMechanisms certified /\
    phase1StageContractRevisionPlanJustifications plan = canonicalStageJustifications certified.
Proof.
  intros [instanceValue realization systems profile facts dispositions mechanisms justifications
          sourceFormatting diagnosticPresentation containerOrder backendSymbols].
  cbn.
  repeat split; reflexivity.
Qed.

Theorem systems_revision_plan_ignores_nonsemantic_metadata :
  forall first second,
    systemsRevisionSourceSemantics first = systemsRevisionSourceSemantics second ->
    systemsRevisionProgramSemantics first = systemsRevisionProgramSemantics second ->
    systemsRevisionStageContractSemantics first = systemsRevisionStageContractSemantics second ->
    systemsRevisionLoweringSemantics first = systemsRevisionLoweringSemantics second ->
    planSystemsArtifactRevision
      (systemsRevisionSourceSemantics first)
      (systemsRevisionProgramSemantics first)
      (systemsRevisionStageContractSemantics first)
      (systemsRevisionLoweringSemantics first) =
    planSystemsArtifactRevision
      (systemsRevisionSourceSemantics second)
      (systemsRevisionProgramSemantics second)
      (systemsRevisionStageContractSemantics second)
      (systemsRevisionLoweringSemantics second).
Proof.
  intros first second Hsource Hprogram Hstage Hlowering.
  rewrite Hsource, Hprogram, Hstage, Hlowering.
  reflexivity.
Qed.

Theorem stage_revision_plan_ignores_nonsemantic_metadata :
  forall first second,
    stageRevisionArchitectureInstance first = stageRevisionArchitectureInstance second ->
    stageRevisionRealization first = stageRevisionRealization second ->
    stageRevisionSystems first = stageRevisionSystems second ->
    stageRevisionVerifierProfile first = stageRevisionVerifierProfile second ->
    stageRevisionSourceFacts first = stageRevisionSourceFacts second ->
    stageRevisionDispositions first = stageRevisionDispositions second ->
    stageRevisionMechanisms first = stageRevisionMechanisms second ->
    stageRevisionJustifications first = stageRevisionJustifications second ->
    planPhase1StageContractRevision
      (stageRevisionArchitectureInstance first)
      (stageRevisionRealization first)
      (stageRevisionSystems first)
      (stageRevisionVerifierProfile first)
      (stageRevisionSourceFacts first)
      (stageRevisionDispositions first)
      (stageRevisionMechanisms first)
      (stageRevisionJustifications first) =
    planPhase1StageContractRevision
      (stageRevisionArchitectureInstance second)
      (stageRevisionRealization second)
      (stageRevisionSystems second)
      (stageRevisionVerifierProfile second)
      (stageRevisionSourceFacts second)
      (stageRevisionDispositions second)
      (stageRevisionMechanisms second)
      (stageRevisionJustifications second).
Proof.
  intros first second Hinstance Hrealization Hsystems Hprofile Hfacts Hdispositions Hmechanisms Hjustifications.
  rewrite Hinstance, Hrealization, Hsystems, Hprofile,
    Hfacts, Hdispositions, Hmechanisms, Hjustifications.
  reflexivity.
Qed.
