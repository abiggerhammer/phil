From Stdlib Require Import Bool.Bool.

From Phil.Assurance Require Import ValidityScope.
From Phil.Systems Require Import FactDisposition.
From Phil.Core Require Import SystemsStageClosure.

(*
  Mechanical implementation-correspondence surface for already-Certified
  PHIL-SYS-STAGE-CLOSURE-001.

  The extracted kernel owns only normalized decision structure. Concrete
  Text/Map/Set/list enumeration, responsibility/mechanism derivation,
  canonical revision construction, diagnostics, predecessor evidence truth,
  and Haskell representation remain explicit correspondence boundaries.
*)

Inductive SourceClosureDecision : Type :=
| SourceClosureAcceptedDecision
| SourceClosureCoverageDecision
| SourceClosureEmptyFactDecision
| SourceClosureDispositionDecision.

Definition decideSourceClosureByFacts
  (coverageExact noEmptyFact dispositionsPermitted : bool)
  : SourceClosureDecision :=
  if coverageExact then
    if noEmptyFact then
      if dispositionsPermitted
      then SourceClosureAcceptedDecision
      else SourceClosureDispositionDecision
    else SourceClosureEmptyFactDecision
  else SourceClosureCoverageDecision.

Theorem source_closure_decision_exact :
  forall coverageExact noEmptyFact dispositionsPermitted,
    decideSourceClosureByFacts coverageExact noEmptyFact dispositionsPermitted =
      SourceClosureAcceptedDecision <->
    coverageExact = true /\
    noEmptyFact = true /\
    dispositionsPermitted = true.
Proof.
  intros coverageExact noEmptyFact dispositionsPermitted.
  unfold decideSourceClosureByFacts.
  destruct coverageExact;
  destruct noEmptyFact;
  destruct dispositionsPermitted;
  simpl; intuition discriminate.
Qed.

Theorem source_closure_decision_corresponds_certified_relation :
  forall live mechanisms dispositions
         coverageExact noEmptyFact dispositionsPermitted,
    (coverageExact = true <->
      ExactSourceDispositionCoverage live dispositions) ->
    (noEmptyFact = true <->
      live (SourceFactResponsibility 0) = false) ->
    (dispositionsPermitted = true <->
      forall responsibility disposition,
        dispositions responsibility = Some disposition ->
        ClosureDispositionValid mechanisms disposition) ->
    decideSourceClosureByFacts
      coverageExact noEmptyFact dispositionsPermitted =
      SourceClosureAcceptedDecision <->
    SourceClosureVerified live mechanisms dispositions.
Proof.
  intros live mechanisms dispositions
    coverageExact noEmptyFact dispositionsPermitted
    Hcoverage Hempty Hpermitted.
  rewrite source_closure_decision_exact.
  split.
  - intros [HcoverageB [HemptyB HpermittedB]].
    constructor.
    + apply (proj1 Hcoverage). exact HcoverageB.
    + apply (proj1 Hempty). exact HemptyB.
    + apply (proj1 Hpermitted). exact HpermittedB.
  - intros Hverified.
    destruct Hverified as [HcoverageP HemptyP HpermittedP].
    repeat split.
    + apply (proj2 Hcoverage). exact HcoverageP.
    + apply (proj2 Hempty). exact HemptyP.
    + apply (proj2 Hpermitted). exact HpermittedP.
Qed.

Inductive TargetClosureDecision : Type :=
| TargetClosureAcceptedDecision
| TargetClosureCoverageDecision
| TargetClosureEmptyMechanismDecision
| TargetClosureJustificationDecision.

Definition decideTargetClosureByFacts
  (coverageExact noEmptyMechanism justificationsValid : bool)
  : TargetClosureDecision :=
  if coverageExact then
    if noEmptyMechanism then
      if justificationsValid
      then TargetClosureAcceptedDecision
      else TargetClosureJustificationDecision
    else TargetClosureEmptyMechanismDecision
  else TargetClosureCoverageDecision.

Theorem target_closure_decision_exact :
  forall coverageExact noEmptyMechanism justificationsValid,
    decideTargetClosureByFacts
      coverageExact noEmptyMechanism justificationsValid =
      TargetClosureAcceptedDecision <->
    coverageExact = true /\
    noEmptyMechanism = true /\
    justificationsValid = true.
Proof.
  intros coverageExact noEmptyMechanism justificationsValid.
  unfold decideTargetClosureByFacts.
  destruct coverageExact;
  destruct noEmptyMechanism;
  destruct justificationsValid;
  simpl; intuition discriminate.
Qed.

Theorem target_closure_decision_corresponds_certified_relation :
  forall live mechanisms kinds justifications
         coverageExact noEmptyMechanism justificationsValid,
    (coverageExact = true <->
      ExactTargetMechanismCoverage mechanisms kinds justifications) ->
    (noEmptyMechanism = true <->
      mechanisms 0 = false) ->
    (justificationsValid = true <->
      forall mechanism justification,
        justifications mechanism = Some justification ->
        TargetJustificationValid live justification) ->
    decideTargetClosureByFacts
      coverageExact noEmptyMechanism justificationsValid =
      TargetClosureAcceptedDecision <->
    TargetClosureVerified live mechanisms kinds justifications.
Proof.
  intros live mechanisms kinds justifications
    coverageExact noEmptyMechanism justificationsValid
    Hcoverage Hempty Hvalid.
  rewrite target_closure_decision_exact.
  split.
  - intros [HcoverageB [HemptyB HvalidB]].
    constructor.
    + apply (proj1 Hcoverage). exact HcoverageB.
    + apply (proj1 Hempty). exact HemptyB.
    + apply (proj1 Hvalid). exact HvalidB.
  - intros Hverified.
    destruct Hverified as [HcoverageP HemptyP HvalidP].
    repeat split.
    + apply (proj2 Hcoverage). exact HcoverageP.
    + apply (proj2 Hempty). exact HemptyP.
    + apply (proj2 Hvalid). exact HvalidP.
Qed.

Inductive StageIdentityDecision : Type :=
| StageIdentityAcceptedDecision
| StageIdentitySubjectDecision
| StageIdentityInstanceDecision
| StageIdentityRealizationDecision
| StageIdentitySystemsDecision
| StageIdentityContractDecision
| StageIdentityProfileDecision
| StageIdentityRecomputedSystemsDecision
| StageIdentityRecomputedFinalDecision
| StageIdentityStoredSystemsDecision
| StageIdentityStoredFinalDecision.

Definition decideStageIdentityByFacts
  (subjectExact instanceExact realizationExact systemsExact contractExact
   profileExact recomputedSystemsExact recomputedFinalExact
   storedSystemsPresent storedFinalPresent : bool)
  : StageIdentityDecision :=
  if subjectExact then
    if instanceExact then
      if realizationExact then
        if systemsExact then
          if contractExact then
            if profileExact then
              if recomputedSystemsExact then
                if recomputedFinalExact then
                  if storedSystemsPresent then
                    if storedFinalPresent
                    then StageIdentityAcceptedDecision
                    else StageIdentityStoredFinalDecision
                  else StageIdentityStoredSystemsDecision
                else StageIdentityRecomputedFinalDecision
              else StageIdentityRecomputedSystemsDecision
            else StageIdentityProfileDecision
          else StageIdentityContractDecision
        else StageIdentitySystemsDecision
      else StageIdentityRealizationDecision
    else StageIdentityInstanceDecision
  else StageIdentitySubjectDecision.

Theorem stage_identity_decision_exact :
  forall subjectExact instanceExact realizationExact systemsExact contractExact
         profileExact recomputedSystemsExact recomputedFinalExact
         storedSystemsPresent storedFinalPresent,
    decideStageIdentityByFacts
      subjectExact instanceExact realizationExact systemsExact contractExact
      profileExact recomputedSystemsExact recomputedFinalExact
      storedSystemsPresent storedFinalPresent =
      StageIdentityAcceptedDecision <->
    subjectExact = true /\
    instanceExact = true /\
    realizationExact = true /\
    systemsExact = true /\
    contractExact = true /\
    profileExact = true /\
    recomputedSystemsExact = true /\
    recomputedFinalExact = true /\
    storedSystemsPresent = true /\
    storedFinalPresent = true.
Proof.
  intros subjectExact instanceExact realizationExact systemsExact contractExact
    profileExact recomputedSystemsExact recomputedFinalExact
    storedSystemsPresent storedFinalPresent.
  unfold decideStageIdentityByFacts.
  destruct subjectExact;
  destruct instanceExact;
  destruct realizationExact;
  destruct systemsExact;
  destruct contractExact;
  destruct profileExact;
  destruct recomputedSystemsExact;
  destruct recomputedFinalExact;
  destruct storedSystemsPresent;
  destruct storedFinalPresent;
  simpl; intuition discriminate.
Qed.

Theorem stage_identity_decision_corresponds_certified_relation :
  forall identity
         subjectExact instanceExact realizationExact systemsExact contractExact
         profileExact recomputedSystemsExact recomputedFinalExact
         storedSystemsPresent storedFinalPresent,
    (subjectExact = true <->
      closureConcreteSubjectRevision identity =
        closureNextStageSubjectRevision identity) ->
    (instanceExact = true <->
      closureConcreteInstanceRevision identity =
        closureNextStageInstanceRevision identity) ->
    (realizationExact = true <->
      closureConcreteRealizationRevision identity =
        closureNextStageRealizationRevision identity) ->
    (systemsExact = true <->
      closureConcreteSystemsRevision identity =
        closureNextStageSystemsRevision identity) ->
    (contractExact = true <->
      closureConcreteStageContractRevision identity =
        closureNextStageStageContractRevision identity) ->
    (profileExact = true <->
      closureConcreteVerifierProfileRevision identity =
        closureNextStageVerifierProfileRevision identity) ->
    (recomputedSystemsExact = true <->
      closureRecomputedSystemsRevision identity =
        closureStoredSystemsRevision identity) ->
    (recomputedFinalExact = true <->
      closureRecomputedFinalRevision identity =
        closureStoredFinalRevision identity) ->
    (storedSystemsPresent = true <->
      closureStoredSystemsRevision identity <> 0) ->
    (storedFinalPresent = true <->
      closureStoredFinalRevision identity <> 0) ->
    decideStageIdentityByFacts
      subjectExact instanceExact realizationExact systemsExact contractExact
      profileExact recomputedSystemsExact recomputedFinalExact
      storedSystemsPresent storedFinalPresent =
      StageIdentityAcceptedDecision <->
    StageClosureIdentityValid identity.
Proof.
  intros identity
    subjectExact instanceExact realizationExact systemsExact contractExact
    profileExact recomputedSystemsExact recomputedFinalExact
    storedSystemsPresent storedFinalPresent
    Hsubject Hinstance Hrealization Hsystems Hcontract Hprofile
    HrecomputedSystems HrecomputedFinal HstoredSystems HstoredFinal.
  rewrite stage_identity_decision_exact.
  split.
  - intros [HsubjectB [HinstanceB [HrealizationB [HsystemsB [HcontractB
      [HprofileB [HrecomputedSystemsB [HrecomputedFinalB
      [HstoredSystemsB HstoredFinalB]]]]]]]]].
    unfold StageClosureIdentityValid.
    repeat split.
    + apply (proj1 Hsubject). exact HsubjectB.
    + apply (proj1 Hinstance). exact HinstanceB.
    + apply (proj1 Hrealization). exact HrealizationB.
    + apply (proj1 Hsystems). exact HsystemsB.
    + apply (proj1 Hcontract). exact HcontractB.
    + apply (proj1 Hprofile). exact HprofileB.
    + apply (proj1 HrecomputedSystems). exact HrecomputedSystemsB.
    + apply (proj1 HrecomputedFinal). exact HrecomputedFinalB.
    + apply (proj1 HstoredSystems). exact HstoredSystemsB.
    + apply (proj1 HstoredFinal). exact HstoredFinalB.
  - intros Hvalid.
    unfold StageClosureIdentityValid in Hvalid.
    destruct Hvalid as
      [HsubjectP [HinstanceP [HrealizationP [HsystemsP [HcontractP
       [HprofileP [HrecomputedSystemsP [HrecomputedFinalP
       [HstoredSystemsP HstoredFinalP]]]]]]]]].
    repeat split.
    + apply (proj2 Hsubject). exact HsubjectP.
    + apply (proj2 Hinstance). exact HinstanceP.
    + apply (proj2 Hrealization). exact HrealizationP.
    + apply (proj2 Hsystems). exact HsystemsP.
    + apply (proj2 Hcontract). exact HcontractP.
    + apply (proj2 Hprofile). exact HprofileP.
    + apply (proj2 HrecomputedSystems). exact HrecomputedSystemsP.
    + apply (proj2 HrecomputedFinal). exact HrecomputedFinalP.
    + apply (proj2 HstoredSystems). exact HstoredSystemsP.
    + apply (proj2 HstoredFinal). exact HstoredFinalP.
Qed.

Inductive SystemsStageClosureDecision : Type :=
| SystemsStageClosureAcceptedDecision
| SystemsStageClosureFactDecision
| SystemsStageClosureProjectionDecision
| SystemsStageClosureSourceDecision
| SystemsStageClosureTargetDecision
| SystemsStageClosureScopeDecision
| SystemsStageClosureIdentityDecision.

Definition decideSystemsStageClosureByFacts
  (factVerificationAccepted factProjectionExact sourceClosureAccepted
   targetClosureAccepted scopeMatchesAccepted finalIdentityAccepted : bool)
  : SystemsStageClosureDecision :=
  if factVerificationAccepted then
    if factProjectionExact then
      if sourceClosureAccepted then
        if targetClosureAccepted then
          if scopeMatchesAccepted then
            if finalIdentityAccepted
            then SystemsStageClosureAcceptedDecision
            else SystemsStageClosureIdentityDecision
          else SystemsStageClosureScopeDecision
        else SystemsStageClosureTargetDecision
      else SystemsStageClosureSourceDecision
    else SystemsStageClosureProjectionDecision
  else SystemsStageClosureFactDecision.

Theorem systems_stage_closure_decision_exact :
  forall factVerificationAccepted factProjectionExact sourceClosureAccepted
         targetClosureAccepted scopeMatchesAccepted finalIdentityAccepted,
    decideSystemsStageClosureByFacts
      factVerificationAccepted factProjectionExact sourceClosureAccepted
      targetClosureAccepted scopeMatchesAccepted finalIdentityAccepted =
      SystemsStageClosureAcceptedDecision <->
    factVerificationAccepted = true /\
    factProjectionExact = true /\
    sourceClosureAccepted = true /\
    targetClosureAccepted = true /\
    scopeMatchesAccepted = true /\
    finalIdentityAccepted = true.
Proof.
  intros factVerificationAccepted factProjectionExact sourceClosureAccepted
    targetClosureAccepted scopeMatchesAccepted finalIdentityAccepted.
  unfold decideSystemsStageClosureByFacts.
  destruct factVerificationAccepted;
  destruct factProjectionExact;
  destruct sourceClosureAccepted;
  destruct targetClosureAccepted;
  destruct scopeMatchesAccepted;
  destruct finalIdentityAccepted;
  simpl; intuition discriminate.
Qed.

Theorem systems_stage_closure_decision_corresponds_certified_relation :
  forall factModel live mechanisms dispositions kinds justifications
         scope effective identity
         factVerificationAccepted factProjectionExact sourceClosureAccepted
         targetClosureAccepted scopeMatchesAccepted finalIdentityAccepted,
    (factVerificationAccepted = true <->
      StageFactVerificationSuccess factModel) ->
    (factProjectionExact = true <->
      FactProjectionExact live factModel) ->
    (sourceClosureAccepted = true <->
      SourceClosureVerified live mechanisms dispositions) ->
    (targetClosureAccepted = true <->
      TargetClosureVerified live mechanisms kinds justifications) ->
    (scopeMatchesAccepted = true <->
      ScopeMatches scope effective) ->
    (finalIdentityAccepted = true <->
      StageClosureIdentityValid identity) ->
    decideSystemsStageClosureByFacts
      factVerificationAccepted factProjectionExact sourceClosureAccepted
      targetClosureAccepted scopeMatchesAccepted finalIdentityAccepted =
      SystemsStageClosureAcceptedDecision <->
    SystemsStageClosurePreserved
      factModel live mechanisms dispositions kinds justifications
      scope effective identity.
Proof.
  intros factModel live mechanisms dispositions kinds justifications
    scope effective identity
    factVerificationAccepted factProjectionExact sourceClosureAccepted
    targetClosureAccepted scopeMatchesAccepted finalIdentityAccepted
    Hfacts Hprojection Hsource Htarget Hscope Hidentity.
  rewrite systems_stage_closure_decision_exact.
  split.
  - intros [HfactsB [HprojectionB [HsourceB [HtargetB [HscopeB HidentityB]]]]].
    constructor.
    + apply (proj1 Hfacts). exact HfactsB.
    + apply (proj1 Hprojection). exact HprojectionB.
    + apply (proj1 Hsource). exact HsourceB.
    + apply (proj1 Htarget). exact HtargetB.
    + apply (proj1 Hscope). exact HscopeB.
    + apply (proj1 Hidentity). exact HidentityB.
  - intros Hpreserved.
    destruct Hpreserved as
      [HfactsP HprojectionP HsourceP HtargetP HscopeP HidentityP].
    repeat split.
    + apply (proj2 Hfacts). exact HfactsP.
    + apply (proj2 Hprojection). exact HprojectionP.
    + apply (proj2 Hsource). exact HsourceP.
    + apply (proj2 Htarget). exact HtargetP.
    + apply (proj2 Hscope). exact HscopeP.
    + apply (proj2 Hidentity). exact HidentityP.
Qed.
