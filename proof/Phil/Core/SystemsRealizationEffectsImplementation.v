From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import SystemsStageClosure.
From Phil.Core Require Import SystemsRealizationEffects.

(*
  Mechanical implementation-refinement surface for already-Certified
  PHIL-SYS-REALIZE-001. The extracted classifiers own only the normalized
  semantic gate order. Concrete Haskell representation, enumeration, and
  diagnostic payload recovery remain explicit correspondence boundaries.
*)

Inductive TargetStrengtheningDecision : Type :=
| TargetStrengtheningAcceptedDecision
| TargetStrengtheningCoverageDecision
| TargetStrengtheningIntroducerDecision
| TargetStrengtheningSourceAssuranceDecision
| TargetStrengtheningDerivedRequiredDecision
| TargetStrengtheningDerivedRevisionDecision
| TargetStrengtheningDerivedIntroducerDecision
| TargetStrengtheningDerivedSubjectDecision
| TargetStrengtheningDerivedStatementDecision
| TargetStrengtheningDerivedAcceptanceDecision.

Definition decideTargetStrengtheningByFacts
  (coverageExact introducerPresent sourceAssuranceValid
   derivedRequirementSatisfied derivedRevisionPresent derivedIntroducerExact
   derivedSubjectPresent derivedStatementPresent derivedAcceptancePresent : bool)
  : TargetStrengtheningDecision :=
  if coverageExact then
    if introducerPresent then
      if sourceAssuranceValid then
        if derivedRequirementSatisfied then
          if derivedRevisionPresent then
            if derivedIntroducerExact then
              if derivedSubjectPresent then
                if derivedStatementPresent then
                  if derivedAcceptancePresent then TargetStrengtheningAcceptedDecision
                  else TargetStrengtheningDerivedAcceptanceDecision
                else TargetStrengtheningDerivedStatementDecision
              else TargetStrengtheningDerivedSubjectDecision
            else TargetStrengtheningDerivedIntroducerDecision
          else TargetStrengtheningDerivedRevisionDecision
        else TargetStrengtheningDerivedRequiredDecision
      else TargetStrengtheningSourceAssuranceDecision
    else TargetStrengtheningIntroducerDecision
  else TargetStrengtheningCoverageDecision.

Theorem target_strengthening_accepted_facts :
  forall coverageExact introducerPresent sourceAssuranceValid
         derivedRequirementSatisfied derivedRevisionPresent
         derivedIntroducerExact derivedSubjectPresent derivedStatementPresent
         derivedAcceptancePresent,
    decideTargetStrengtheningByFacts
      coverageExact introducerPresent sourceAssuranceValid
      derivedRequirementSatisfied derivedRevisionPresent
      derivedIntroducerExact derivedSubjectPresent derivedStatementPresent
      derivedAcceptancePresent = TargetStrengtheningAcceptedDecision ->
    coverageExact = true /\ introducerPresent = true /\
    sourceAssuranceValid = true /\ derivedRequirementSatisfied = true /\
    derivedRevisionPresent = true /\ derivedIntroducerExact = true /\
    derivedSubjectPresent = true /\ derivedStatementPresent = true /\
    derivedAcceptancePresent = true.
Proof.
  intros coverageExact introducerPresent sourceAssuranceValid
    derivedRequirementSatisfied derivedRevisionPresent derivedIntroducerExact
    derivedSubjectPresent derivedStatementPresent derivedAcceptancePresent H.
  unfold decideTargetStrengtheningByFacts in H.
  destruct coverageExact eqn:Hcoverage; try discriminate.
  destruct introducerPresent eqn:Hintroducer; try discriminate.
  destruct sourceAssuranceValid eqn:Hsource; try discriminate.
  destruct derivedRequirementSatisfied eqn:Hrequired; try discriminate.
  destruct derivedRevisionPresent eqn:Hrevision; try discriminate.
  destruct derivedIntroducerExact eqn:HderivedIntroducer; try discriminate.
  destruct derivedSubjectPresent eqn:Hsubject; try discriminate.
  destruct derivedStatementPresent eqn:Hstatement; try discriminate.
  destruct derivedAcceptancePresent eqn:Hacceptance; try discriminate.
  inversion H. repeat split; assumption.
Qed.

Theorem target_strengthening_decision_reflects_closure :
  forall live environment coverageExact introducerPresent sourceAssuranceValid
         derivedRequirementSatisfied derivedRevisionPresent
         derivedIntroducerExact derivedSubjectPresent derivedStatementPresent
         derivedAcceptancePresent,
    (coverageExact = true -> ExactTargetStrengtheningCoverage live environment) ->
    (introducerPresent = true -> sourceAssuranceValid = true ->
      derivedRequirementSatisfied = true -> derivedRevisionPresent = true ->
      derivedIntroducerExact = true -> derivedSubjectPresent = true ->
      derivedStatementPresent = true -> derivedAcceptancePresent = true ->
      forall factId fact,
        environment factId = Some fact -> TargetStrengtheningValid fact) ->
    decideTargetStrengtheningByFacts
      coverageExact introducerPresent sourceAssuranceValid
      derivedRequirementSatisfied derivedRevisionPresent
      derivedIntroducerExact derivedSubjectPresent derivedStatementPresent
      derivedAcceptancePresent = TargetStrengtheningAcceptedDecision ->
    TargetStrengtheningClosure live environment.
Proof.
  intros live environment coverageExact introducerPresent sourceAssuranceValid
    derivedRequirementSatisfied derivedRevisionPresent derivedIntroducerExact
    derivedSubjectPresent derivedStatementPresent derivedAcceptancePresent
    Hcoverage Hfacts Haccepted.
  pose proof (target_strengthening_accepted_facts _ _ _ _ _ _ _ _ _ Haccepted)
    as [Hcoverage' [Hintroducer [Hsource [Hrequired [Hrevision
      [HderivedIntroducer [Hsubject [Hstatement Hacceptance]]]]]]]].
  constructor.
  - apply Hcoverage. exact Hcoverage'.
  - intros factId fact Hlookup. eapply Hfacts; eauto.
Qed.

Inductive StagingEffectDecision : Type :=
| StagingEffectAcceptedDecision
| StagingEffectCoverageDecision
| StagingEffectRequirementDecision
| StagingEffectEffectDecision
| StagingEffectAuthorityDecision
| StagingEffectFailureDecision
| StagingEffectTransferDecision
| StagingEffectCostDecision
| StagingEffectBytesDecision
| StagingEffectFrequencyDecision.

Definition decideStagingEffectByFacts
  (coverageExact requirementIdentityPresent effectIdentityPresent
   authorityAccountPresent failureAccountValid subjectTransferPresent
   costIdentityPresent bytesCopiedAccounted frequencyAccounted : bool)
  : StagingEffectDecision :=
  if coverageExact then
    if requirementIdentityPresent then
      if effectIdentityPresent then
        if authorityAccountPresent then
          if failureAccountValid then
            if subjectTransferPresent then
              if costIdentityPresent then
                if bytesCopiedAccounted then
                  if frequencyAccounted then StagingEffectAcceptedDecision
                  else StagingEffectFrequencyDecision
                else StagingEffectBytesDecision
              else StagingEffectCostDecision
            else StagingEffectTransferDecision
          else StagingEffectFailureDecision
        else StagingEffectAuthorityDecision
      else StagingEffectEffectDecision
    else StagingEffectRequirementDecision
  else StagingEffectCoverageDecision.

Theorem staging_effect_accepted_facts :
  forall coverageExact requirementIdentityPresent effectIdentityPresent
         authorityAccountPresent failureAccountValid subjectTransferPresent
         costIdentityPresent bytesCopiedAccounted frequencyAccounted,
    decideStagingEffectByFacts
      coverageExact requirementIdentityPresent effectIdentityPresent
      authorityAccountPresent failureAccountValid subjectTransferPresent
      costIdentityPresent bytesCopiedAccounted frequencyAccounted =
      StagingEffectAcceptedDecision ->
    coverageExact = true /\ requirementIdentityPresent = true /\
    effectIdentityPresent = true /\ authorityAccountPresent = true /\
    failureAccountValid = true /\ subjectTransferPresent = true /\
    costIdentityPresent = true /\ bytesCopiedAccounted = true /\
    frequencyAccounted = true.
Proof.
  intros coverageExact requirementIdentityPresent effectIdentityPresent
    authorityAccountPresent failureAccountValid subjectTransferPresent
    costIdentityPresent bytesCopiedAccounted frequencyAccounted H.
  unfold decideStagingEffectByFacts in H.
  destruct coverageExact eqn:Hcoverage; try discriminate.
  destruct requirementIdentityPresent eqn:Hrequirement; try discriminate.
  destruct effectIdentityPresent eqn:Heffect; try discriminate.
  destruct authorityAccountPresent eqn:Hauthority; try discriminate.
  destruct failureAccountValid eqn:Hfailure; try discriminate.
  destruct subjectTransferPresent eqn:Htransfer; try discriminate.
  destruct costIdentityPresent eqn:Hcost; try discriminate.
  destruct bytesCopiedAccounted eqn:Hbytes; try discriminate.
  destruct frequencyAccounted eqn:Hfrequency; try discriminate.
  inversion H. repeat split; assumption.
Qed.

Theorem staging_effect_decision_reflects_closure :
  forall live environment coverageExact requirementIdentityPresent
         effectIdentityPresent authorityAccountPresent failureAccountValid
         subjectTransferPresent costIdentityPresent bytesCopiedAccounted
         frequencyAccounted,
    (coverageExact = true -> ExactStagingEventCoverage live environment) ->
    (requirementIdentityPresent = true -> effectIdentityPresent = true ->
      authorityAccountPresent = true -> failureAccountValid = true ->
      subjectTransferPresent = true -> costIdentityPresent = true ->
      bytesCopiedAccounted = true -> frequencyAccounted = true ->
      forall requirement event,
        environment requirement = Some event -> StagingEventValid event) ->
    decideStagingEffectByFacts
      coverageExact requirementIdentityPresent effectIdentityPresent
      authorityAccountPresent failureAccountValid subjectTransferPresent
      costIdentityPresent bytesCopiedAccounted frequencyAccounted =
      StagingEffectAcceptedDecision -> StagingEffectClosure live environment.
Proof.
  intros live environment coverageExact requirementIdentityPresent
    effectIdentityPresent authorityAccountPresent failureAccountValid
    subjectTransferPresent costIdentityPresent bytesCopiedAccounted
    frequencyAccounted Hcoverage Hevents Haccepted.
  pose proof (staging_effect_accepted_facts _ _ _ _ _ _ _ _ _ Haccepted)
    as [Hcoverage' [Hrequirement [Heffect [Hauthority [Hfailure
      [Htransfer [Hcost [Hbytes Hfrequency]]]]]]]].
  constructor.
  - apply Hcoverage. exact Hcoverage'.
  - intros requirement event Hlookup. eapply Hevents; eauto.
Qed.

Inductive NextStageExportDecision : Type :=
| NextStageExportAcceptedDecision
| NextStageExportCoverageDecision
| NextStageExportRevisionDecision
| NextStageExportSourceDecision
| NextStageExportFactDecision
| NextStageExportFolkloreDecision
| NextStageExportAcceptanceDecision
| NextStageExportScopeDecision.

Definition decideNextStageExportByFacts
  (coverageExact revisionPresent sourceRefsPresent requiredFactPresent
   notFolkloreOnly acceptanceRulePresent validityScopePresent : bool)
  : NextStageExportDecision :=
  if coverageExact then
    if revisionPresent then
      if sourceRefsPresent then
        if requiredFactPresent then
          if notFolkloreOnly then
            if acceptanceRulePresent then
              if validityScopePresent then NextStageExportAcceptedDecision
              else NextStageExportScopeDecision
            else NextStageExportAcceptanceDecision
          else NextStageExportFolkloreDecision
        else NextStageExportFactDecision
      else NextStageExportSourceDecision
    else NextStageExportRevisionDecision
  else NextStageExportCoverageDecision.

Theorem next_stage_export_accepted_facts :
  forall coverageExact revisionPresent sourceRefsPresent requiredFactPresent
         notFolkloreOnly acceptanceRulePresent validityScopePresent,
    decideNextStageExportByFacts
      coverageExact revisionPresent sourceRefsPresent requiredFactPresent
      notFolkloreOnly acceptanceRulePresent validityScopePresent =
      NextStageExportAcceptedDecision ->
    coverageExact = true /\ revisionPresent = true /\ sourceRefsPresent = true /\
    requiredFactPresent = true /\ notFolkloreOnly = true /\
    acceptanceRulePresent = true /\ validityScopePresent = true.
Proof.
  intros coverageExact revisionPresent sourceRefsPresent requiredFactPresent
    notFolkloreOnly acceptanceRulePresent validityScopePresent H.
  unfold decideNextStageExportByFacts in H.
  destruct coverageExact eqn:Hcoverage; try discriminate.
  destruct revisionPresent eqn:Hrevision; try discriminate.
  destruct sourceRefsPresent eqn:Hsource; try discriminate.
  destruct requiredFactPresent eqn:Hfact; try discriminate.
  destruct notFolkloreOnly eqn:Hfolklore; try discriminate.
  destruct acceptanceRulePresent eqn:Hacceptance; try discriminate.
  destruct validityScopePresent eqn:Hscope; try discriminate.
  inversion H. repeat split; assumption.
Qed.

Theorem next_stage_export_decision_reflects_closure :
  forall live environment coverageExact revisionPresent sourceRefsPresent
         requiredFactPresent notFolkloreOnly acceptanceRulePresent
         validityScopePresent,
    (coverageExact = true -> ExactNextStageRequirementCoverage live environment) ->
    (revisionPresent = true -> sourceRefsPresent = true ->
      requiredFactPresent = true -> notFolkloreOnly = true ->
      acceptanceRulePresent = true -> validityScopePresent = true ->
      forall basis requirement,
        environment basis = Some requirement -> NextStageRequirementValid requirement) ->
    decideNextStageExportByFacts
      coverageExact revisionPresent sourceRefsPresent requiredFactPresent
      notFolkloreOnly acceptanceRulePresent validityScopePresent =
      NextStageExportAcceptedDecision -> NextStageRequirementClosure live environment.
Proof.
  intros live environment coverageExact revisionPresent sourceRefsPresent
    requiredFactPresent notFolkloreOnly acceptanceRulePresent validityScopePresent
    Hcoverage Hrequirements Haccepted.
  pose proof (next_stage_export_accepted_facts _ _ _ _ _ _ _ Haccepted)
    as [Hcoverage' [Hrevision [Hsource [Hfact [Hfolklore
      [Hacceptance Hscope]]]]]].
  constructor.
  - apply Hcoverage. exact Hcoverage'.
  - intros basis requirement Hlookup. eapply Hrequirements; eauto.
Qed.

Inductive SystemsRealizationEffectsDecision : Type :=
| SystemsRealizationEffectsAcceptedDecision
| SystemsRealizationEffectsStageClosureDecision
| SystemsRealizationEffectsStrengtheningDecision
| SystemsRealizationEffectsStagingDecision
| SystemsRealizationEffectsNextStageDecision.

Definition decideSystemsRealizationEffectsByFacts
  (stageClosureAccepted strengtheningAccepted stagingAccepted nextStageAccepted : bool)
  : SystemsRealizationEffectsDecision :=
  if stageClosureAccepted then
    if strengtheningAccepted then
      if stagingAccepted then
        if nextStageAccepted then SystemsRealizationEffectsAcceptedDecision
        else SystemsRealizationEffectsNextStageDecision
      else SystemsRealizationEffectsStagingDecision
    else SystemsRealizationEffectsStrengtheningDecision
  else SystemsRealizationEffectsStageClosureDecision.

Theorem systems_realization_effects_accepted_facts :
  forall stageClosureAccepted strengtheningAccepted stagingAccepted nextStageAccepted,
    decideSystemsRealizationEffectsByFacts
      stageClosureAccepted strengtheningAccepted stagingAccepted nextStageAccepted =
      SystemsRealizationEffectsAcceptedDecision ->
    stageClosureAccepted = true /\ strengtheningAccepted = true /\
    stagingAccepted = true /\ nextStageAccepted = true.
Proof.
  intros stageClosureAccepted strengtheningAccepted stagingAccepted nextStageAccepted H.
  unfold decideSystemsRealizationEffectsByFacts in H.
  destruct stageClosureAccepted eqn:Hstage; try discriminate.
  destruct strengtheningAccepted eqn:Hstrengthening; try discriminate.
  destruct stagingAccepted eqn:Hstaging; try discriminate.
  destruct nextStageAccepted eqn:Hnext; try discriminate.
  inversion H. repeat split; assumption.
Qed.

Theorem systems_realization_effects_decision_reflects_preservation :
  forall identity liveStrengthenings strengthenings liveStaging staging
         liveNextStage nextStage stageClosureAccepted strengtheningAccepted
         stagingAccepted nextStageAccepted,
    (stageClosureAccepted = true -> StageClosureIdentityValid identity) ->
    (strengtheningAccepted = true ->
      TargetStrengtheningClosure liveStrengthenings strengthenings) ->
    (stagingAccepted = true -> StagingEffectClosure liveStaging staging) ->
    (nextStageAccepted = true ->
      NextStageRequirementClosure liveNextStage nextStage) ->
    decideSystemsRealizationEffectsByFacts
      stageClosureAccepted strengtheningAccepted stagingAccepted nextStageAccepted =
      SystemsRealizationEffectsAcceptedDecision ->
    SystemsRealizationEffectsPreserved
      identity liveStrengthenings strengthenings liveStaging staging
      liveNextStage nextStage.
Proof.
  intros identity liveStrengthenings strengthenings liveStaging staging
    liveNextStage nextStage stageClosureAccepted strengtheningAccepted
    stagingAccepted nextStageAccepted Hstage Hstrengthening Hstaging Hnext Haccepted.
  pose proof (systems_realization_effects_accepted_facts _ _ _ _ Haccepted)
    as [Hstage' [Hstrengthening' [Hstaging' Hnext']]].
  constructor.
  - apply Hstage. exact Hstage'.
  - apply Hstrengthening. exact Hstrengthening'.
  - apply Hstaging. exact Hstaging'.
  - apply Hnext. exact Hnext'.
Qed.
