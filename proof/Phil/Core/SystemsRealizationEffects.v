From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import SystemsStageClosure.

(*
  PHIL-SYS-REALIZE-001 — target strengthening, target-inserted staging,
  and next-stage competence-boundary export.

  This normalized semantic model composes the already Certified
  PHIL-SYS-STAGE-CLOSURE-001 final StageContract identity closure with the
  implemented SYS-014, SYS-017, and SYS-019 relations.

  Concrete Haskell Text/Map/Set/list enumeration, canonical SemanticForm
  rendering, target/profile-specific facts, and implementation equivalence
  remain explicit correspondence boundaries.
*)

(* -------------------------------------------------------------------------- *)
(* SYS-014 — stronger target facts require explicit realization obligations.  *)
(* -------------------------------------------------------------------------- *)

Definition RealizationFactId := nat.
Definition RealizationFactSet := RealizationFactId -> bool.

Inductive DerivedRealizationObligation : Type :=
| mkDerivedRealizationObligation :
    nat ->
    (RealizationFactId -> bool) ->
    (nat -> bool) ->
    bool ->
    bool ->
    DerivedRealizationObligation.

Inductive TargetStrengtheningFact : Type :=
| mkTargetStrengtheningFact :
    RealizationFactId ->
    bool ->
    bool ->
    option DerivedRealizationObligation ->
    TargetStrengtheningFact.

Definition StrengtheningEnvironment :=
  RealizationFactId -> option TargetStrengtheningFact.

Definition strengtheningIntroducer
  (fact : TargetStrengtheningFact) : RealizationFactId :=
  match fact with
  | mkTargetStrengtheningFact introducer _ _ _ => introducer
  end.

Definition strengtheningHasSourceAssurance
  (fact : TargetStrengtheningFact) : bool :=
  match fact with
  | mkTargetStrengtheningFact _ present _ _ => present
  end.

Definition strengtheningSourceAssuranceKnown
  (fact : TargetStrengtheningFact) : bool :=
  match fact with
  | mkTargetStrengtheningFact _ _ known _ => known
  end.

Definition strengtheningDerivedObligation
  (fact : TargetStrengtheningFact) : option DerivedRealizationObligation :=
  match fact with
  | mkTargetStrengtheningFact _ _ _ derived => derived
  end.

Definition derivedRealizationRevision
  (obligation : DerivedRealizationObligation) : nat :=
  match obligation with
  | mkDerivedRealizationObligation revision _ _ _ _ => revision
  end.

Definition derivedRealizationIntroducers
  (obligation : DerivedRealizationObligation) : RealizationFactId -> bool :=
  match obligation with
  | mkDerivedRealizationObligation _ introducers _ _ _ => introducers
  end.

Definition derivedRealizationSubjects
  (obligation : DerivedRealizationObligation) : nat -> bool :=
  match obligation with
  | mkDerivedRealizationObligation _ _ subjects _ _ => subjects
  end.

Definition derivedRealizationStatementPresent
  (obligation : DerivedRealizationObligation) : bool :=
  match obligation with
  | mkDerivedRealizationObligation _ _ _ statementPresent _ => statementPresent
  end.

Definition derivedRealizationAcceptancePresent
  (obligation : DerivedRealizationObligation) : bool :=
  match obligation with
  | mkDerivedRealizationObligation _ _ _ _ acceptancePresent => acceptancePresent
  end.

Definition DerivedRealizationObligationValid
  (introducer : RealizationFactId)
  (obligation : DerivedRealizationObligation) : Prop :=
  derivedRealizationRevision obligation <> 0 /\
  derivedRealizationIntroducers obligation introducer = true /\
  (forall other,
    derivedRealizationIntroducers obligation other = true ->
    other = introducer) /\
  (exists subject,
    derivedRealizationSubjects obligation subject = true) /\
  derivedRealizationStatementPresent obligation = true /\
  derivedRealizationAcceptancePresent obligation = true.

Definition TargetStrengtheningValid
  (fact : TargetStrengtheningFact) : Prop :=
  strengtheningIntroducer fact <> 0 /\
  (strengtheningHasSourceAssurance fact = true ->
    strengtheningSourceAssuranceKnown fact = true) /\
  (strengtheningHasSourceAssurance fact = false ->
    exists obligation,
      strengtheningDerivedObligation fact = Some obligation /\
      DerivedRealizationObligationValid
        (strengtheningIntroducer fact) obligation) /\
  (forall obligation,
    strengtheningDerivedObligation fact = Some obligation ->
    DerivedRealizationObligationValid
      (strengtheningIntroducer fact) obligation).

Definition ExactTargetStrengtheningCoverage
  (live : RealizationFactSet)
  (environment : StrengtheningEnvironment) : Prop :=
  forall factId,
    live factId = true <->
    exists fact, environment factId = Some fact.

Record TargetStrengtheningClosure
  (live : RealizationFactSet)
  (environment : StrengtheningEnvironment) : Prop :=
  mkTargetStrengtheningClosure {
    targetStrengtheningCoverageExact :
      ExactTargetStrengtheningCoverage live environment;
    targetStrengtheningFactsValid :
      forall factId fact,
        environment factId = Some fact ->
        TargetStrengtheningValid fact
  }.

Theorem stronger_target_fact_requires_derived_obligation :
  forall fact,
    TargetStrengtheningValid fact ->
    strengtheningHasSourceAssurance fact = false ->
    exists obligation,
      strengtheningDerivedObligation fact = Some obligation /\
      DerivedRealizationObligationValid
        (strengtheningIntroducer fact) obligation.
Proof.
  intros fact Hvalid Hsource.
  destruct Hvalid as [_ [_ [Hderived _]]].
  apply Hderived.
  exact Hsource.
Qed.

Theorem target_fact_cannot_relabel_unknown_assurance_as_source :
  forall fact,
    strengtheningHasSourceAssurance fact = true ->
    strengtheningSourceAssuranceKnown fact = false ->
    ~ TargetStrengtheningValid fact.
Proof.
  intros fact Hpresent Hunknown Hvalid.
  destruct Hvalid as [_ [Hknown _]].
  specialize (Hknown Hpresent).
  rewrite Hunknown in Hknown.
  discriminate.
Qed.

Theorem derived_obligation_retains_exact_introducer :
  forall fact obligation other,
    TargetStrengtheningValid fact ->
    strengtheningDerivedObligation fact = Some obligation ->
    derivedRealizationIntroducers obligation other = true ->
    other = strengtheningIntroducer fact.
Proof.
  intros fact obligation other Hvalid Hlookup Hintroducer.
  destruct Hvalid as [_ [_ [_ Hall]]].
  pose proof (Hall obligation Hlookup) as Hobligation.
  destruct Hobligation as [_ [_ [Hexact _]]].
  eapply Hexact.
  exact Hintroducer.
Qed.

(* -------------------------------------------------------------------------- *)
(* SYS-017 — target-inserted staging exposes every semantic consequence.       *)
(* -------------------------------------------------------------------------- *)

Inductive StagingFailureAccount : Type :=
| StagingExplicitInfallible
| StagingExplicitMayFail : (nat -> bool) -> StagingFailureAccount.

Definition StagingFailureAccountValid
  (failure : StagingFailureAccount) : Prop :=
  match failure with
  | StagingExplicitInfallible => True
  | StagingExplicitMayFail failures =>
      exists failureId, failures failureId = true
  end.

Record StagingEventFacts : Type := mkStagingEventFacts {
  stagingRequirementIdentity : nat;
  stagingEffectIdentity : nat;
  stagingAuthorityAccountIdentity : nat;
  stagingFailureAccount : StagingFailureAccount;
  stagingSubjectTransferRevision : nat;
  stagingCostIdentity : nat;
  stagingBytesCopiedAccounted : bool;
  stagingFrequencyAccounted : bool
}.

Definition StagingEventValid (event : StagingEventFacts) : Prop :=
  stagingRequirementIdentity event <> 0 /\
  stagingEffectIdentity event <> 0 /\
  stagingAuthorityAccountIdentity event <> 0 /\
  StagingFailureAccountValid (stagingFailureAccount event) /\
  stagingSubjectTransferRevision event <> 0 /\
  stagingCostIdentity event <> 0 /\
  stagingBytesCopiedAccounted event = true /\
  stagingFrequencyAccounted event = true.

Definition StagingRequirementSet := nat -> bool.
Definition StagingEventEnvironment := nat -> option StagingEventFacts.

Definition ExactStagingEventCoverage
  (live : StagingRequirementSet)
  (environment : StagingEventEnvironment) : Prop :=
  forall requirement,
    live requirement = true <->
    exists event, environment requirement = Some event.

Record StagingEffectClosure
  (live : StagingRequirementSet)
  (environment : StagingEventEnvironment) : Prop :=
  mkStagingEffectClosure {
    stagingEventCoverageExact : ExactStagingEventCoverage live environment;
    stagingEventsValid :
      forall requirement event,
        environment requirement = Some event ->
        StagingEventValid event
  }.

Theorem valid_staging_event_exposes_all_consequences :
  forall event,
    StagingEventValid event ->
    stagingEffectIdentity event <> 0 /\
    stagingAuthorityAccountIdentity event <> 0 /\
    StagingFailureAccountValid (stagingFailureAccount event) /\
    stagingSubjectTransferRevision event <> 0 /\
    stagingCostIdentity event <> 0 /\
    stagingBytesCopiedAccounted event = true /\
    stagingFrequencyAccounted event = true.
Proof.
  intros event Hvalid.
  destruct Hvalid as
    [_ [Heffect [Hauthority [Hfailure [Htransfer [Hcost [Hbytes Hfrequency]]]]]]].
  split.
  - exact Heffect.
  - split.
    + exact Hauthority.
    + split.
      * exact Hfailure.
      * split.
        -- exact Htransfer.
        -- split.
           ++ exact Hcost.
           ++ split.
              ** exact Hbytes.
              ** exact Hfrequency.
Qed.

Theorem every_live_staging_requirement_has_one_event :
  forall live environment requirement,
    StagingEffectClosure live environment ->
    live requirement = true ->
    exists event,
      environment requirement = Some event /\
      StagingEventValid event.
Proof.
  intros live environment requirement Hclosure Hlive.
  destruct Hclosure as [Hexact Hvalid].
  apply (proj1 (Hexact requirement)) in Hlive.
  destruct Hlive as [event Hlookup].
  exists event.
  split.
  - exact Hlookup.
  - eapply Hvalid.
    exact Hlookup.
Qed.

(* -------------------------------------------------------------------------- *)
(* SYS-019 — backend requirements cross the competence boundary explicitly.   *)
(* -------------------------------------------------------------------------- *)

Inductive NextStageBasis : Type :=
| NextStageTargetBasis : nat -> NextStageBasis
| NextStageRuntimeBasis : nat -> NextStageBasis.

Definition NextStageSourceRefs := nat -> bool.

Record NextStageRequirementFacts : Type := mkNextStageRequirementFacts {
  nextStageRequirementRevision : nat;
  nextStageSourceRefs : NextStageSourceRefs;
  nextStageRequiredFactIdentity : nat;
  nextStageFolkloreOnly : bool;
  nextStageAcceptanceRuleIdentity : nat;
  nextStageValidityScopeIdentity : nat
}.

Definition NextStageRequirementValid
  (requirement : NextStageRequirementFacts) : Prop :=
  nextStageRequirementRevision requirement <> 0 /\
  (exists sourceRef, nextStageSourceRefs requirement sourceRef = true) /\
  nextStageRequiredFactIdentity requirement <> 0 /\
  nextStageFolkloreOnly requirement = false /\
  nextStageAcceptanceRuleIdentity requirement <> 0 /\
  nextStageValidityScopeIdentity requirement <> 0.

Definition NextStageBasisSet := NextStageBasis -> bool.
Definition NextStageRequirementEnvironment :=
  NextStageBasis -> option NextStageRequirementFacts.

Definition ExactNextStageRequirementCoverage
  (live : NextStageBasisSet)
  (environment : NextStageRequirementEnvironment) : Prop :=
  forall basis,
    live basis = true <->
    exists requirement, environment basis = Some requirement.

Record NextStageRequirementClosure
  (live : NextStageBasisSet)
  (environment : NextStageRequirementEnvironment) : Prop :=
  mkNextStageRequirementClosure {
    nextStageRequirementCoverageExact :
      ExactNextStageRequirementCoverage live environment;
    nextStageRequirementsValid :
      forall basis requirement,
        environment basis = Some requirement ->
        NextStageRequirementValid requirement
  }.

Theorem every_live_next_stage_basis_has_exact_requirement :
  forall live environment basis,
    NextStageRequirementClosure live environment ->
    live basis = true ->
    exists requirement,
      environment basis = Some requirement /\
      NextStageRequirementValid requirement.
Proof.
  intros live environment basis Hclosure Hlive.
  destruct Hclosure as [Hexact Hvalid].
  apply (proj1 (Hexact basis)) in Hlive.
  destruct Hlive as [requirement Hlookup].
  exists requirement.
  split.
  - exact Hlookup.
  - eapply Hvalid.
    exact Hlookup.
Qed.

Theorem folklore_only_requirement_cannot_close :
  forall requirement,
    nextStageFolkloreOnly requirement = true ->
    ~ NextStageRequirementValid requirement.
Proof.
  intros requirement Hfolklore Hvalid.
  destruct Hvalid as [_ [_ [_ [Hexact _]]]].
  rewrite Hfolklore in Hexact.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cumulative PHIL-SYS-REALIZE-001 composition.                               *)
(* -------------------------------------------------------------------------- *)

Record SystemsRealizationEffectsPreserved
  (identity : StageClosureIdentityFacts)
  (liveStrengthenings : RealizationFactSet)
  (strengthenings : StrengtheningEnvironment)
  (liveStaging : StagingRequirementSet)
  (staging : StagingEventEnvironment)
  (liveNextStage : NextStageBasisSet)
  (nextStage : NextStageRequirementEnvironment) : Prop :=
  mkSystemsRealizationEffectsPreserved {
    realizationBaseStageClosure : StageClosureIdentityValid identity;
    realizationTargetStrengtheningClosure :
      TargetStrengtheningClosure liveStrengthenings strengthenings;
    realizationStagingEffectClosure :
      StagingEffectClosure liveStaging staging;
    realizationNextStageRequirementClosure :
      NextStageRequirementClosure liveNextStage nextStage
  }.

Theorem systems_realization_effects_are_explicit :
  forall identity liveStrengthenings strengthenings liveStaging staging
         liveNextStage nextStage,
    SystemsRealizationEffectsPreserved
      identity liveStrengthenings strengthenings liveStaging staging
      liveNextStage nextStage ->
    StageClosureIdentityValid identity /\
    ExactTargetStrengtheningCoverage liveStrengthenings strengthenings /\
    ExactStagingEventCoverage liveStaging staging /\
    ExactNextStageRequirementCoverage liveNextStage nextStage.
Proof.
  intros identity liveStrengthenings strengthenings liveStaging staging
    liveNextStage nextStage Hpreserved.
  destruct Hpreserved as [Hstage Hstrengthening Hstaging Hnext].
  destruct Hstrengthening as [HstrengtheningExact _].
  destruct Hstaging as [HstagingExact _].
  destruct Hnext as [HnextExact _].
  split.
  - exact Hstage.
  - split.
    + exact HstrengtheningExact.
    + split.
      * exact HstagingExact.
      * exact HnextExact.
Qed.
