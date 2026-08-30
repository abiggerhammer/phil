From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Assurance Require Import ValidityScope.
From Phil.Systems Require Import FactDisposition.

(*
  PHIL-SYS-STAGE-CLOSURE-001 — generalized source-disposition,
  target-justification, and final StageContract closure.

  This is a normalized semantic model of the already implemented SYS-002/003
  coarse closure envelope plus SYS-020 final deterministic closure. It composes
  the already Certified PHIL-SYS-FACT-001 exact fact-disposition theorem and
  PHIL-ASSURE-VALIDITY-001 scope semantics.

  Concrete Haskell Text/Map/Set/list enumeration, extraction of source
  responsibilities and target mechanisms, canonical SemanticForm rendering,
  digest construction, witness-specific concrete-trunk selection, diagnostic
  ordering, and Haskell implementation equivalence remain explicit
  correspondence boundaries.
*)

(* -------------------------------------------------------------------------- *)
(* Generalized source responsibility closure.                                 *)
(* -------------------------------------------------------------------------- *)

Inductive SourceResponsibility : Type :=
| SourceFactResponsibility : FactId -> SourceResponsibility
| SourceEdgeResponsibility : nat -> SourceResponsibility
| SourceObligationResponsibility : nat -> SourceResponsibility.

Definition SourceResponsibilitySet := SourceResponsibility -> bool.
Definition TargetMechanismId := nat.
Definition TargetMechanismSet := TargetMechanismId -> bool.
Definition MechanismRefs := TargetMechanismId -> bool.

Inductive ClosureDisposition : Type :=
| ClosureRealized : MechanismRefs -> ClosureDisposition
| ClosurePreserved : MechanismRefs -> ClosureDisposition
| ClosureExported : nat -> ClosureDisposition
| ClosureAssumptionDependent : nat -> ClosureDisposition -> ClosureDisposition.

Definition SourceDispositionEnvironment :=
  SourceResponsibility -> option ClosureDisposition.

Fixpoint ClosureDispositionValid
  (mechanisms : TargetMechanismSet)
  (disposition : ClosureDisposition) : Prop :=
  match disposition with
  | ClosureRealized refs =>
      forall mechanism, refs mechanism = true -> mechanisms mechanism = true
  | ClosurePreserved refs =>
      forall mechanism, refs mechanism = true -> mechanisms mechanism = true
  | ClosureExported nextStageRevision =>
      nextStageRevision <> 0
  | ClosureAssumptionDependent assumption inner =>
      assumption <> 0 /\ ClosureDispositionValid mechanisms inner
  end.

Definition ExactSourceDispositionCoverage
  (live : SourceResponsibilitySet)
  (dispositions : SourceDispositionEnvironment) : Prop :=
  forall responsibility,
    live responsibility = true <->
    exists disposition, dispositions responsibility = Some disposition.

Record SourceClosureVerified
  (live : SourceResponsibilitySet)
  (mechanisms : TargetMechanismSet)
  (dispositions : SourceDispositionEnvironment) : Prop :=
  mkSourceClosureVerified {
    sourceClosureCoverageExact :
      ExactSourceDispositionCoverage live dispositions;
    sourceClosureNoEmptyFactResponsibility :
      live (SourceFactResponsibility 0) = false;
    sourceClosureDispositionsPermitted :
      forall responsibility disposition,
        dispositions responsibility = Some disposition ->
        ClosureDispositionValid mechanisms disposition
  }.

Theorem every_live_source_responsibility_has_one_disposition :
  forall live mechanisms dispositions responsibility,
    SourceClosureVerified live mechanisms dispositions ->
    live responsibility = true ->
    exists disposition,
      dispositions responsibility = Some disposition.
Proof.
  intros live mechanisms dispositions responsibility Hverified Hlive.
  destruct Hverified as [Hexact _ _].
  apply (proj1 (Hexact responsibility)).
  exact Hlive.
Qed.

Theorem normalized_source_disposition_is_unique :
  forall (dispositions : SourceDispositionEnvironment)
         (responsibility : SourceResponsibility)
         (first second : ClosureDisposition),
    dispositions responsibility = Some first ->
    dispositions responsibility = Some second ->
    first = second.
Proof.
  intros dispositions responsibility first second Hfirst Hsecond.
  rewrite Hfirst in Hsecond.
  inversion Hsecond.
  reflexivity.
Qed.

Theorem source_disposition_cannot_name_unknown_mechanism :
  forall live mechanisms dispositions responsibility refs mechanism,
    SourceClosureVerified live mechanisms dispositions ->
    dispositions responsibility = Some (ClosureRealized refs) ->
    refs mechanism = true ->
    mechanisms mechanism = true.
Proof.
  intros live mechanisms dispositions responsibility refs mechanism
    Hverified Hlookup Href.
  destruct Hverified as [_ _ Hvalid].
  pose proof
    (Hvalid responsibility (ClosureRealized refs) Hlookup)
    as Hdisposition.
  simpl in Hdisposition.
  eapply Hdisposition.
  exact Href.
Qed.

Theorem empty_assumption_dependency_cannot_close_source :
  forall live mechanisms dispositions responsibility inner,
    dispositions responsibility = Some
      (ClosureAssumptionDependent 0 inner) ->
    ~ SourceClosureVerified live mechanisms dispositions.
Proof.
  intros live mechanisms dispositions responsibility inner Hlookup Hverified.
  destruct Hverified as [_ _ Hvalid].
  pose proof
    (Hvalid responsibility (ClosureAssumptionDependent 0 inner) Hlookup)
    as Hdisposition.
  simpl in Hdisposition.
  destruct Hdisposition as [Hnonzero _].
  apply Hnonzero.
  reflexivity.
Qed.

(* The generalized responsibility map projects exact source facts to the
   already Certified PHIL-SYS-FACT-001 model. Edges and obligations remain
   explicit responsibilities in the generalized map; concrete Haskell
   enumeration of those categories is a correspondence boundary. *)
Definition FactProjectionExact
  (live : SourceResponsibilitySet)
  (factModel : StageFactModel) : Prop :=
  forall fact,
    live (SourceFactResponsibility fact) = trustedFacts factModel fact.

Theorem live_source_fact_inherits_certified_fact_disposition :
  forall live factModel fact,
    StageFactVerificationSuccess factModel ->
    FactProjectionExact live factModel ->
    live (SourceFactResponsibility fact) = true ->
    exists record,
      stageFacts factModel fact = Some record /\
      FactDispositionValid factModel fact record.
Proof.
  intros live factModel fact Hfacts Hprojection Hlive.
  destruct Hfacts as [Hexact [_ Hvalid]].
  rewrite (Hprojection fact) in Hlive.
  apply (proj1 (Hexact fact)) in Hlive.
  destruct Hlive as [record Hlookup].
  exists record.
  split.
  - exact Hlookup.
  - eapply Hvalid.
    exact Hlookup.
Qed.

(* -------------------------------------------------------------------------- *)
(* Exact reverse justification for target mechanisms.                         *)
(* -------------------------------------------------------------------------- *)

Inductive TargetMechanismKind : Type :=
| TargetOperationMechanism
| TargetRuntimeSiteMechanism
| TargetOwnershipTransferMechanism
| TargetCarrierMechanism
| TargetCostMechanism.

Definition SourceReasonRefs := SourceResponsibility -> bool.

Record TargetJustification : Type := mkTargetJustification {
  closureSourceReasonRefs : SourceReasonRefs;
  closureRealizationReason : bool;
  closureQualificationReason : bool;
  closureDerivedObligationReason : bool
}.

Definition TargetMechanismKindEnvironment :=
  TargetMechanismId -> option TargetMechanismKind.
Definition TargetJustificationEnvironment :=
  TargetMechanismId -> option TargetJustification.

Definition HasTargetReason (justification : TargetJustification) : Prop :=
  (exists responsibility,
    closureSourceReasonRefs justification responsibility = true) \/
  closureRealizationReason justification = true \/
  closureQualificationReason justification = true \/
  closureDerivedObligationReason justification = true.

Definition TargetJustificationValid
  (live : SourceResponsibilitySet)
  (justification : TargetJustification) : Prop :=
  (forall responsibility,
    closureSourceReasonRefs justification responsibility = true ->
    live responsibility = true) /\
  HasTargetReason justification.

Definition ExactTargetMechanismCoverage
  (mechanisms : TargetMechanismSet)
  (kinds : TargetMechanismKindEnvironment)
  (justifications : TargetJustificationEnvironment) : Prop :=
  forall mechanism,
    mechanisms mechanism = true <->
    exists kind justification,
      kinds mechanism = Some kind /\
      justifications mechanism = Some justification.

Record TargetClosureVerified
  (live : SourceResponsibilitySet)
  (mechanisms : TargetMechanismSet)
  (kinds : TargetMechanismKindEnvironment)
  (justifications : TargetJustificationEnvironment) : Prop :=
  mkTargetClosureVerified {
    targetClosureCoverageExact :
      ExactTargetMechanismCoverage mechanisms kinds justifications;
    targetClosureNoEmptyMechanismIdentity :
      mechanisms 0 = false;
    targetClosureJustificationsValid :
      forall mechanism justification,
        justifications mechanism = Some justification ->
        TargetJustificationValid live justification
  }.

Theorem every_live_target_mechanism_has_exact_justification :
  forall live mechanisms kinds justifications mechanism,
    TargetClosureVerified live mechanisms kinds justifications ->
    mechanisms mechanism = true ->
    exists kind justification,
      kinds mechanism = Some kind /\
      justifications mechanism = Some justification /\
      TargetJustificationValid live justification.
Proof.
  intros live mechanisms kinds justifications mechanism Hverified Hlive.
  destruct Hverified as [Hexact _ Hvalid].
  apply (proj1 (Hexact mechanism)) in Hlive.
  destruct Hlive as [kind [justification [Hkind Hjustification]]].
  exists kind, justification.
  split.
  - exact Hkind.
  - split.
    + exact Hjustification.
    + eapply Hvalid.
      exact Hjustification.
Qed.

Theorem target_source_reason_must_name_live_source :
  forall live mechanisms kinds justifications mechanism justification responsibility,
    TargetClosureVerified live mechanisms kinds justifications ->
    justifications mechanism = Some justification ->
    closureSourceReasonRefs justification responsibility = true ->
    live responsibility = true.
Proof.
  intros live mechanisms kinds justifications mechanism justification
    responsibility Hverified Hlookup Hsource.
  destruct Hverified as [_ _ Hvalid].
  pose proof (Hvalid mechanism justification Hlookup) as Hjustification.
  destruct Hjustification as [Hknown _].
  eapply Hknown.
  exact Hsource.
Qed.

Theorem assumption_only_target_mechanism_cannot_close :
  forall live mechanisms kinds justifications mechanism justification,
    justifications mechanism = Some justification ->
    (forall responsibility,
      closureSourceReasonRefs justification responsibility = false) ->
    closureRealizationReason justification = false ->
    closureQualificationReason justification = false ->
    closureDerivedObligationReason justification = false ->
    ~ TargetClosureVerified live mechanisms kinds justifications.
Proof.
  intros live mechanisms kinds justifications mechanism justification
    Hlookup Hnosource Hnorealization Hnoqualification Hnoderived Hverified.
  destruct Hverified as [_ _ Hvalid].
  pose proof (Hvalid mechanism justification Hlookup) as Hjustification.
  destruct Hjustification as [_ Hreason].
  unfold HasTargetReason in Hreason.
  destruct Hreason as
    [[responsibility Hsource] | [Hrealization | [Hqualification | Hderived]]].
  - rewrite (Hnosource responsibility) in Hsource.
    discriminate.
  - rewrite Hnorealization in Hrealization.
    discriminate.
  - rewrite Hnoqualification in Hqualification.
    discriminate.
  - rewrite Hnoderived in Hderived.
    discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* SYS-020 — exact final closure of the concrete and next-stage trunks.        *)
(* -------------------------------------------------------------------------- *)

Record StageClosureIdentityFacts : Type := mkStageClosureIdentityFacts {
  closureConcreteSubjectRevision : nat;
  closureNextStageSubjectRevision : nat;
  closureConcreteInstanceRevision : nat;
  closureNextStageInstanceRevision : nat;
  closureConcreteRealizationRevision : nat;
  closureNextStageRealizationRevision : nat;
  closureConcreteSystemsRevision : nat;
  closureNextStageSystemsRevision : nat;
  closureConcreteStageContractRevision : nat;
  closureNextStageStageContractRevision : nat;
  closureConcreteVerifierProfileRevision : nat;
  closureNextStageVerifierProfileRevision : nat;
  closureRecomputedSystemsRevision : nat;
  closureStoredSystemsRevision : nat;
  closureRecomputedFinalRevision : nat;
  closureStoredFinalRevision : nat
}.

Definition StageClosureIdentityValid
  (facts : StageClosureIdentityFacts) : Prop :=
  closureConcreteSubjectRevision facts = closureNextStageSubjectRevision facts /\
  closureConcreteInstanceRevision facts = closureNextStageInstanceRevision facts /\
  closureConcreteRealizationRevision facts = closureNextStageRealizationRevision facts /\
  closureConcreteSystemsRevision facts = closureNextStageSystemsRevision facts /\
  closureConcreteStageContractRevision facts =
    closureNextStageStageContractRevision facts /\
  closureConcreteVerifierProfileRevision facts =
    closureNextStageVerifierProfileRevision facts /\
  closureRecomputedSystemsRevision facts = closureStoredSystemsRevision facts /\
  closureRecomputedFinalRevision facts = closureStoredFinalRevision facts /\
  closureStoredSystemsRevision facts <> 0 /\
  closureStoredFinalRevision facts <> 0.

Theorem final_stage_closure_binds_one_exact_common_trunk :
  forall facts,
    StageClosureIdentityValid facts ->
    closureConcreteSubjectRevision facts = closureNextStageSubjectRevision facts /\
    closureConcreteInstanceRevision facts = closureNextStageInstanceRevision facts /\
    closureConcreteRealizationRevision facts = closureNextStageRealizationRevision facts /\
    closureConcreteSystemsRevision facts = closureNextStageSystemsRevision facts /\
    closureConcreteStageContractRevision facts =
      closureNextStageStageContractRevision facts /\
    closureConcreteVerifierProfileRevision facts =
      closureNextStageVerifierProfileRevision facts.
Proof.
  intros facts Hvalid.
  destruct Hvalid as
    [Hsubject [Hinstance [Hrealization [Hsystems [Hstage [Hprofile _]]]]]].
  split.
  - exact Hsubject.
  - split.
    + exact Hinstance.
    + split.
      * exact Hrealization.
      * split.
        -- exact Hsystems.
        -- split.
           ++ exact Hstage.
           ++ exact Hprofile.
Qed.

Theorem final_stage_closure_recomputes_stored_identities :
  forall facts,
    StageClosureIdentityValid facts ->
    closureRecomputedSystemsRevision facts = closureStoredSystemsRevision facts /\
    closureRecomputedFinalRevision facts = closureStoredFinalRevision facts.
Proof.
  intros facts Hvalid.
  destruct Hvalid as
    [_ [_ [_ [_ [_ [_ [Hsystems [Hfinal _]]]]]]]].
  split.
  - exact Hsystems.
  - exact Hfinal.
Qed.

Theorem mismatched_subject_trunks_cannot_close :
  forall facts,
    closureConcreteSubjectRevision facts <>
      closureNextStageSubjectRevision facts ->
    ~ StageClosureIdentityValid facts.
Proof.
  intros facts Hmismatch Hvalid.
  destruct Hvalid as [Hsubject _].
  apply Hmismatch.
  exact Hsubject.
Qed.

Theorem stale_stored_systems_revision_cannot_close :
  forall facts,
    closureRecomputedSystemsRevision facts <>
      closureStoredSystemsRevision facts ->
    ~ StageClosureIdentityValid facts.
Proof.
  intros facts Hstale Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [Hsystems _]]]]]]].
  apply Hstale.
  exact Hsystems.
Qed.

Theorem stale_stored_final_revision_cannot_close :
  forall facts,
    closureRecomputedFinalRevision facts <>
      closureStoredFinalRevision facts ->
    ~ StageClosureIdentityValid facts.
Proof.
  intros facts Hstale Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hfinal _]]]]]]]].
  apply Hstale.
  exact Hfinal.
Qed.

(* -------------------------------------------------------------------------- *)
(* Validity-scope authority and cumulative PHIL-SYS-STAGE-CLOSURE-001.         *)
(* -------------------------------------------------------------------------- *)

Record SystemsStageClosurePreserved
  (factModel : StageFactModel)
  (live : SourceResponsibilitySet)
  (mechanisms : TargetMechanismSet)
  (dispositions : SourceDispositionEnvironment)
  (kinds : TargetMechanismKindEnvironment)
  (justifications : TargetJustificationEnvironment)
  (scope effective : ValidityMap)
  (identity : StageClosureIdentityFacts) : Prop :=
  mkSystemsStageClosurePreserved {
    systemsStageFactVerification :
      StageFactVerificationSuccess factModel;
    systemsStageFactProjection :
      FactProjectionExact live factModel;
    systemsStageSourceClosure :
      SourceClosureVerified live mechanisms dispositions;
    systemsStageTargetClosure :
      TargetClosureVerified live mechanisms kinds justifications;
    systemsStageValidityScopeMatches :
      ScopeMatches scope effective;
    systemsStageFinalIdentityClosure :
      StageClosureIdentityValid identity
  }.

Theorem systems_stage_closure_is_bidirectional_and_exact :
  forall factModel live mechanisms dispositions kinds justifications
         scope effective identity,
    SystemsStageClosurePreserved
      factModel live mechanisms dispositions kinds justifications
      scope effective identity ->
    ExactSourceDispositionCoverage live dispositions /\
    ExactTargetMechanismCoverage mechanisms kinds justifications /\
    ScopeMatches scope effective /\
    StageClosureIdentityValid identity.
Proof.
  intros factModel live mechanisms dispositions kinds justifications
    scope effective identity Hpreserved.
  destruct Hpreserved as
    [_ _ Hsource Htarget Hscope Hidentity].
  destruct Hsource as [HsourceExact _ _].
  destruct Htarget as [HtargetExact _ _].
  split.
  - exact HsourceExact.
  - split.
    + exact HtargetExact.
    + split.
      * exact Hscope.
      * exact Hidentity.
Qed.

Theorem bound_target_change_invalidates_stage_closure_authority :
  forall factModel live mechanisms dispositions kinds justifications
         scope oldContext newContext identity expectedTarget,
    SystemsStageClosurePreserved
      factModel live mechanisms dispositions kinds justifications
      scope oldContext identity ->
    scope TargetDimension = Some expectedTarget ->
    newContext TargetDimension <> Some expectedTarget ->
    ~ SystemsStageClosurePreserved
        factModel live mechanisms dispositions kinds justifications
        scope newContext identity.
Proof.
  intros factModel live mechanisms dispositions kinds justifications
    scope oldContext newContext identity expectedTarget
    Hold Hbound Hchanged Hnew.
  destruct Hold as [_ _ _ _ HoldScope _].
  destruct Hnew as [_ _ _ _ HnewScope _].
  pose proof
    (bound_target_change_invalidates_authority
      scope oldContext newContext expectedTarget
      HoldScope Hbound Hchanged)
    as HnotNewScope.
  apply HnotNewScope.
  exact HnewScope.
Qed.

Theorem bound_profile_change_invalidates_stage_closure_authority :
  forall factModel live mechanisms dispositions kinds justifications
         scope oldContext newContext identity expectedProfile,
    SystemsStageClosurePreserved
      factModel live mechanisms dispositions kinds justifications
      scope oldContext identity ->
    scope CompilationProfileDimension = Some expectedProfile ->
    newContext CompilationProfileDimension <> Some expectedProfile ->
    ~ SystemsStageClosurePreserved
        factModel live mechanisms dispositions kinds justifications
        scope newContext identity.
Proof.
  intros factModel live mechanisms dispositions kinds justifications
    scope oldContext newContext identity expectedProfile
    Hold Hbound Hchanged Hnew.
  destruct Hold as [_ _ _ _ HoldScope _].
  destruct Hnew as [_ _ _ _ HnewScope _].
  pose proof
    (bound_compilation_profile_change_invalidates_authority
      scope oldContext newContext expectedProfile
      HoldScope Hbound Hchanged)
    as HnotNewScope.
  apply HnotNewScope.
  exact HnewScope.
Qed.
