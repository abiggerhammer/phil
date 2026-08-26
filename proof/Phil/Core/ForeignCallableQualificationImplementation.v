From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import ForeignCallableQualification.

(* PHIL-CALL-FOREIGN-IMPL-001 — executable production correspondence. *)

Definition qualificationBits {Qualification : Type}
  (artifactMatches : Qualification -> bool)
  (surfaceMatches : Qualification -> bool)
  (hasAbiEvidence : Qualification -> bool)
  (hasResourceLifecycleEvidence : Qualification -> bool)
  (hasEffectConfinementEvidence : Qualification -> bool)
  (hasAuthorityConfinementEvidence : Qualification -> bool)
  (hasFailureBehaviorEvidence : Qualification -> bool)
  (qualification : Qualification) : list bool :=
  [ artifactMatches qualification
  ; surfaceMatches qualification
  ; hasAbiEvidence qualification
  ; hasResourceLifecycleEvidence qualification
  ; hasEffectConfinementEvidence qualification
  ; hasAuthorityConfinementEvidence qualification
  ; hasFailureBehaviorEvidence qualification
  ].

Fixpoint allQualificationBits (bits : list bool) : Prop :=
  match bits with
  | nil => True
  | bit :: rest => bit = true /\ allQualificationBits rest
  end.

Fixpoint allQualificationBitsb (bits : list bool) : bool :=
  match bits with
  | nil => true
  | bit :: rest => bit && allQualificationBitsb rest
  end.

Lemma all_qualification_bitsb_true_iff :
  forall bits,
    allQualificationBitsb bits = true <-> allQualificationBits bits.
Proof.
  induction bits as [| bit rest IH].
  - cbn. tauto.
  - cbn. rewrite andb_true_iff, IH. tauto.
Qed.

Definition decideForeignQualification {Qualification : Type}
  (maybeQualification : option Qualification)
  (artifactMatches : Qualification -> bool)
  (surfaceMatches : Qualification -> bool)
  (hasAbiEvidence : Qualification -> bool)
  (hasResourceLifecycleEvidence : Qualification -> bool)
  (hasEffectConfinementEvidence : Qualification -> bool)
  (hasAuthorityConfinementEvidence : Qualification -> bool)
  (hasFailureBehaviorEvidence : Qualification -> bool) : bool :=
  match maybeQualification with
  | None => false
  | Some qualification =>
      allQualificationBitsb
        (qualificationBits
          artifactMatches surfaceMatches
          hasAbiEvidence hasResourceLifecycleEvidence
          hasEffectConfinementEvidence hasAuthorityConfinementEvidence
          hasFailureBehaviorEvidence qualification)
  end.

Definition ForeignQualificationProjectionAccepts {Qualification : Type}
  (maybeQualification : option Qualification)
  (artifactMatches : Qualification -> bool)
  (surfaceMatches : Qualification -> bool)
  (hasAbiEvidence : Qualification -> bool)
  (hasResourceLifecycleEvidence : Qualification -> bool)
  (hasEffectConfinementEvidence : Qualification -> bool)
  (hasAuthorityConfinementEvidence : Qualification -> bool)
  (hasFailureBehaviorEvidence : Qualification -> bool)
  (qualification : Qualification) : Prop :=
  maybeQualification = Some qualification /\
  allQualificationBits
    (qualificationBits
      artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence qualification).

Theorem foreign_decision_true_for_exact_qualification_iff :
  forall (Qualification : Type)
      (qualification : Qualification)
      artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence,
    decideForeignQualification
      (Some qualification)
      artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence = true <->
    ForeignQualificationProjectionAccepts
      (Some qualification)
      artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence qualification.
Proof.
  intros Qualification qualification
    artifactMatches surfaceMatches
    hasAbiEvidence hasResourceLifecycleEvidence
    hasEffectConfinementEvidence hasAuthorityConfinementEvidence
    hasFailureBehaviorEvidence.
  unfold decideForeignQualification, ForeignQualificationProjectionAccepts.
  cbn.
  rewrite all_qualification_bitsb_true_iff.
  tauto.
Qed.

Theorem absent_foreign_qualification_rejects :
  forall (Qualification : Type)
      artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence,
    decideForeignQualification
      (None : option Qualification)
      artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence = false.
Proof. reflexivity. Qed.

Theorem accepted_production_qualification_refines_call015 :
  forall expected artifact qualification
      artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence,
    (artifactMatches qualification = true ->
      qualificationArtifactKey qualification = foreignArtifactKey artifact) ->
    (surfaceMatches qualification = true ->
      qualificationSurface qualification = foreignObservedSurface artifact) ->
    (hasAbiEvidence qualification = true ->
      exists evidence, qualificationEvidence qualification EvidenceAbi = Some evidence) ->
    (hasResourceLifecycleEvidence qualification = true ->
      exists evidence,
        qualificationEvidence qualification EvidenceResourceLifecycle = Some evidence) ->
    (hasEffectConfinementEvidence qualification = true ->
      exists evidence,
        qualificationEvidence qualification EvidenceEffectConfinement = Some evidence) ->
    (hasAuthorityConfinementEvidence qualification = true ->
      exists evidence,
        qualificationEvidence qualification EvidenceAuthorityConfinement = Some evidence) ->
    (hasFailureBehaviorEvidence qualification = true ->
      exists evidence,
        qualificationEvidence qualification EvidenceFailureBehavior = Some evidence) ->
    callableRefines expected (qualificationSurface qualification) ->
    decideForeignQualification
      (Some qualification)
      artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence = true ->
    ForeignQualificationAccepts expected artifact qualification.
Proof.
  intros expected artifact qualification
    artifactMatches surfaceMatches
    hasAbiEvidence hasResourceLifecycleEvidence
    hasEffectConfinementEvidence hasAuthorityConfinementEvidence
    hasFailureBehaviorEvidence
    HartifactBridge HsurfaceBridge
    HabiBridge HresourceBridge HeffectBridge HauthorityBridge HfailureBridge
    Hrefines Hdecision.
  pose proof (proj1
    (foreign_decision_true_for_exact_qualification_iff
      ForeignQualification qualification
      artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence) Hdecision) as [_ Hbits].
  cbn in Hbits.
  destruct Hbits as
    [Hartifact [Hsurface [Habi [Hresource [Heffect [Hauthority [Hfailure _]]]]]]].
  unfold ForeignQualificationAccepts.
  split.
  - apply HartifactBridge. exact Hartifact.
  - split.
    + apply HsurfaceBridge. exact Hsurface.
    + split.
      * intro kind. destruct kind.
        -- apply HabiBridge. exact Habi.
        -- apply HresourceBridge. exact Hresource.
        -- apply HeffectBridge. exact Heffect.
        -- apply HauthorityBridge. exact Hauthority.
        -- apply HfailureBridge. exact Hfailure.
      * exact Hrefines.
Qed.
