From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ForeignCallableQualification.

(*
  PHIL-CALL-FOREIGN-IMPL-001 — executable production correspondence for CALL-015.

  The extracted gate handles qualification presence and every finite admission
  condition.  The production Haskell adapter supplies only exact equality and
  evidence-presence predicates.  Semantic callable non-widening remains a
  separate second-stage decision and is composed with the already
  Implementation Refined CALL-012 production checker.
*)

Inductive ForeignQualificationDecision (Qualification : Type) : Type :=
| ForeignQualificationAccepted (qualification : Qualification)
| ForeignQualificationMissing
| ForeignQualificationArtifactMismatch (qualification : Qualification)
| ForeignQualificationSurfaceMismatch (qualification : Qualification)
| ForeignQualificationEvidenceMissing (qualification : Qualification).

Arguments ForeignQualificationAccepted {Qualification} _.
Arguments ForeignQualificationMissing {Qualification}.
Arguments ForeignQualificationArtifactMismatch {Qualification} _.
Arguments ForeignQualificationSurfaceMismatch {Qualification} _.
Arguments ForeignQualificationEvidenceMissing {Qualification} _.

Definition decideForeignQualification {Qualification : Type}
  (maybeQualification : option Qualification)
  (artifactMatches : Qualification -> bool)
  (surfaceMatches : Qualification -> bool)
  (hasAbiEvidence : Qualification -> bool)
  (hasResourceLifecycleEvidence : Qualification -> bool)
  (hasEffectConfinementEvidence : Qualification -> bool)
  (hasAuthorityConfinementEvidence : Qualification -> bool)
  (hasFailureBehaviorEvidence : Qualification -> bool)
  : ForeignQualificationDecision Qualification :=
  match maybeQualification with
  | None => ForeignQualificationMissing
  | Some qualification =>
      if artifactMatches qualification then
        if surfaceMatches qualification then
          if hasAbiEvidence qualification then
            if hasResourceLifecycleEvidence qualification then
              if hasEffectConfinementEvidence qualification then
                if hasAuthorityConfinementEvidence qualification then
                  if hasFailureBehaviorEvidence qualification then
                    ForeignQualificationAccepted qualification
                  else ForeignQualificationEvidenceMissing qualification
                else ForeignQualificationEvidenceMissing qualification
              else ForeignQualificationEvidenceMissing qualification
            else ForeignQualificationEvidenceMissing qualification
          else ForeignQualificationEvidenceMissing qualification
        else ForeignQualificationSurfaceMismatch qualification
      else ForeignQualificationArtifactMismatch qualification
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
  artifactMatches qualification = true /\
  surfaceMatches qualification = true /\
  hasAbiEvidence qualification = true /\
  hasResourceLifecycleEvidence qualification = true /\
  hasEffectConfinementEvidence qualification = true /\
  hasAuthorityConfinementEvidence qualification = true /\
  hasFailureBehaviorEvidence qualification = true.

Theorem accepted_foreign_decision_iff_projection :
  forall (Qualification : Type)
      (maybeQualification : option Qualification)
      artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence qualification,
    decideForeignQualification
      maybeQualification artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence = ForeignQualificationAccepted qualification <->
    ForeignQualificationProjectionAccepts
      maybeQualification artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence qualification.
Proof.
  intros Qualification maybeQualification artifactMatches surfaceMatches
    hasAbiEvidence hasResourceLifecycleEvidence
    hasEffectConfinementEvidence hasAuthorityConfinementEvidence
    hasFailureBehaviorEvidence qualification.
  destruct maybeQualification as [candidate|].
  - cbn.
    destruct (artifactMatches candidate) eqn:Hartifact.
    + destruct (surfaceMatches candidate) eqn:Hsurface.
      * destruct (hasAbiEvidence candidate) eqn:Habi.
        -- destruct (hasResourceLifecycleEvidence candidate) eqn:Hresource.
           ++ destruct (hasEffectConfinementEvidence candidate) eqn:Heffect.
              ** destruct (hasAuthorityConfinementEvidence candidate) eqn:Hauthority.
                 --- destruct (hasFailureBehaviorEvidence candidate) eqn:Hfailure.
                     +++ split; intro H.
                         *** inversion H; subst candidate.
                             repeat split; assumption.
                         *** destruct H as [Hsome [Ha [Hs [Hab [Hr [He [Hau Hf]]]]]]].
                             inversion Hsome; subst candidate.
                             rewrite Ha, Hs, Hab, Hr, He, Hau, Hf.
                             reflexivity.
                     +++ split; intro H; [discriminate | destruct H as [_ [_ [_ [_ [_ [_ [_ Hf]]]]]]]; rewrite Hfailure in Hf; discriminate].
                 --- split; intro H; [discriminate | destruct H as [_ [_ [_ [_ [_ [_ [Hau _]]]]]]]; rewrite Hauthority in Hau; discriminate].
              ** split; intro H; [discriminate | destruct H as [_ [_ [_ [_ [_ [He _]]]]]]; rewrite Heffect in He; discriminate].
           ++ split; intro H; [discriminate | destruct H as [_ [_ [_ [_ [Hr _]]]]]; rewrite Hresource in Hr; discriminate].
        -- split; intro H; [discriminate | destruct H as [_ [_ [_ [Hab _]]]]; rewrite Habi in Hab; discriminate].
      * split; intro H; [discriminate | destruct H as [_ [_ [Hs _]]]; rewrite Hsurface in Hs; discriminate].
    + split; intro H; [discriminate | destruct H as [_ [Ha _]]; rewrite Hartifact in Ha; discriminate].
  - cbn. split; intro H.
    + discriminate.
    + destruct H as [Hsome _]. discriminate.
Qed.

Theorem accepted_production_qualification_refines_call015 :
  forall expected artifact maybeQualification qualification
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
      maybeQualification artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence = ForeignQualificationAccepted qualification ->
    ForeignQualificationAccepts expected artifact qualification.
Proof.
  intros expected artifact maybeQualification qualification
    artifactMatches surfaceMatches
    hasAbiEvidence hasResourceLifecycleEvidence
    hasEffectConfinementEvidence hasAuthorityConfinementEvidence
    hasFailureBehaviorEvidence
    HartifactBridge HsurfaceBridge
    HabiBridge HresourceBridge HeffectBridge HauthorityBridge HfailureBridge
    Hrefines Hdecision.
  pose proof (proj1
    (accepted_foreign_decision_iff_projection
      ForeignQualification maybeQualification
      artifactMatches surfaceMatches
      hasAbiEvidence hasResourceLifecycleEvidence
      hasEffectConfinementEvidence hasAuthorityConfinementEvidence
      hasFailureBehaviorEvidence qualification) Hdecision)
    as [Hsome [Hartifact [Hsurface [Habi [Hresource [Heffect [Hauthority Hfailure]]]]]]].
  unfold ForeignQualificationAccepts.
  split.
  - apply HartifactBridge. exact Hartifact.
  - split.
    + apply HsurfaceBridge. exact Hsurface.
    + split.
      * intro kind.
        destruct kind.
        -- apply HabiBridge. exact Habi.
        -- apply HresourceBridge. exact Hresource.
        -- apply HeffectBridge. exact Heffect.
        -- apply HauthorityBridge. exact Hauthority.
        -- apply HfailureBridge. exact Hfailure.
      * exact Hrefines.
Qed.
