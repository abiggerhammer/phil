From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import DataSubject.

(*
  PHIL-DATA-SUBJECT-001 — executable implementation correspondence.

  Concrete RefTerm/Proposition/Text representation, stable-identity decoding,
  proposition substitution/normalization, and diagnostics remain native.  The
  extracted layer owns only the ordered final semantic decisions over reflected
  primitive facts.
*)

Inductive DataSubjectPrerequisiteDecision : Type :=
| DataSubjectPrerequisitesAccepted
| DataSubjectPriorNotConsumedDecision
| DataSubjectReplacementNotConstructedDecision
| DataSubjectPriorNotStableDecision
| DataSubjectReplacementNotStableDecision
| DataSubjectKindMismatchDecision
| DataSubjectEvidenceTemplateMissingSubjectDecision
| DataSubjectEvidencePriorMismatchDecision
| DataSubjectEvidenceNotStableDecision
| DataSubjectEvidenceKindMismatchDecision.

Definition decideDataSubjectPrerequisites
  (priorConsumed replacementConstructed priorStable replacementStable
   kindsMatch evidenceTemplateMentionsSubject evidenceMatchesPrior
   evidenceStable evidenceKindMatchesPrior : bool)
  : DataSubjectPrerequisiteDecision :=
  if priorConsumed then
    if replacementConstructed then
      if priorStable then
        if replacementStable then
          if kindsMatch then
            if evidenceTemplateMentionsSubject then
              if evidenceMatchesPrior then
                if evidenceStable then
                  if evidenceKindMatchesPrior then
                    DataSubjectPrerequisitesAccepted
                  else DataSubjectEvidenceKindMismatchDecision
                else DataSubjectEvidenceNotStableDecision
              else DataSubjectEvidencePriorMismatchDecision
            else DataSubjectEvidenceTemplateMissingSubjectDecision
          else DataSubjectKindMismatchDecision
        else DataSubjectReplacementNotStableDecision
      else DataSubjectPriorNotStableDecision
    else DataSubjectReplacementNotConstructedDecision
  else DataSubjectPriorNotConsumedDecision.

Definition dataSubjectPrerequisiteFactsAccepted
  (priorConsumed replacementConstructed priorStable replacementStable
   kindsMatch evidenceTemplateMentionsSubject evidenceMatchesPrior
   evidenceStable evidenceKindMatchesPrior : bool) : bool :=
  andb priorConsumed
    (andb replacementConstructed
      (andb priorStable
        (andb replacementStable
          (andb kindsMatch
            (andb evidenceTemplateMentionsSubject
              (andb evidenceMatchesPrior
                (andb evidenceStable evidenceKindMatchesPrior))))))).

Definition DataSubjectPrerequisites
  (update : DataSubjectUpdate)
  (evidence : SubjectBoundEvidence) : Prop :=
  dataSubjectUpdatePriorConsumed update = true /\
  dataSubjectUpdateReplacementConstructed update = true /\
  dataSubjectStable (dataSubjectUpdatePrior update) = true /\
  dataSubjectStable (dataSubjectUpdateReplacement update) = true /\
  dataSubjectKind (dataSubjectUpdatePrior update) =
    dataSubjectKind (dataSubjectUpdateReplacement update) /\
  subjectEvidenceTemplateMentionsSubject evidence = true /\
  dataSubjectIdentity (subjectEvidenceSubject evidence) =
    dataSubjectIdentity (dataSubjectUpdatePrior update) /\
  dataSubjectStable (subjectEvidenceSubject evidence) = true /\
  dataSubjectKind (subjectEvidenceSubject evidence) =
    dataSubjectKind (dataSubjectUpdatePrior update).

Theorem prerequisite_decision_accept_iff_all_reflected_facts :
  forall priorConsumed replacementConstructed priorStable replacementStable
    kindsMatch evidenceTemplateMentionsSubject evidenceMatchesPrior
    evidenceStable evidenceKindMatchesPrior,
    decideDataSubjectPrerequisites
      priorConsumed replacementConstructed priorStable replacementStable
      kindsMatch evidenceTemplateMentionsSubject evidenceMatchesPrior
      evidenceStable evidenceKindMatchesPrior =
      DataSubjectPrerequisitesAccepted <->
    dataSubjectPrerequisiteFactsAccepted
      priorConsumed replacementConstructed priorStable replacementStable
      kindsMatch evidenceTemplateMentionsSubject evidenceMatchesPrior
      evidenceStable evidenceKindMatchesPrior = true.
Proof.
  intros.
  destruct priorConsumed, replacementConstructed, priorStable,
    replacementStable, kindsMatch, evidenceTemplateMentionsSubject,
    evidenceMatchesPrior, evidenceStable, evidenceKindMatchesPrior;
    simpl; split; intro H; try reflexivity; discriminate H.
Qed.

Theorem reflected_prerequisite_facts_are_certified :
  forall update evidence
    priorConsumed replacementConstructed priorStable replacementStable
    kindsMatch evidenceTemplateMentionsSubject evidenceMatchesPrior
    evidenceStable evidenceKindMatchesPrior,
    (priorConsumed = true <-> dataSubjectUpdatePriorConsumed update = true) ->
    (replacementConstructed = true <->
      dataSubjectUpdateReplacementConstructed update = true) ->
    (priorStable = true <->
      dataSubjectStable (dataSubjectUpdatePrior update) = true) ->
    (replacementStable = true <->
      dataSubjectStable (dataSubjectUpdateReplacement update) = true) ->
    (kindsMatch = true <->
      dataSubjectKind (dataSubjectUpdatePrior update) =
        dataSubjectKind (dataSubjectUpdateReplacement update)) ->
    (evidenceTemplateMentionsSubject = true <->
      subjectEvidenceTemplateMentionsSubject evidence = true) ->
    (evidenceMatchesPrior = true <->
      dataSubjectIdentity (subjectEvidenceSubject evidence) =
        dataSubjectIdentity (dataSubjectUpdatePrior update)) ->
    (evidenceStable = true <->
      dataSubjectStable (subjectEvidenceSubject evidence) = true) ->
    (evidenceKindMatchesPrior = true <->
      dataSubjectKind (subjectEvidenceSubject evidence) =
        dataSubjectKind (dataSubjectUpdatePrior update)) ->
    (dataSubjectPrerequisiteFactsAccepted
      priorConsumed replacementConstructed priorStable replacementStable
      kindsMatch evidenceTemplateMentionsSubject evidenceMatchesPrior
      evidenceStable evidenceKindMatchesPrior = true <->
      DataSubjectPrerequisites update evidence).
Proof.
  intros update evidence priorConsumed replacementConstructed priorStable
    replacementStable kindsMatch evidenceTemplateMentionsSubject
    evidenceMatchesPrior evidenceStable evidenceKindMatchesPrior
    Hconsumed Hconstructed HpriorStable HreplacementStable Hkinds Hmentions
    HevidenceIdentity HevidenceStable HevidenceKind.
  unfold dataSubjectPrerequisiteFactsAccepted, DataSubjectPrerequisites.
  repeat rewrite Bool.andb_true_iff.
  rewrite Hconsumed, Hconstructed, HpriorStable, HreplacementStable, Hkinds,
    Hmentions, HevidenceIdentity, HevidenceStable, HevidenceKind.
  reflexivity.
Qed.

Inductive DataSubjectTransportModeDecision : Type :=
| DataSubjectTransportModeAccepted
| DataSubjectUnexpectedTransportDecision
| DataSubjectTransportRequiredDecision.

Definition decideDataSubjectTransportMode
  (sameSubject transportPresent : bool) : DataSubjectTransportModeDecision :=
  if sameSubject then
    if transportPresent then DataSubjectUnexpectedTransportDecision
    else DataSubjectTransportModeAccepted
  else
    if transportPresent then DataSubjectTransportModeAccepted
    else DataSubjectTransportRequiredDecision.

Definition dataSubjectTransportModeFactsAccepted
  (sameSubject transportPresent : bool) : bool :=
  Bool.eqb sameSubject (negb transportPresent).

Theorem transport_mode_decision_accept_iff_exact_presence_shape :
  forall sameSubject transportPresent,
    decideDataSubjectTransportMode sameSubject transportPresent =
      DataSubjectTransportModeAccepted <->
    dataSubjectTransportModeFactsAccepted sameSubject transportPresent = true.
Proof.
  intros sameSubject transportPresent.
  destruct sameSubject, transportPresent;
    simpl; split; intro H; try reflexivity; discriminate H.
Qed.

Inductive DataSubjectTransportDecision : Type :=
| DataSubjectTransportAcceptedDecision
| DataSubjectTransportDispositionRejectedDecision
| DataSubjectTransportRevisionMissingDecision
| DataSubjectTransportEvidenceMismatchDecision
| DataSubjectTransportPriorMismatchDecision
| DataSubjectTransportReplacementMismatchDecision
| DataSubjectTransportSourcePropositionMismatchDecision
| DataSubjectTransportTargetPropositionMismatchDecision.

Definition decideDataSubjectTransport
  (dispositionAccepted revisionNonempty evidenceReferenceMatches
   priorIdentityMatches replacementIdentityMatches sourcePropositionMatches
   targetPropositionMatches : bool) : DataSubjectTransportDecision :=
  if dispositionAccepted then
    if revisionNonempty then
      if evidenceReferenceMatches then
        if priorIdentityMatches then
          if replacementIdentityMatches then
            if sourcePropositionMatches then
              if targetPropositionMatches then DataSubjectTransportAcceptedDecision
              else DataSubjectTransportTargetPropositionMismatchDecision
            else DataSubjectTransportSourcePropositionMismatchDecision
          else DataSubjectTransportReplacementMismatchDecision
        else DataSubjectTransportPriorMismatchDecision
      else DataSubjectTransportEvidenceMismatchDecision
    else DataSubjectTransportRevisionMissingDecision
  else DataSubjectTransportDispositionRejectedDecision.

Definition dataSubjectTransportFactsAccepted
  (dispositionAccepted revisionNonempty evidenceReferenceMatches
   priorIdentityMatches replacementIdentityMatches sourcePropositionMatches
   targetPropositionMatches : bool) : bool :=
  andb dispositionAccepted
    (andb revisionNonempty
      (andb evidenceReferenceMatches
        (andb priorIdentityMatches
          (andb replacementIdentityMatches
            (andb sourcePropositionMatches targetPropositionMatches))))).

Theorem transport_decision_accept_iff_all_reflected_facts :
  forall dispositionAccepted revisionNonempty evidenceReferenceMatches
    priorIdentityMatches replacementIdentityMatches sourcePropositionMatches
    targetPropositionMatches,
    decideDataSubjectTransport
      dispositionAccepted revisionNonempty evidenceReferenceMatches
      priorIdentityMatches replacementIdentityMatches sourcePropositionMatches
      targetPropositionMatches = DataSubjectTransportAcceptedDecision <->
    dataSubjectTransportFactsAccepted
      dispositionAccepted revisionNonempty evidenceReferenceMatches
      priorIdentityMatches replacementIdentityMatches sourcePropositionMatches
      targetPropositionMatches = true.
Proof.
  intros.
  destruct dispositionAccepted, revisionNonempty, evidenceReferenceMatches,
    priorIdentityMatches, replacementIdentityMatches, sourcePropositionMatches,
    targetPropositionMatches;
    simpl; split; intro H; try reflexivity; discriminate H.
Qed.

Theorem reflected_transport_facts_are_certified :
  forall update evidence transport
    dispositionAccepted revisionNonempty evidenceReferenceMatches
    priorIdentityMatches replacementIdentityMatches sourcePropositionMatches
    targetPropositionMatches,
    (dispositionAccepted = true <->
      dataSubjectTransportAccepted transport = true) ->
    (revisionNonempty = true <->
      dataSubjectTransportRelationRevision transport <> 0) ->
    (evidenceReferenceMatches = true <->
      dataSubjectTransportEvidenceReference transport =
        subjectEvidenceReference evidence) ->
    (priorIdentityMatches = true <->
      dataSubjectTransportPriorIdentity transport =
        dataSubjectIdentity (dataSubjectUpdatePrior update)) ->
    (replacementIdentityMatches = true <->
      dataSubjectTransportReplacementIdentity transport =
        dataSubjectIdentity (dataSubjectUpdateReplacement update)) ->
    (sourcePropositionMatches = true <->
      dataSubjectTransportSourceProposition transport =
        sourceProposition update evidence) ->
    (targetPropositionMatches = true <->
      dataSubjectTransportTargetProposition transport =
        targetProposition update evidence) ->
    (dataSubjectTransportFactsAccepted
      dispositionAccepted revisionNonempty evidenceReferenceMatches
      priorIdentityMatches replacementIdentityMatches sourcePropositionMatches
      targetPropositionMatches = true <->
      TransportValid update evidence transport).
Proof.
  intros update evidence transport dispositionAccepted revisionNonempty
    evidenceReferenceMatches priorIdentityMatches replacementIdentityMatches
    sourcePropositionMatches targetPropositionMatches Hdisposition Hrevision
    Hevidence Hprior Hreplacement Hsource Htarget.
  unfold dataSubjectTransportFactsAccepted, TransportValid.
  repeat rewrite Bool.andb_true_iff.
  rewrite Hdisposition, Hrevision, Hevidence, Hprior, Hreplacement, Hsource,
    Htarget.
  reflexivity.
Qed.

Theorem certified_same_subject_without_transport_constructs_checked_update :
  forall update evidence,
    DataSubjectPrerequisites update evidence ->
    dataSubjectIdentity (dataSubjectUpdatePrior update) =
      dataSubjectIdentity (dataSubjectUpdateReplacement update) ->
    CheckedDataSubjectUpdate update evidence None
      (retargetEvidence evidence (dataSubjectUpdateReplacement update)).
Proof.
  intros update evidence Hpre Hsame.
  unfold DataSubjectPrerequisites in Hpre.
  destruct Hpre as
    [Hconsumed [Hconstructed [HpriorStable [HreplacementStable
    [Hkind [Hmentions [HevidenceIdentity [HevidenceStable HevidenceKind]]]]]]]].
  constructor; assumption.
Qed.

Theorem certified_changed_subject_with_valid_transport_constructs_checked_update :
  forall update evidence transport,
    DataSubjectPrerequisites update evidence ->
    dataSubjectIdentity (dataSubjectUpdatePrior update) <>
      dataSubjectIdentity (dataSubjectUpdateReplacement update) ->
    TransportValid update evidence transport ->
    CheckedDataSubjectUpdate update evidence (Some transport)
      (retargetEvidence evidence (dataSubjectUpdateReplacement update)).
Proof.
  intros update evidence transport Hpre Hchanged Htransport.
  unfold DataSubjectPrerequisites in Hpre.
  destruct Hpre as
    [Hconsumed [Hconstructed [HpriorStable [HreplacementStable
    [Hkind [Hmentions [HevidenceIdentity [HevidenceStable HevidenceKind]]]]]]]].
  econstructor; eauto.
Qed.
