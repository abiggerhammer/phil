From Stdlib Require Import Bool.Bool.

From Phil.Verification Require Import VerificationArtifact.

(*
  PHIL-VERIFY-ARTIFACT-001 — finite executable correspondence.

  The production composition has three authorities:

  - an already-accepted source assurance value;
  - the existing StageClosure verifier for the exact emitted realization; and
  - final manifest closure/binding at the release-assurance boundary.

  This normalized boolean layer certifies only the conjunction structure.  It
  does not re-implement StageClosure, GenericApplicationAssurance, manifest
  verification, hashing, or backend/toolchain semantics.
*)

Definition finalArtifactFactsb
  (sourceAssuranceAccepted stageClosureAccepted manifestClosed
    manifestScopeMatches manifestBoundToStage : bool) : bool :=
  andb sourceAssuranceAccepted
    (andb stageClosureAccepted
      (andb manifestClosed
        (andb manifestScopeMatches manifestBoundToStage))).

Inductive FinalArtifactDecision : Type :=
| FinalArtifactAccepted
| FinalArtifactRejected.

Definition decideFinalArtifactCertification
  (sourceAssuranceAccepted stageClosureAccepted manifestClosed
    manifestScopeMatches manifestBoundToStage : bool) : FinalArtifactDecision :=
  if finalArtifactFactsb
      sourceAssuranceAccepted stageClosureAccepted manifestClosed
      manifestScopeMatches manifestBoundToStage
  then FinalArtifactAccepted
  else FinalArtifactRejected.

Theorem final_artifact_facts_true_iff_all_gates :
  forall sourceAssuranceAccepted stageClosureAccepted manifestClosed
    manifestScopeMatches manifestBoundToStage,
    finalArtifactFactsb
      sourceAssuranceAccepted stageClosureAccepted manifestClosed
      manifestScopeMatches manifestBoundToStage = true <->
    sourceAssuranceAccepted = true /\
    stageClosureAccepted = true /\
    manifestClosed = true /\
    manifestScopeMatches = true /\
    manifestBoundToStage = true.
Proof.
  intros sourceAssuranceAccepted stageClosureAccepted manifestClosed
    manifestScopeMatches manifestBoundToStage.
  unfold finalArtifactFactsb.
  repeat rewrite andb_true_iff.
  tauto.
Qed.

Theorem final_artifact_decision_accept_iff_facts_true :
  forall sourceAssuranceAccepted stageClosureAccepted manifestClosed
    manifestScopeMatches manifestBoundToStage,
    decideFinalArtifactCertification
      sourceAssuranceAccepted stageClosureAccepted manifestClosed
      manifestScopeMatches manifestBoundToStage = FinalArtifactAccepted <->
    finalArtifactFactsb
      sourceAssuranceAccepted stageClosureAccepted manifestClosed
      manifestScopeMatches manifestBoundToStage = true.
Proof.
  intros sourceAssuranceAccepted stageClosureAccepted manifestClosed
    manifestScopeMatches manifestBoundToStage.
  unfold decideFinalArtifactCertification.
  destruct (finalArtifactFactsb
    sourceAssuranceAccepted stageClosureAccepted manifestClosed
    manifestScopeMatches manifestBoundToStage) eqn:Hfacts.
  - split.
    + intros Haccepted.
      reflexivity.
    + intros Htrue.
      reflexivity.
  - split.
    + intros Haccepted.
      discriminate Haccepted.
    + intros Htrue.
      rewrite Hfacts in Htrue.
      discriminate Htrue.
Qed.

Theorem source_assurance_without_stage_closure_rejects :
  forall manifestClosed manifestScopeMatches manifestBoundToStage,
    decideFinalArtifactCertification
      true false manifestClosed manifestScopeMatches manifestBoundToStage =
      FinalArtifactRejected.
Proof.
  reflexivity.
Qed.

Theorem stage_closure_without_manifest_closure_rejects :
  forall manifestScopeMatches manifestBoundToStage,
    decideFinalArtifactCertification
      true true false manifestScopeMatches manifestBoundToStage =
      FinalArtifactRejected.
Proof.
  reflexivity.
Qed.

Theorem manifest_scope_mismatch_rejects :
  forall manifestBoundToStage,
    decideFinalArtifactCertification true true true false manifestBoundToStage =
      FinalArtifactRejected.
Proof.
  reflexivity.
Qed.

Theorem mutated_manifest_stage_binding_rejects :
  decideFinalArtifactCertification true true true true false =
    FinalArtifactRejected.
Proof.
  reflexivity.
Qed.

Theorem all_exact_artifact_gates_accept :
  decideFinalArtifactCertification true true true true true =
    FinalArtifactAccepted.
Proof.
  reflexivity.
Qed.
