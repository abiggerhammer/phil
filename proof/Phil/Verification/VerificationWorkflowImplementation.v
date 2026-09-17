From Stdlib Require Import Bool.Bool Lists.List.

Import ListNotations.

From Phil.Verification Require Import VerificationWorkflow.

(*
  PHIL-VERIFY-WORKFLOW-001 — executable workflow correspondence.

  Production reaches the independent VerificationBundle only after a sequence
  of already-competent native facts has been established: intrinsic acceptance,
  canonical graph construction, nonempty source/policy identities, and exact
  evidence admission.  This file owns the finite conjunction of those facts.

  Concrete parsing/checking, Text emptiness, Map/Set normalization, revision and
  digest construction, and diagnostic payloads remain native/predecessor
  boundaries.  Under explicit fact reflection, the executable decision accepts
  iff the Certified semantic workflow admission relation holds.
*)

Definition GraphNodesUnique (graph : VerificationGraph) : Prop :=
  NoDup (verificationGraphNodes graph).

Definition GraphDependenciesKnown (graph : VerificationGraph) : Prop :=
  forall owner dependency,
    In (owner, dependency) (verificationGraphDependencies graph) ->
    In owner (verificationGraphNodes graph) /\
    In dependency (verificationGraphNodes graph).

Definition GraphScopeKnown (graph : VerificationGraph) : Prop :=
  forall revision,
    In revision (verificationGraphCertificationScope graph) ->
    In revision (verificationGraphNodes graph).

Theorem graph_well_formed_iff_component_facts :
  forall graph,
    GraphWellFormed graph <->
    GraphNodesUnique graph /\
    GraphDependenciesKnown graph /\
    GraphScopeKnown graph /\
    NoDependencyCycle graph.
Proof.
  intros graph.
  unfold GraphWellFormed, GraphNodesUnique,
    GraphDependenciesKnown, GraphScopeKnown.
  tauto.
Qed.

Definition evidenceFactAcceptedb (facts : EvidenceFacts) : bool :=
  andb (evidenceAccepted facts)
    (andb (evidenceDigestMatches facts)
      (andb (evidenceTargetKnown facts)
        (evidenceIdentityConflictFree facts))).

Fixpoint evidenceFactsb (facts : list EvidenceFacts) : bool :=
  match facts with
  | [] => true
  | fact :: rest => andb (evidenceFactAcceptedb fact) (evidenceFactsb rest)
  end.

Theorem evidence_fact_acceptedb_true_iff_valid :
  forall facts,
    evidenceFactAcceptedb facts = true <-> EvidenceFactsValid facts.
Proof.
  intros facts.
  unfold evidenceFactAcceptedb, EvidenceFactsValid.
  repeat rewrite andb_true_iff.
  tauto.
Qed.

Theorem evidence_factsb_true_iff_all_valid :
  forall facts,
    evidenceFactsb facts = true <-> Forall EvidenceFactsValid facts.
Proof.
  intros facts.
  induction facts as [|fact rest IH].
  - cbn.
    split.
    + intros _.
      constructor.
    + intros _.
      reflexivity.
  - cbn.
    rewrite andb_true_iff.
    rewrite evidence_fact_acceptedb_true_iff_valid.
    rewrite IH.
    split.
    + intros [Hfact Hrest].
      constructor; assumption.
    + intros Hall.
      inversion Hall; subst.
      split; assumption.
Qed.

Inductive VerificationWorkflowDecision : Type :=
| VerificationWorkflowAccepted
| VerificationWorkflowRejected.

Definition workflowFactsb
  (intrinsicAcceptedFact : bool)
  (nodesUniqueFact : bool)
  (dependenciesKnownFact : bool)
  (scopeKnownFact : bool)
  (acyclicFact : bool)
  (sourceRevisionValidFact : bool)
  (policyRevisionValidFact : bool)
  (evidence : list EvidenceFacts) : bool :=
  andb intrinsicAcceptedFact
    (andb nodesUniqueFact
      (andb dependenciesKnownFact
        (andb scopeKnownFact
          (andb acyclicFact
            (andb sourceRevisionValidFact
              (andb policyRevisionValidFact
                (evidenceFactsb evidence))))))).

Definition decideVerificationWorkflow
  (intrinsicAcceptedFact : bool)
  (nodesUniqueFact : bool)
  (dependenciesKnownFact : bool)
  (scopeKnownFact : bool)
  (acyclicFact : bool)
  (sourceRevisionValidFact : bool)
  (policyRevisionValidFact : bool)
  (evidence : list EvidenceFacts) : VerificationWorkflowDecision :=
  if workflowFactsb
      intrinsicAcceptedFact
      nodesUniqueFact
      dependenciesKnownFact
      scopeKnownFact
      acyclicFact
      sourceRevisionValidFact
      policyRevisionValidFact
      evidence
  then VerificationWorkflowAccepted
  else VerificationWorkflowRejected.

Record WorkflowFactReflection
  (graph : VerificationGraph)
  (state : WorkflowState)
  (policy : PolicyRevision)
  (sourceRevisionValid policyRevisionValid : Prop)
  (intrinsicAcceptedFact : bool)
  (nodesUniqueFact : bool)
  (dependenciesKnownFact : bool)
  (scopeKnownFact : bool)
  (acyclicFact : bool)
  (sourceRevisionValidFact : bool)
  (policyRevisionValidFact : bool) : Prop := mkWorkflowFactReflection {
  intrinsicAcceptedFactReflects :
    intrinsicAcceptedFact = true <-> state = WorkflowReady policy;
  nodesUniqueFactReflects :
    nodesUniqueFact = true <-> GraphNodesUnique graph;
  dependenciesKnownFactReflects :
    dependenciesKnownFact = true <-> GraphDependenciesKnown graph;
  scopeKnownFactReflects :
    scopeKnownFact = true <-> GraphScopeKnown graph;
  acyclicFactReflects :
    acyclicFact = true <-> NoDependencyCycle graph;
  sourceRevisionValidFactReflects :
    sourceRevisionValidFact = true <-> sourceRevisionValid;
  policyRevisionValidFactReflects :
    policyRevisionValidFact = true <-> policyRevisionValid
}.

Definition SemanticWorkflowAdmission
  (graph : VerificationGraph)
  (state : WorkflowState)
  (policy : PolicyRevision)
  (sourceRevisionValid policyRevisionValid : Prop)
  (evidence : list EvidenceFacts) : Prop :=
  state = WorkflowReady policy /\
  GraphWellFormed graph /\
  sourceRevisionValid /\
  policyRevisionValid /\
  Forall EvidenceFactsValid evidence.

Theorem workflow_factsb_true_iff_semantic_admission :
  forall graph state policy sourceRevisionValid policyRevisionValid
    intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
    acyclicFact sourceRevisionValidFact policyRevisionValidFact evidence,
    WorkflowFactReflection
      graph state policy sourceRevisionValid policyRevisionValid
      intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
      acyclicFact sourceRevisionValidFact policyRevisionValidFact ->
    (workflowFactsb
      intrinsicAcceptedFact
      nodesUniqueFact
      dependenciesKnownFact
      scopeKnownFact
      acyclicFact
      sourceRevisionValidFact
      policyRevisionValidFact
      evidence = true <->
      SemanticWorkflowAdmission
        graph state policy sourceRevisionValid policyRevisionValid evidence).
Proof.
  intros graph state policy sourceRevisionValid policyRevisionValid
    intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
    acyclicFact sourceRevisionValidFact policyRevisionValidFact evidence
    Hreflection.
  destruct Hreflection as
    [Hintrinsic Hnodes Hdependencies Hscope Hacyclic Hsource Hpolicy].
  unfold workflowFactsb, SemanticWorkflowAdmission.
  repeat rewrite andb_true_iff.
  rewrite Hintrinsic, Hnodes, Hdependencies, Hscope, Hacyclic, Hsource, Hpolicy.
  rewrite evidence_factsb_true_iff_all_valid.
  rewrite graph_well_formed_iff_component_facts.
  tauto.
Qed.

Theorem verification_workflow_decision_accept_iff_facts_true :
  forall intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
    acyclicFact sourceRevisionValidFact policyRevisionValidFact evidence,
    decideVerificationWorkflow
      intrinsicAcceptedFact
      nodesUniqueFact
      dependenciesKnownFact
      scopeKnownFact
      acyclicFact
      sourceRevisionValidFact
      policyRevisionValidFact
      evidence = VerificationWorkflowAccepted <->
    workflowFactsb
      intrinsicAcceptedFact
      nodesUniqueFact
      dependenciesKnownFact
      scopeKnownFact
      acyclicFact
      sourceRevisionValidFact
      policyRevisionValidFact
      evidence = true.
Proof.
  intros intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
    acyclicFact sourceRevisionValidFact policyRevisionValidFact evidence.
  unfold decideVerificationWorkflow.
  destruct (workflowFactsb
    intrinsicAcceptedFact
    nodesUniqueFact
    dependenciesKnownFact
    scopeKnownFact
    acyclicFact
    sourceRevisionValidFact
    policyRevisionValidFact
    evidence) eqn:Hfacts;
    split; intro H; try reflexivity; try discriminate.
Qed.

Theorem verification_workflow_decision_accept_iff_certified_semantics :
  forall graph state policy sourceRevisionValid policyRevisionValid
    intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
    acyclicFact sourceRevisionValidFact policyRevisionValidFact evidence,
    WorkflowFactReflection
      graph state policy sourceRevisionValid policyRevisionValid
      intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
      acyclicFact sourceRevisionValidFact policyRevisionValidFact ->
    (decideVerificationWorkflow
      intrinsicAcceptedFact
      nodesUniqueFact
      dependenciesKnownFact
      scopeKnownFact
      acyclicFact
      sourceRevisionValidFact
      policyRevisionValidFact
      evidence = VerificationWorkflowAccepted <->
      SemanticWorkflowAdmission
        graph state policy sourceRevisionValid policyRevisionValid evidence).
Proof.
  intros graph state policy sourceRevisionValid policyRevisionValid
    intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
    acyclicFact sourceRevisionValidFact policyRevisionValidFact evidence Hreflection.
  split.
  - intros Hdecision.
    apply (proj1
      (workflow_factsb_true_iff_semantic_admission
        graph state policy sourceRevisionValid policyRevisionValid
        intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
        acyclicFact sourceRevisionValidFact policyRevisionValidFact evidence
        Hreflection)).
    apply (proj1
      (verification_workflow_decision_accept_iff_facts_true
        intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
        acyclicFact sourceRevisionValidFact policyRevisionValidFact evidence)).
    exact Hdecision.
  - intros Hsemantic.
    apply (proj2
      (verification_workflow_decision_accept_iff_facts_true
        intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
        acyclicFact sourceRevisionValidFact policyRevisionValidFact evidence)).
    apply (proj2
      (workflow_factsb_true_iff_semantic_admission
        graph state policy sourceRevisionValid policyRevisionValid
        intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
        acyclicFact sourceRevisionValidFact policyRevisionValidFact evidence
        Hreflection)).
    exact Hsemantic.
Qed.

Theorem intrinsic_rejection_cannot_be_workflow_accepted :
  forall nodesUniqueFact dependenciesKnownFact scopeKnownFact acyclicFact
    sourceRevisionValidFact policyRevisionValidFact evidence,
    decideVerificationWorkflow
      false
      nodesUniqueFact
      dependenciesKnownFact
      scopeKnownFact
      acyclicFact
      sourceRevisionValidFact
      policyRevisionValidFact
      evidence = VerificationWorkflowRejected.
Proof.
  intros.
  reflexivity.
Qed.

Theorem one_rejected_evidence_fact_rejects_workflow :
  forall intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
    acyclicFact sourceRevisionValidFact policyRevisionValidFact prefix fact suffix,
    evidenceFactAcceptedb fact = false ->
    decideVerificationWorkflow
      intrinsicAcceptedFact
      nodesUniqueFact
      dependenciesKnownFact
      scopeKnownFact
      acyclicFact
      sourceRevisionValidFact
      policyRevisionValidFact
      (prefix ++ fact :: suffix) = VerificationWorkflowRejected.
Proof.
  intros intrinsicAcceptedFact nodesUniqueFact dependenciesKnownFact scopeKnownFact
    acyclicFact sourceRevisionValidFact policyRevisionValidFact prefix fact suffix Hrejected.
  unfold decideVerificationWorkflow, workflowFactsb.
  assert (Hevidence : evidenceFactsb (prefix ++ fact :: suffix) = false).
  {
    induction prefix as [|head rest IH].
    - cbn.
      rewrite Hrejected.
      reflexivity.
    - cbn.
      destruct (evidenceFactAcceptedb head); cbn.
      + exact IH.
      + reflexivity.
  }
  rewrite Hevidence.
  repeat rewrite andb_false_r.
  reflexivity.
Qed.
