From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.
Import ListNotations.

(*
  Proof-oriented model of the authority-bearing core of Phil.Assurance.Verify.

  This slice intentionally does not formalize SHA-256, Data.Map/Data.Set, or
  artifact semantics.  It proves the manifest verifier's authority algebra:

  - the trusted obligation set is closed by either local certification or one
    explicit permitted export, never by silently treating export as truth;
  - acceptance rules are structurally non-vacuous and entry acceptance requires
    selected, exact-match, accepted, recursively usable evidence;
  - assurance-justification graphs are acyclic, and the recursive usability
    guard rejects revisiting a node rather than treating recursion as proof.

  Concrete identifier/digest correspondence remains a separately tracked
  implementation boundary.
*)

Definition RevisionId := nat.
Definition EvidenceId := nat.
Definition BoundaryId := nat.
Definition RevisionSet := RevisionId -> bool.
Definition BoundarySet := BoundaryId -> bool.
Definition EvidenceSet := EvidenceId -> bool.

Definition SameRevisionSet (left right : RevisionSet) : Prop :=
  forall revision, left revision = right revision.

(* -------------------------------------------------------------------------- *)
(* PHIL-ASSURE-SCOPE-001 — certification-scope closure.                       *)
(* -------------------------------------------------------------------------- *)

Inductive RevisionDisposition : Type :=
| LocallyAccepted
| ExplicitlyExported : BoundaryId -> RevisionDisposition
| UnresolvedRevision.

Record ScopeModel : Type := mkScopeModel {
  trustedExpectedRevisions : RevisionSet;
  manifestRevisions : RevisionSet;
  certificationScope : RevisionSet;
  permittedExportBoundaries : BoundarySet;
  revisionDisposition : RevisionId -> RevisionDisposition;
  selectedEvidence : EvidenceSet;
  evidenceDependsOnRevision : EvidenceId -> RevisionId -> Prop
}.

Definition CertificationClosure (model : ScopeModel) : Prop :=
  SameRevisionSet
    (trustedExpectedRevisions model)
    (manifestRevisions model) /\
  (forall revision,
    certificationScope model revision = true ->
    manifestRevisions model revision = true) /\
  (forall revision,
    manifestRevisions model revision = true ->
    certificationScope model revision = true ->
    revisionDisposition model revision = LocallyAccepted) /\
  (forall revision,
    manifestRevisions model revision = true ->
    certificationScope model revision = false ->
    exists boundary,
      revisionDisposition model revision = ExplicitlyExported boundary /\
      permittedExportBoundaries model boundary = true) /\
  (forall evidence revision,
    selectedEvidence model evidence = true ->
    evidenceDependsOnRevision model evidence revision ->
    certificationScope model revision = true).

Theorem verified_manifest_covers_exact_trusted_revision_set :
  forall model,
    CertificationClosure model ->
    SameRevisionSet
      (trustedExpectedRevisions model)
      (manifestRevisions model).
Proof.
  intros model Hclosure.
  destruct Hclosure as [Hexact _].
  exact Hexact.
Qed.

Theorem certification_scope_is_inside_manifest :
  forall model revision,
    CertificationClosure model ->
    certificationScope model revision = true ->
    manifestRevisions model revision = true.
Proof.
  intros model revision Hclosure Hscope.
  destruct Hclosure as [_ [Hsubset _]].
  apply Hsubset.
  exact Hscope.
Qed.

Theorem in_scope_revision_is_locally_accepted :
  forall model revision,
    CertificationClosure model ->
    certificationScope model revision = true ->
    revisionDisposition model revision = LocallyAccepted.
Proof.
  intros model revision Hclosure Hscope.
  destruct Hclosure as [_ [Hsubset [Hlocal _]]].
  apply Hlocal.
  - apply Hsubset. exact Hscope.
  - exact Hscope.
Qed.

Theorem in_scope_revision_is_not_exported :
  forall model revision boundary,
    CertificationClosure model ->
    certificationScope model revision = true ->
    revisionDisposition model revision <> ExplicitlyExported boundary.
Proof.
  intros model revision boundary Hclosure Hscope Hexported.
  pose proof (in_scope_revision_is_locally_accepted model revision Hclosure Hscope)
    as Hlocal.
  rewrite Hlocal in Hexported.
  discriminate.
Qed.

Theorem out_of_scope_manifest_revision_has_permitted_export :
  forall model revision,
    CertificationClosure model ->
    manifestRevisions model revision = true ->
    certificationScope model revision = false ->
    exists boundary,
      revisionDisposition model revision = ExplicitlyExported boundary /\
      permittedExportBoundaries model boundary = true.
Proof.
  intros model revision Hclosure Hmanifest Hscope.
  destruct Hclosure as [_ [_ [_ [Hexport _]]]].
  eapply Hexport; eauto.
Qed.

Theorem out_of_scope_export_is_unique :
  forall model revision left right,
    revisionDisposition model revision = ExplicitlyExported left ->
    revisionDisposition model revision = ExplicitlyExported right ->
    left = right.
Proof.
  intros model revision left right Hleft Hright.
  rewrite Hleft in Hright.
  inversion Hright.
  reflexivity.
Qed.

Theorem selected_evidence_cannot_depend_on_exported_revision_as_truth :
  forall model evidence revision boundary,
    CertificationClosure model ->
    selectedEvidence model evidence = true ->
    evidenceDependsOnRevision model evidence revision ->
    revisionDisposition model revision = ExplicitlyExported boundary ->
    False.
Proof.
  intros model evidence revision boundary Hclosure Hselected Hdepends Hexported.
  destruct Hclosure as [_ [_ [_ [_ Hdependency]]]].
  pose proof (Hdependency evidence revision Hselected Hdepends) as Hscope.
  pose proof (in_scope_revision_is_not_exported
    model revision boundary Hclosure Hscope) as HnotExported.
  contradiction.
Qed.

(* -------------------------------------------------------------------------- *)
(* PHIL-ASSURE-ACCEPT-001 — non-vacuous evidence acceptance.                  *)
(* -------------------------------------------------------------------------- *)

Inductive AssuranceKind : Type :=
| KernelKind
| ProofKind
| CertificateKind
| TranslationKind
| DifferentialKind
| PropertyKind
| RuntimeKind
| AssumedKind.

Definition EvidenceRole := nat.

Inductive AcceptanceRule : Type :=
| AcceptEntry : AssuranceKind -> EvidenceRole -> AcceptanceRule
| AcceptAll : list AcceptanceRule -> AcceptanceRule
| AcceptAny : list AcceptanceRule -> AcceptanceRule.

Inductive ValidAcceptanceRule : AcceptanceRule -> Prop :=
| ValidEntry : forall kind role,
    role <> 0 ->
    ValidAcceptanceRule (AcceptEntry kind role)
| ValidAll : forall rules,
    rules <> [] ->
    Forall ValidAcceptanceRule rules ->
    ValidAcceptanceRule (AcceptAll rules)
| ValidAny : forall rules,
    rules <> [] ->
    Forall ValidAcceptanceRule rules ->
    ValidAcceptanceRule (AcceptAny rules).

Record EvidenceEntry : Type := mkEvidenceEntry {
  entryRevision : RevisionId;
  entryKind : AssuranceKind;
  entryRole : EvidenceRole;
  entrySelected : bool;
  entryAccepted : bool;
  entryDependenciesUsable : bool
}.

Definition EvidenceEnvironment := EvidenceId -> option EvidenceEntry.

Definition MatchingUsableEvidence
  (environment : EvidenceEnvironment)
  (revision : RevisionId)
  (kind : AssuranceKind)
  (role : EvidenceRole)
  (evidence : EvidenceId) : Prop :=
  exists entry,
    environment evidence = Some entry /\
    entrySelected entry = true /\
    entryRevision entry = revision /\
    entryKind entry = kind /\
    entryRole entry = role /\
    entryAccepted entry = true /\
    entryDependenciesUsable entry = true.

Inductive RuleSatisfied
  (environment : EvidenceEnvironment)
  (revision : RevisionId) : AcceptanceRule -> Prop :=
| SatisfiedEntry : forall kind role evidence,
    MatchingUsableEvidence environment revision kind role evidence ->
    RuleSatisfied environment revision (AcceptEntry kind role)
| SatisfiedAll : forall rules,
    rules <> [] ->
    Forall (RuleSatisfied environment revision) rules ->
    RuleSatisfied environment revision (AcceptAll rules)
| SatisfiedAny : forall rules rule,
    rules <> [] ->
    In rule rules ->
    RuleSatisfied environment revision rule ->
    RuleSatisfied environment revision (AcceptAny rules).

Definition AcceptanceCheckSuccess
  (environment : EvidenceEnvironment)
  (revision : RevisionId)
  (rule : AcceptanceRule) : Prop :=
  ValidAcceptanceRule rule /\
  RuleSatisfied environment revision rule.

Theorem empty_all_acceptance_rule_is_invalid :
  ~ ValidAcceptanceRule (AcceptAll []).
Proof.
  intro Hvalid.
  inversion Hvalid.
  contradiction.
Qed.

Theorem empty_any_acceptance_rule_is_invalid :
  ~ ValidAcceptanceRule (AcceptAny []).
Proof.
  intro Hvalid.
  inversion Hvalid.
  contradiction.
Qed.

Theorem accepted_entry_requires_selected_exact_usable_evidence :
  forall environment revision kind role,
    AcceptanceCheckSuccess
      environment revision (AcceptEntry kind role) ->
    exists evidence,
      MatchingUsableEvidence environment revision kind role evidence.
Proof.
  intros environment revision kind role Hsuccess.
  destruct Hsuccess as [_ Hsatisfied].
  inversion Hsatisfied; subst.
  exists evidence.
  assumption.
Qed.

Theorem matching_evidence_is_selected :
  forall environment revision kind role evidence,
    MatchingUsableEvidence environment revision kind role evidence ->
    exists entry,
      environment evidence = Some entry /\
      entrySelected entry = true.
Proof.
  intros environment revision kind role evidence Hmatching.
  destruct Hmatching as
    [entry [Hlookup [Hselected _]]].
  exists entry.
  split; assumption.
Qed.

Theorem matching_evidence_is_accepted :
  forall environment revision kind role evidence,
    MatchingUsableEvidence environment revision kind role evidence ->
    exists entry,
      environment evidence = Some entry /\
      entryAccepted entry = true.
Proof.
  intros environment revision kind role evidence Hmatching.
  destruct Hmatching as
    [entry [Hlookup [_ [_ [_ [_ [Haccepted _]]]]]]].
  exists entry.
  split; assumption.
Qed.

Theorem matching_evidence_has_usable_dependencies :
  forall environment revision kind role evidence,
    MatchingUsableEvidence environment revision kind role evidence ->
    exists entry,
      environment evidence = Some entry /\
      entryDependenciesUsable entry = true.
Proof.
  intros environment revision kind role evidence Hmatching.
  destruct Hmatching as
    [entry [Hlookup [_ [_ [_ [_ [_ Hdependencies]]]]]]].
  exists entry.
  split; assumption.
Qed.

Theorem rejected_evidence_cannot_match :
  forall environment revision kind role evidence entry,
    environment evidence = Some entry ->
    entryAccepted entry = false ->
    ~ MatchingUsableEvidence environment revision kind role evidence.
Proof.
  intros environment revision kind role evidence entry Hlookup Hrejected Hmatching.
  destruct Hmatching as
    [matched [HmatchedLookup [_ [_ [_ [_ [Haccepted _]]]]]]].
  rewrite Hlookup in HmatchedLookup.
  inversion HmatchedLookup; subst matched.
  rewrite Hrejected in Haccepted.
  discriminate.
Qed.

Theorem unselected_evidence_cannot_match :
  forall environment revision kind role evidence entry,
    environment evidence = Some entry ->
    entrySelected entry = false ->
    ~ MatchingUsableEvidence environment revision kind role evidence.
Proof.
  intros environment revision kind role evidence entry Hlookup Hunselected Hmatching.
  destruct Hmatching as
    [matched [HmatchedLookup [Hselected _]]].
  rewrite Hlookup in HmatchedLookup.
  inversion HmatchedLookup; subst matched.
  rewrite Hunselected in Hselected.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* PHIL-ASSURE-GRAPH-001 — justification acyclicity.                          *)
(* -------------------------------------------------------------------------- *)

Inductive GraphNode : Type :=
| ObligationNode : RevisionId -> GraphNode
| EvidenceNode : EvidenceId -> GraphNode.

Inductive Reachable
  (edge : GraphNode -> GraphNode -> Prop) : GraphNode -> GraphNode -> Prop :=
| Reachable_step : forall source target,
    edge source target ->
    Reachable edge source target
| Reachable_more : forall source middle target,
    edge source middle ->
    Reachable edge middle target ->
    Reachable edge source target.

Definition HasCycle (edge : GraphNode -> GraphNode -> Prop) : Prop :=
  exists node, Reachable edge node node.

Definition Acyclic (edge : GraphNode -> GraphNode -> Prop) : Prop :=
  ~ HasCycle edge.

Record GraphVerificationSuccess
  (edge : GraphNode -> GraphNode -> Prop) : Prop := mkGraphVerificationSuccess {
  verifiedAcyclic : Acyclic edge
}.

Theorem verified_graph_has_no_self_edge :
  forall edge node,
    GraphVerificationSuccess edge ->
    ~ edge node node.
Proof.
  intros edge node Hverified Hself.
  destruct Hverified as [Hacyclic].
  apply Hacyclic.
  exists node.
  apply Reachable_step.
  exact Hself.
Qed.

Theorem verified_graph_has_no_two_node_cycle :
  forall edge left right,
    GraphVerificationSuccess edge ->
    edge left right ->
    ~ edge right left.
Proof.
  intros edge left right Hverified HleftRight HrightLeft.
  destruct Hverified as [Hacyclic].
  apply Hacyclic.
  exists left.
  eapply Reachable_more.
  - exact HleftRight.
  - apply Reachable_step. exact HrightLeft.
Qed.

Definition VisitingSet := GraphNode -> bool.

Inductive VisitGuardResult : Type :=
| VisitRejected
| VisitEntered.

Definition guardVisit (visiting : VisitingSet) (node : GraphNode) : VisitGuardResult :=
  if visiting node then VisitRejected else VisitEntered.

Theorem revisited_node_is_never_entered_as_justification :
  forall visiting node,
    visiting node = true ->
    guardVisit visiting node = VisitRejected.
Proof.
  intros visiting node Hvisited.
  unfold guardVisit.
  rewrite Hvisited.
  reflexivity.
Qed.

Theorem successful_visit_implies_node_was_not_already_visiting :
  forall visiting node,
    guardVisit visiting node = VisitEntered ->
    visiting node = false.
Proof.
  intros visiting node Hguard.
  unfold guardVisit in Hguard.
  destruct (visiting node) eqn:Hvisited.
  - discriminate.
  - reflexivity.
Qed.
