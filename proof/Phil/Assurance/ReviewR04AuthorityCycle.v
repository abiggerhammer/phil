From Stdlib Require Import Bool.Bool.

From Phil.Assurance Require Import Manifest LineageAuthority.

(*
  PHIL-P1-REVIEW-R04 — provenance lineage must never become justification
  authority, and genuine justification cycles must remain fail-closed.

  This aggregate proof composes two already-Certified assurance boundaries:
  PHIL-ASSURE-LINEAGE-001 and PHIL-ASSURE-GRAPH-001.

  revisionGeneratedFrom may record ancestry and require that the ancestor remain
  present, but an ancestor's evidence cannot establish a distinct child
  revision merely because of that lineage relation.  Genuine proof/evidence
  dependencies are separate justification edges, and an accepted assurance
  graph cannot contain a self-cycle or two-way cycle.

  Concrete RevisionId/EvidenceEntryId/Digest representation, Data.Map/Data.Set
  traversal, diagnostic ordering, and the Haskell verifier correspondence
  remain explicit implementation boundaries.
*)

Theorem review_r04_ancestor_evidence_cannot_authorize_distinct_child :
  forall
    (model : LineageAuthority.LineageAuthorityModel)
    (child parent : LineageAuthority.RevisionId)
    (evidence : LineageAuthority.EvidenceId),
    child <> parent ->
    LineageAuthority.modelEvidenceRevision model evidence = parent ->
    ~ LineageAuthority.EvidenceUsableFor model child evidence.
Proof.
  intros model child parent evidence Hdistinct Hparent.
  eapply LineageAuthority.ancestor_evidence_cannot_satisfy_distinct_child.
  - exact Hdistinct.
  - exact Hparent.
Qed.

Theorem review_r04_lineage_alone_does_not_establish_authority :
  LineageAuthority.modelGeneratedFrom
      LineageAuthority.LineageOnlyModel 1 0 = true /\
  ~ LineageAuthority.RevisionAccepted
      LineageAuthority.LineageOnlyModel 1.
Proof.
  exact LineageAuthority.lineage_alone_does_not_establish_child_authority.
Qed.

Theorem review_r04_verified_justification_graph_has_no_self_cycle :
  forall
    (edge : Manifest.GraphNode -> Manifest.GraphNode -> Prop)
    (node : Manifest.GraphNode),
    Manifest.GraphVerificationSuccess edge ->
    ~ edge node node.
Proof.
  intros edge node Hverified.
  eapply Manifest.verified_graph_has_no_self_edge.
  exact Hverified.
Qed.

Theorem review_r04_verified_justification_graph_has_no_two_way_cycle :
  forall
    (edge : Manifest.GraphNode -> Manifest.GraphNode -> Prop)
    (left right : Manifest.GraphNode),
    Manifest.GraphVerificationSuccess edge ->
    edge left right ->
    ~ edge right left.
Proof.
  intros edge left right Hverified Hforward.
  eapply Manifest.verified_graph_has_no_two_node_cycle.
  - exact Hverified.
  - exact Hforward.
Qed.

Theorem review_r04_recursive_revisit_is_rejected :
  forall
    (visiting : Manifest.VisitingSet)
    (node : Manifest.GraphNode),
    visiting node = true ->
    Manifest.guardVisit visiting node = Manifest.VisitRejected.
Proof.
  intros visiting node Hvisited.
  eapply Manifest.revisited_node_is_never_entered_as_justification.
  exact Hvisited.
Qed.

Theorem review_r04_provenance_and_justification_are_separate :
  forall
    (model : LineageAuthority.LineageAuthorityModel)
    (child parent : LineageAuthority.RevisionId)
    (evidence : LineageAuthority.EvidenceId)
    (edge : Manifest.GraphNode -> Manifest.GraphNode -> Prop)
    (left right : Manifest.GraphNode),
    child <> parent ->
    LineageAuthority.modelEvidenceRevision model evidence = parent ->
    Manifest.GraphVerificationSuccess edge ->
    edge left right ->
    (~ LineageAuthority.EvidenceUsableFor model child evidence) /\
    (~ edge right left).
Proof.
  intros model child parent evidence edge left right
    Hdistinct Hparent Hverified Hforward.
  split.
  - eapply review_r04_ancestor_evidence_cannot_authorize_distinct_child; eauto.
  - eapply review_r04_verified_justification_graph_has_no_two_way_cycle; eauto.
Qed.
