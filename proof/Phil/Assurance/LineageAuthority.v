From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  PHIL-ASSURE-LINEAGE-001 — revision lineage is provenance, not authority.

  Phil.Assurance distinguishes three relations that must not be conflated:

  - revisionGeneratedFrom records historical/provenance ancestry;
  - evidenceObligationRevision identifies the exact revision established by an
    evidence entry;
  - DependsOnObligation is an explicit cross-revision justification edge.

  Phil.Assurance.Verify checks a generated-from parent only for presence in the
  manifest.  It does not use revisionGeneratedFrom while evaluating an
  acceptance rule.  Acceptance candidates must establish the exact current
  revision, while an explicit DependsOnObligation edge is recursively usable
  only when the depended-on revision is in certification scope and accepted.

  This normalized model proves those authority distinctions.  Concrete
  RevisionId/EvidenceEntryId identity, Data.Map/Data.Set enumeration, acceptance
  rule traversal, and recursive verifier correspondence remain explicit
  implementation boundaries.
*)

Definition RevisionId := nat.
Definition EvidenceId := nat.

Record LineageAuthorityModel : Type := mkLineageAuthorityModel {
  modelManifestRevision : RevisionId -> bool;
  modelCertificationScope : RevisionId -> bool;
  modelGeneratedFrom : RevisionId -> RevisionId -> bool;
  modelEvidenceRevision : EvidenceId -> RevisionId;
  modelEvidenceSelected : EvidenceId -> bool;
  modelEvidenceAccepted : EvidenceId -> bool;
  modelDependsOnObligation : EvidenceId -> RevisionId -> bool;
  modelObligationAccepted : RevisionId -> bool
}.

Definition LineageWellFormed
  (model : LineageAuthorityModel)
  (child : RevisionId) : Prop :=
  forall parent,
    modelGeneratedFrom model child parent = true ->
    modelManifestRevision model parent = true.

Definition ObligationDependencyUsable
  (model : LineageAuthorityModel)
  (evidence : EvidenceId) : Prop :=
  forall parent,
    modelDependsOnObligation model evidence parent = true ->
    modelCertificationScope model parent = true /\
    modelObligationAccepted model parent = true.

Definition EvidenceUsableFor
  (model : LineageAuthorityModel)
  (revision : RevisionId)
  (evidence : EvidenceId) : Prop :=
  modelEvidenceSelected model evidence = true /\
  modelEvidenceAccepted model evidence = true /\
  modelEvidenceRevision model evidence = revision /\
  ObligationDependencyUsable model evidence.

Definition RevisionAccepted
  (model : LineageAuthorityModel)
  (revision : RevisionId) : Prop :=
  exists evidence, EvidenceUsableFor model revision evidence.

Theorem lineage_parent_must_exist_in_manifest :
  forall model child parent,
    LineageWellFormed model child ->
    modelGeneratedFrom model child parent = true ->
    modelManifestRevision model parent = true.
Proof.
  intros model child parent Hlineage Hgenerated.
  eapply Hlineage.
  exact Hgenerated.
Qed.

Theorem accepted_revision_requires_exact_revision_evidence :
  forall model revision,
    RevisionAccepted model revision ->
    exists evidence,
      modelEvidenceSelected model evidence = true /\
      modelEvidenceAccepted model evidence = true /\
      modelEvidenceRevision model evidence = revision.
Proof.
  intros model revision Haccepted.
  destruct Haccepted as [evidence [Hselected [Hresult [Hexact _]]]].
  exists evidence.
  split.
  - exact Hselected.
  - split.
    + exact Hresult.
    + exact Hexact.
Qed.

Theorem ancestor_evidence_cannot_satisfy_distinct_child :
  forall model child parent evidence,
    child <> parent ->
    modelEvidenceRevision model evidence = parent ->
    ~ EvidenceUsableFor model child evidence.
Proof.
  intros model child parent evidence Hdistinct Hparent Hevidence.
  destruct Hevidence as [_ [_ [Hchild _]]].
  rewrite Hparent in Hchild.
  apply Hdistinct.
  symmetry.
  exact Hchild.
Qed.

Theorem explicit_obligation_dependency_requires_in_scope_accepted_parent :
  forall model child evidence parent,
    EvidenceUsableFor model child evidence ->
    modelDependsOnObligation model evidence parent = true ->
    modelCertificationScope model parent = true /\
    modelObligationAccepted model parent = true.
Proof.
  intros model child evidence parent Hevidence Hdependency.
  destruct Hevidence as [_ [_ [_ Husable]]].
  eapply Husable.
  exact Hdependency.
Qed.

Theorem out_of_scope_parent_cannot_be_justification_authority :
  forall model child evidence parent,
    modelCertificationScope model parent = false ->
    modelDependsOnObligation model evidence parent = true ->
    ~ EvidenceUsableFor model child evidence.
Proof.
  intros model child evidence parent Hout Hdependency Hevidence.
  pose proof
    (explicit_obligation_dependency_requires_in_scope_accepted_parent
      model child evidence parent Hevidence Hdependency)
    as [Hscope _].
  rewrite Hout in Hscope.
  discriminate.
Qed.

(* A fixed witness that contains lineage but no evidence authority. *)
Definition LineageOnlyModel : LineageAuthorityModel :=
  mkLineageAuthorityModel
    (fun revision =>
      match revision with
      | 0 => true
      | 1 => true
      | _ => false
      end)
    (fun _ => false)
    (fun child parent =>
      match child, parent with
      | 1, 0 => true
      | _, _ => false
      end)
    (fun _ => 0)
    (fun _ => false)
    (fun _ => false)
    (fun _ _ => false)
    (fun _ => false).

Theorem lineage_only_model_is_well_formed :
  LineageWellFormed LineageOnlyModel 1.
Proof.
  intros parent Hgenerated.
  destruct parent; simpl in *.
  - reflexivity.
  - discriminate.
Qed.

Theorem lineage_alone_does_not_establish_child_authority :
  modelGeneratedFrom LineageOnlyModel 1 0 = true /\
  ~ RevisionAccepted LineageOnlyModel 1.
Proof.
  split.
  - reflexivity.
  - intros [evidence Hevidence].
    destruct Hevidence as [Hselected _].
    simpl in Hselected.
    discriminate.
Qed.

(* Historical ancestry may remain in the manifest while outside certification
   scope, provided it is not used as a justification dependency. *)
Definition HistoricalLineageModel : LineageAuthorityModel :=
  mkLineageAuthorityModel
    (fun revision =>
      match revision with
      | 0 => true
      | 1 => true
      | _ => false
      end)
    (fun revision =>
      match revision with
      | 1 => true
      | _ => false
      end)
    (fun child parent =>
      match child, parent with
      | 1, 0 => true
      | _, _ => false
      end)
    (fun evidence =>
      match evidence with
      | 10 => 1
      | _ => 0
      end)
    (fun evidence =>
      match evidence with
      | 10 => true
      | _ => false
      end)
    (fun evidence =>
      match evidence with
      | 10 => true
      | _ => false
      end)
    (fun _ _ => false)
    (fun revision =>
      match revision with
      | 1 => true
      | _ => false
      end).

Theorem historical_lineage_model_is_well_formed :
  LineageWellFormed HistoricalLineageModel 1.
Proof.
  intros parent Hgenerated.
  destruct parent; simpl in *.
  - reflexivity.
  - discriminate.
Qed.

Theorem exported_historical_ancestor_can_coexist_with_child_authority :
  modelGeneratedFrom HistoricalLineageModel 1 0 = true /\
  modelManifestRevision HistoricalLineageModel 0 = true /\
  modelCertificationScope HistoricalLineageModel 0 = false /\
  RevisionAccepted HistoricalLineageModel 1.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * exists 10.
        unfold EvidenceUsableFor.
        split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ split.
              ** reflexivity.
              ** intros parent Hdependency.
                 simpl in Hdependency.
                 discriminate.
Qed.

(* Conversely, explicit justification can be usable without any generated-from
   relation: semantic dependency and historical derivation are independent. *)
Definition ExplicitDependencyModel : LineageAuthorityModel :=
  mkLineageAuthorityModel
    (fun revision =>
      match revision with
      | 0 => true
      | 1 => true
      | _ => false
      end)
    (fun revision =>
      match revision with
      | 0 => true
      | 1 => true
      | _ => false
      end)
    (fun _ _ => false)
    (fun evidence =>
      match evidence with
      | 10 => 1
      | _ => 0
      end)
    (fun evidence =>
      match evidence with
      | 10 => true
      | _ => false
      end)
    (fun evidence =>
      match evidence with
      | 10 => true
      | _ => false
      end)
    (fun evidence parent =>
      match evidence, parent with
      | 10, 0 => true
      | _, _ => false
      end)
    (fun revision =>
      match revision with
      | 0 => true
      | _ => false
      end).

Theorem explicit_justification_does_not_require_lineage :
  modelGeneratedFrom ExplicitDependencyModel 1 0 = false /\
  modelDependsOnObligation ExplicitDependencyModel 10 0 = true /\
  EvidenceUsableFor ExplicitDependencyModel 1 10.
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + unfold EvidenceUsableFor.
      split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros parent Hdependency.
              destruct parent; simpl in *.
              ** split; reflexivity.
              ** discriminate.
Qed.
