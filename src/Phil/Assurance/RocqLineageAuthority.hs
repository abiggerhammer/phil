{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqLineageAuthority
  ( lineageAuthorityCertificationSpec
  ) where

import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

lineageAuthorityCertificationSpec :: RocqCertificationSpec
lineageAuthorityCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "assurance-lineage-authority"
  , rocqSpecObligation = ObligationId "PHIL-ASSURE-LINEAGE-001"
  , rocqSpecClaim =
      "Revision lineage is provenance rather than justification authority. A revisionGeneratedFrom parent is required to exist in the manifest, but ancestry alone cannot satisfy the child's acceptance rule: accepted child authority requires selected accepted evidence whose evidenceObligationRevision is the exact child revision. Cross-revision justification exists only through explicit DependsOnObligation edges; such dependencies require the parent revision to be in certification scope and accepted. Consequently an exported/out-of-scope ancestor may remain valid historical lineage but cannot simultaneously serve as justification authority, while an explicit semantic dependency may be valid without a generated-from relation."
  , rocqSpecKind = "Assurance lineage / justification separation"
  , rocqSpecOrigin =
      "src/Phil/Assurance/Types.hs; src/Phil/Assurance/Verify.hs; proof/Phil/Assurance/LineageAuthority.v"
  , rocqSpecScope =
      "Phil.Assurance revisionGeneratedFrom, evidenceObligationRevision, and DependsOnObligation authority relations"
  , rocqSpecRepresentation =
      "normalized manifest-lineage, exact-revision evidence, and explicit obligation-dependency model"
  , rocqSpecSubjects =
      [ "ObligationRevision.revisionGeneratedFrom"
      , "EvidenceEntry.evidenceObligationRevision"
      , "EvidenceEntry.evidenceDependsOn"
      , "DependsOnObligation"
      , "manifestCertificationScope"
      ]
  , rocqSpecTheorems =
      [ "lineage_parent_must_exist_in_manifest"
      , "accepted_revision_requires_exact_revision_evidence"
      , "ancestor_evidence_cannot_satisfy_distinct_child"
      , "explicit_obligation_dependency_requires_in_scope_accepted_parent"
      , "out_of_scope_parent_cannot_be_justification_authority"
      , "lineage_only_model_is_well_formed"
      , "lineage_alone_does_not_establish_child_authority"
      , "historical_lineage_model_is_well_formed"
      , "exported_historical_ancestor_can_coexist_with_child_authority"
      , "explicit_justification_does_not_require_lineage"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Assurance/LineageAuthority.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Assurance/LineageAuthority.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-ASSURE-LINEAGE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-ASSURE-LINEAGE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from Haskell RevisionId/EvidenceEntryId identity, revisionGeneratedFrom manifest-membership checks, exact evidenceObligationRevision filtering, acceptance-rule evaluation, recursive DependsOnObligation usability, Data.Map/Data.Set enumeration, and export/certification-scope handling to the normalized proof model remain explicit trust boundaries. The theorem establishes authority separation; it does not assert that every semantic dependency must also be revision ancestry or vice versa."
  }
