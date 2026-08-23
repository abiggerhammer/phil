{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqValidityScope
  ( validityScopeCertificationSpec
  , knownValidityScopeRocqCertificationSpec
  ) where

import Data.Text (Text)
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

validityScopeCertificationSpec :: RocqCertificationSpec
validityScopeCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "assurance-validity-scope"
  , rocqSpecObligation = ObligationId "PHIL-ASSURE-VALIDITY-001"
  , rocqSpecClaim =
      "ValidityScope authority is exact for every dimension the authority binds: successful scope matching requires the effective context to carry the exact expected value for each bound dimension, so changing any bound dimension prevents reuse; target and compilation-profile changes therefore invalidate evidence that explicitly binds those dimensions. Unbound effective-context dimensions carry no authority and may change without invalidating the scope. Strengthening a scope only adds requirements: a stronger matching scope implies its weaker subset matches, while a newly bound mismatching dimension cannot be excused."
  , rocqSpecKind = "Assurance validity-scope authority"
  , rocqSpecOrigin =
      "src/Phil/Assurance/Verify.hs; test/AssuranceMain.hs; proof/Phil/Assurance/ValidityScope.v"
  , rocqSpecScope = "Phil.Assurance.Verify scopeMatches / ValidityScope"
  , rocqSpecRepresentation =
      "partial dimension map whose bound key/value pairs must all match the effective validity context"
  , rocqSpecSubjects =
      [ "ValidityScope"
      , "effective manifest validity context"
      , "target dimension"
      , "compilation_profile dimension"
      , "scope strengthening"
      ]
  , rocqSpecTheorems =
      [ "matching_scope_preserves_every_bound_dimension"
      , "changed_bound_dimension_cannot_match"
      , "evidence_cannot_cross_changed_bound_dimension"
      , "bound_target_change_invalidates_authority"
      , "bound_compilation_profile_change_invalidates_authority"
      , "unbound_dimension_change_preserves_match"
      , "stronger_scope_match_implies_weaker_scope_match"
      , "strengthening_scope_cannot_excuse_new_mismatch"
      , "empty_scope_matches_every_context"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Assurance/ValidityScope.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Assurance/ValidityScope.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-ASSURE-VALIDITY-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-ASSURE-VALIDITY-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from Haskell Data.Map Text dimensions and Phil.Assurance.Verify.scopeMatches to the normalized partial-map model remain explicit trust boundaries. The theorem does not claim that unbound context dimensions are irrelevant to other verifier gates; it establishes only the authority carried by ValidityScope itself."
  }

knownValidityScopeRocqCertificationSpec :: Text -> Maybe RocqCertificationSpec
knownValidityScopeRocqCertificationSpec profile
  | profile == rocqSpecProfile validityScopeCertificationSpec =
      Just validityScopeCertificationSpec
  | otherwise = Nothing
