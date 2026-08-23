{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqRecognitionBundles
  ( recognitionBundleSpecs
  ) where

import Phil.Assurance.RocqBundle
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

recognitionBundleSpecs :: [RocqProofBundleSpec]
recognitionBundleSpecs = [commitSpec, failureSpec]

commitSpec :: RocqProofBundleSpec
commitSpec = RocqProofBundleSpec
  { rocqBundleProfile = "core-recognition-commit-bundle"
  , rocqBundleObligation = ObligationId "PHIL-RECOG-COMMIT-001"
  , rocqBundleClaim =
      "A successful commitReceive requires parsed evidence matching the pending receive owner, grammar, and frame; consumes the pending linear capability; rejects successor reuse of ingress identities; and installs exactly the recorded continuation endpoint."
  , rocqBundleKind = "Core recognition commit provenance and resource preservation"
  , rocqBundleOrigin =
      "src/Phil/Core/Recognition.hs::commitReceive; proof/Phil/Core/Recognition.v; proof/Phil/Core/RecognitionLoan.v"
  , rocqBundleScope = "Phil.Core recognition commit including raw-loan exclusion"
  , rocqBundleRepresentation =
      "pending-capability provenance/resource transition plus live-loan exclusion"
  , rocqBundleSubjects = ["PendingCapability", "ParsedWitness", "ResourceContext", "shared raw loan"]
  , rocqBundleParts =
      [ RocqProofPartSpec
          { rocqPartRole = EvidenceRole "recognition_semantics"
          , rocqPartTheorems = ["commitReceive_success_exact"]
          , rocqPartSourceRef = ArtifactRef "proof/Phil/Core/Recognition.v"
          , rocqPartCompiledRef = ArtifactRef "proof/Phil/Core/Recognition.vo"
          , rocqPartCertificateRef = ArtifactRef "certificate:rocq:PHIL-RECOG-COMMIT-001:recognition-semantics:v1"
          , rocqPartEvidenceId = EvidenceEntryId "evidence.PHIL-RECOG-COMMIT-001.recognition-semantics.rocq.v1"
          }
      , RocqProofPartSpec
          { rocqPartRole = EvidenceRole "loan_exclusion"
          , rocqPartTheorems = ["commitReceive_live_raw_loan_rejected"]
          , rocqPartSourceRef = ArtifactRef "proof/Phil/Core/RecognitionLoan.v"
          , rocqPartCompiledRef = ArtifactRef "proof/Phil/Core/RecognitionLoan.vo"
          , rocqPartCertificateRef = ArtifactRef "certificate:rocq:PHIL-RECOG-COMMIT-001:loan-exclusion:v1"
          , rocqPartEvidenceId = EvidenceEntryId "evidence.PHIL-RECOG-COMMIT-001.loan-exclusion.rocq.v1"
          }
      ]
  , rocqBundleResidualBoundary =
      "The trusted recognizer is outside these theorem parts; PendingCapability represents successful pendingSpecFor identification of the exact linear owner. Concrete Haskell finite-map/set and provenance-field correspondence remain implementation boundaries. Both semantic transition authority and live raw-loan exclusion are required by the bundle acceptance rule."
  }

failureSpec :: RocqProofBundleSpec
failureSpec = RocqProofBundleSpec
  { rocqBundleProfile = "core-recognition-failure-bundle"
  , rocqBundleObligation = ObligationId "PHIL-RECOG-FAIL-001"
  , rocqBundleClaim =
      "failPendingRecognition accepts only failure evidence matching the pending owner, grammar, and frame, then consumes the pending linear capability without installing a continuation."
  , rocqBundleKind = "Core recognition failure provenance and fail-closed destruction"
  , rocqBundleOrigin =
      "src/Phil/Core/Recognition.hs::failPendingRecognition; proof/Phil/Core/Recognition.v; proof/Phil/Core/RecognitionLoan.v"
  , rocqBundleScope = "Phil.Core recognition failure including raw-loan exclusion"
  , rocqBundleRepresentation =
      "pending-capability failure provenance/resource transition plus live-loan exclusion"
  , rocqBundleSubjects = ["PendingCapability", "RecognitionFailure", "ResourceContext", "shared raw loan"]
  , rocqBundleParts =
      [ RocqProofPartSpec
          { rocqPartRole = EvidenceRole "recognition_semantics"
          , rocqPartTheorems = ["failPendingRecognition_success_exact"]
          , rocqPartSourceRef = ArtifactRef "proof/Phil/Core/Recognition.v"
          , rocqPartCompiledRef = ArtifactRef "proof/Phil/Core/Recognition.vo"
          , rocqPartCertificateRef = ArtifactRef "certificate:rocq:PHIL-RECOG-FAIL-001:recognition-semantics:v1"
          , rocqPartEvidenceId = EvidenceEntryId "evidence.PHIL-RECOG-FAIL-001.recognition-semantics.rocq.v1"
          }
      , RocqProofPartSpec
          { rocqPartRole = EvidenceRole "loan_exclusion"
          , rocqPartTheorems = ["failPendingRecognition_live_raw_loan_rejected"]
          , rocqPartSourceRef = ArtifactRef "proof/Phil/Core/RecognitionLoan.v"
          , rocqPartCompiledRef = ArtifactRef "proof/Phil/Core/RecognitionLoan.vo"
          , rocqPartCertificateRef = ArtifactRef "certificate:rocq:PHIL-RECOG-FAIL-001:loan-exclusion:v1"
          , rocqPartEvidenceId = EvidenceEntryId "evidence.PHIL-RECOG-FAIL-001.loan-exclusion.rocq.v1"
          }
      ]
  , rocqBundleResidualBoundary =
      "The trusted recognizer is outside these theorem parts; PendingCapability represents successful pendingSpecFor identification of the exact linear owner. Failure detail text is intentionally outside provenance matching. Concrete Haskell finite-map/set and provenance-field correspondence remain implementation boundaries. Both semantic failure authority and live raw-loan exclusion are required by the bundle acceptance rule."
  }
