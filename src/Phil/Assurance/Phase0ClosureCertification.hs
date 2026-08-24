{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.Phase0ClosureCertification
  ( Phase0ClosureCertificationError (..)
  , Phase0ClosureCertificationBundle (..)
  , phase0ClosureCertification
  , verifyPhase0ClosureCertification
  , renderPhase0ClosureCertification
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.IntegratedNativeUploadTestEvidence
import Phil.Assurance.TestEvidenceCertification
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..), unObligationId)

data Phase0ClosureCertificationError
  = Phase0ClosureWrongRuntimeTest ObligationId ObligationId
  | Phase0ClosureRuntimeManifestError ManifestError
  | Phase0ClosureFinalManifestError ManifestError
  deriving (Eq, Show)

data Phase0ClosureCertificationBundle = Phase0ClosureCertificationBundle
  { phase0ClosureRuntimeTestArtifact :: ArtifactIdentity
  , phase0ClosureArtifact :: ArtifactIdentity
  , phase0ClosureRecord :: Text
  , phase0ClosureLedger :: AssuranceLedger
  , phase0ClosureManifest :: AssuranceManifest
  , phase0ClosureContext :: VerificationContext
  }
  deriving (Eq, Show)

proofBoundCert018 :: ArtifactIdentity
proofBoundCert018 = ArtifactIdentity
  { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-018:v1"
  , artifactDigest = Digest "1705fb11d2cdf30fef1bfdeab7d62b56cbc2c4751fb13251fa5b124057564c96"
  }

phase0SourcePairDigest :: Digest
phase0SourcePairDigest =
  Digest "5339e6c7e6520e5495c1d304edcc2427e4bdbe19ce80167af3a314ab2f69e4df"

phase0ClosureCertification
  :: TestEvidenceCertificationBundle
  -> Either Phase0ClosureCertificationError Phase0ClosureCertificationBundle
phase0ClosureCertification runtimeTest = do
  verifyRuntimeTest runtimeTest

  let runtimeCertificate = testBundleCertificate runtimeTest
      runtimeRevisionId = testCertificateRevision runtimeCertificate
      runtimeArtifact = testBundleCertificateArtifact runtimeTest
      runtimeDigest = artifactDigest runtimeArtifact
      runtimeLedger = testBundleLedger runtimeTest
      runtimeManifest = testBundleManifest runtimeTest
      runtimeValidity = validityDimensions (testCertificateValidity runtimeCertificate)
      validityContext = Map.union runtimeValidity (Map.fromList
        [ ("phase0_closure_profile", "frozen-reference-upload/native-in-memory/v1")
        , ("source_pair_digest", unDigest phase0SourcePairDigest)
        , ("source_projection", "surface-to-systems/phase0-upload/v1")
        , ("predecessor_cert018", unDigest (artifactDigest proofBoundCert018))
        , ("runtime_test_certificate", unDigest runtimeDigest)
        , ("runtime_test_revision", unRevisionId runtimeRevisionId)
        , ("closure_semantics", "CERT-018 source-bound authority + exact DifferentialTested native execution evidence")
        , ("generic_runtime_correctness", "not claimed")
        , ("production_networking", "not claimed")
        , ("crash_durability", "not claimed")
        ])
      closureScope = ValidityScope validityContext
      revisionStatement =
        "Phase 0 for the frozen UploadClient/UploadServer reference program may be labeled Certified closed only when proof-bound PHIL-LLVM-CERT-018 supplies the exact source-pair-to-control-codec-v1 translation authority and a separately manifest-verified PHIL-RUNTIME-INTEGRATED-UPLOAD-001 certificate binds the exact full-ABI/native accepted-upload, digest-rejection, and client-cancellation fixture execution. This closure is limited to the declared x86_64 in-memory native fixture and does not claim generic Phil source lowering, universal runtime correctness, production networking, crash durability, filesystem persistence, scheduler guarantees, cryptographic implementation correctness, or remote receipt."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-PHASE0-CERT-001"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "Phase 0 reference-program closure certification"
        , revisionOrigin =
            "PHIL-LLVM-CERT-018 + PHIL-RUNTIME-INTEGRATED-UPLOAD-001 / frozen Phase 0 upload reference program"
        , revisionScope =
            "frozen Phase 0 UploadClient/UploadServer; x86_64-unknown-linux-gnu; in-memory integrated native fixture"
        , revisionRequiredAt = "phase0-freeze"
        , revisionRepresentation =
            "proof-bound source-to-LLVM authority + content-bound DifferentialTested native execution certificate"
        , revisionSubjectIds =
            [ "source-pair:" <> unDigest phase0SourcePairDigest
            , "predecessor-cert018:" <> unDigest (artifactDigest proofBoundCert018)
            , "runtime-test-certificate:" <> unDigest runtimeDigest
            , "runtime-test-revision:" <> unRevisionId runtimeRevisionId
            ]
        , revisionContextIds =
            [ key <> "=" <> value
            | (key, value) <- Map.toAscList validityContext
            ]
        , revisionAcceptanceRule =
            AcceptEntry CertificateChecked (EvidenceRole "phase0_closure")
        , revisionGeneratedFrom = [runtimeRevisionId]
        }
      closureRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      closureRevisionId = revisionId closureRevision
      closureRecord = Text.unlines
        [ "phil-phase0-reference-closure-certification/v1"
        , "obligation=PHIL-PHASE0-CERT-001"
        , "revision=" <> unRevisionId closureRevisionId
        , "source-pair-digest=" <> unDigest phase0SourcePairDigest
        , "source-projection=surface-to-systems/phase0-upload/v1"
        , "predecessor-cert018=" <> renderArtifact proofBoundCert018
        , "runtime-test-obligation=" <> unObligationId (testCertificateObligation runtimeCertificate)
        , "runtime-test-revision=" <> unRevisionId runtimeRevisionId
        , "runtime-test-artifact=" <> renderArtifact runtimeArtifact
        , "native-scope=x86_64-unknown-linux-gnu;in-memory-loopback;pthreads;OpenSSL"
        , "phase0-reference-program=closed"
        , "generic-source-lowering=not-claimed"
        , "generic-runtime-correctness=not-claimed"
        , "production-networking=not-claimed"
        , "crash-durability=not-claimed"
        ]
      closureArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:phase0:PHIL-PHASE0-CERT-001:v1"
        , artifactDigest = digestText closureRecord
        }
      evidenceId = EvidenceEntryId "evidence.PHIL-PHASE0-CERT-001.certificate-checked.v1"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = closureRevisionId
        , evidenceAssuranceKind = CertificateChecked
        , evidenceRole = EvidenceRole "phase0_closure"
        , evidenceProducer =
            "Phil.Assurance.Phase0ClosureCertification.phase0ClosureCertification"
        , evidenceChecker =
            "separate PHIL-RUNTIME-INTEGRATED-UPLOAD-001 manifest verification + exact predecessor CERT-018 identity binding + Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just closureArtifact
        , evidenceInputDigests =
            [ phase0SourcePairDigest
            , artifactDigest proofBoundCert018
            , runtimeDigest
            ]
        , evidenceAssumptions = []
        , evidenceDependsOn = [DependsOnObligation runtimeRevisionId]
        , evidenceValidityScope = closureScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "the exact frozen source pair has proof-bound source-to-control-codec-v1 authority through PHIL-LLVM-CERT-018"
            , "the exact integrated native fixture has separately manifest-verified DifferentialTested evidence"
            , "the complete generated/runtime ABI agrees for all 46 declared Phil LLVM signatures in the fixture"
            , "accepted-upload, digest-rejection, and client-cancellation native fixture observations all pass"
            , "Phase 0 closure is explicitly scoped and exports generic runtime/network/durability assumptions instead of hiding them"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      closureEvidence = provisionalEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalEvidence }
      revisions = Map.insert closureRevisionId closureRevision (ledgerRevisions runtimeLedger)
      evidence = Map.insert evidenceId closureEvidence (ledgerEvidence runtimeLedger)
      obligationIds = Set.insert closureRevisionId (Map.keysSet revisions)
      evidenceIds = Set.insert evidenceId (Map.keysSet evidence)
      ledger = emptyLedger
        { ledgerRevisions = revisions
        , ledgerEvidence = evidence
        }
      closureRoot = digestText $ Text.intercalate "|"
        [ "phil-phase0-reference-closure-root-v1"
        , unDigest phase0SourcePairDigest
        , unDigest (artifactDigest proofBoundCert018)
        , unDigest runtimeDigest
        , unRevisionId runtimeRevisionId
        ]
      provisionalManifest = emptyManifest
        { manifestArchitectureDigest = manifestArchitectureDigest runtimeManifest
        , manifestPhilCoreDigest = manifestPhilCoreDigest runtimeManifest
        , manifestImplementationDigest = artifactDigest closureArtifact
        , manifestTarget = "phase0/reference-upload/native-closure"
        , manifestCompilationProfile = "phase0-closure/v1/x86_64-unknown-linux-gnu/in-memory"
        , manifestObligationRevisions = obligationIds
        , manifestCertificationScope = obligationIds
        , manifestEvidenceEntries = evidenceIds
        , manifestLoweringLedgerRoot = closureRoot
        , manifestValidityContext = validityContext
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId ledger provisionalManifest }
      explicitArtifacts = [closureArtifact, proofBoundCert018, runtimeArtifact]
      availableArtifacts = Map.fromList
        [ (artifactReference artifact, artifactDigest artifact)
        | artifact <- explicitArtifacts
        ]
      context = emptyVerificationContext
        { verificationArchitectureDigest = manifestArchitectureDigest runtimeManifest
        , verificationPhilCoreDigest = manifestPhilCoreDigest runtimeManifest
        , verificationImplementationDigest = artifactDigest closureArtifact
        , verificationTarget = manifestTarget manifest
        , verificationCompilationProfile = manifestCompilationProfile manifest
        , verificationExpectedObligations = obligationIds
        , verificationAvailableArtifacts = availableArtifacts
        , verificationLoweringLedgerRoot = closureRoot
        , verificationValidityContext = validityContext
        }
      result = Phase0ClosureCertificationBundle
        { phase0ClosureRuntimeTestArtifact = runtimeArtifact
        , phase0ClosureArtifact = closureArtifact
        , phase0ClosureRecord = closureRecord
        , phase0ClosureLedger = ledger
        , phase0ClosureManifest = manifest
        , phase0ClosureContext = context
        }

  mapLeft Phase0ClosureFinalManifestError $ verifyManifest context ledger manifest
  pure result

verifyPhase0ClosureCertification
  :: TestEvidenceCertificationBundle
  -> Either Phase0ClosureCertificationError ()
verifyPhase0ClosureCertification runtimeTest = do
  bundle <- phase0ClosureCertification runtimeTest
  mapLeft Phase0ClosureFinalManifestError $
    verifyManifest
      (phase0ClosureContext bundle)
      (phase0ClosureLedger bundle)
      (phase0ClosureManifest bundle)

renderPhase0ClosureCertification :: Phase0ClosureCertificationBundle -> Text
renderPhase0ClosureCertification = phase0ClosureRecord

verifyRuntimeTest
  :: TestEvidenceCertificationBundle
  -> Either Phase0ClosureCertificationError ()
verifyRuntimeTest bundle = do
  let expected = testSpecObligation integratedNativeUploadCertificationSpec
      actual = testCertificateObligation (testBundleCertificate bundle)
  unless (actual == expected) $
    Left (Phase0ClosureWrongRuntimeTest expected actual)
  mapLeft Phase0ClosureRuntimeManifestError $
    verifyManifest
      (testBundleVerificationContext bundle)
      (testBundleLedger bundle)
      (testBundleManifest bundle)

renderArtifact :: ArtifactIdentity -> Text
renderArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
