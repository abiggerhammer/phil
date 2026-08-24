{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.TestEvidenceCertification
  ( TestEvidenceCertificationSpec (..)
  , TestEvidenceCertificate (..)
  , TestEvidenceCertificationBundle (..)
  , TestEvidenceCertificationError (..)
  , surfaceConformanceCertificationSpec
  , knownTestEvidenceCertificationSpec
  , renderTestEvidenceCertificate
  , certifyTestEvidence
  ) where

import Control.Monad (unless, when)
import qualified Crypto.Hash.SHA256 as SHA256
import Data.Bits ((.&.), shiftR)
import qualified Data.ByteString as ByteString
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Data.Word (Word8)
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..), unObligationId)

data TestEvidenceCertificationSpec = TestEvidenceCertificationSpec
  { testSpecProfile :: Text
  , testSpecObligation :: ObligationId
  , testSpecClaim :: Text
  , testSpecKind :: Text
  , testSpecOrigin :: Text
  , testSpecScope :: Text
  , testSpecRepresentation :: Text
  , testSpecSubjects :: [Text]
  , testSpecAssuranceKind :: AssuranceKind
  , testSpecCheckerRef :: ArtifactRef
  , testSpecInputRefs :: [ArtifactRef]
  , testSpecResultRef :: ArtifactRef
  , testSpecCertificateRef :: ArtifactRef
  , testSpecEvidenceId :: EvidenceEntryId
  , testSpecExpectedMarkers :: [Text]
  , testSpecForbiddenMarkers :: [Text]
  , testSpecValidity :: ValidityScope
  , testSpecProducer :: Text
  , testSpecCheckerProfile :: Text
  , testSpecResidualBoundary :: Text
  }
  deriving (Eq, Show)

data TestEvidenceCertificate = TestEvidenceCertificate
  { testCertificateObligation :: ObligationId
  , testCertificateRevision :: RevisionId
  , testCertificateClaimDigest :: Digest
  , testCertificateAssuranceKind :: AssuranceKind
  , testCertificateCheckerArtifact :: ArtifactIdentity
  , testCertificateInputArtifacts :: [ArtifactIdentity]
  , testCertificateResultArtifact :: ArtifactIdentity
  , testCertificateExpectedMarkers :: [Text]
  , testCertificateValidity :: ValidityScope
  , testCertificateProducer :: Text
  , testCertificateCheckerProfile :: Text
  , testCertificateResidualBoundary :: Text
  }
  deriving (Eq, Show)

data TestEvidenceCertificationBundle = TestEvidenceCertificationBundle
  { testBundleCertificate :: TestEvidenceCertificate
  , testBundleCertificateArtifact :: ArtifactIdentity
  , testBundleLedger :: AssuranceLedger
  , testBundleManifest :: AssuranceManifest
  , testBundleVerificationContext :: VerificationContext
  }
  deriving (Eq, Show)

data TestEvidenceCertificationError
  = TestEvidenceUnsupportedKind AssuranceKind
  | TestEvidenceResultIsNotUtf8
  | TestEvidenceExpectedMarkerMissing Text
  | TestEvidenceForbiddenMarkerPresent Text
  | TestEvidenceInputReferenceMismatch [ArtifactRef] [ArtifactRef]
  | TestEvidenceManifestRejected ManifestError
  deriving (Eq, Show)

surfaceConformanceCertificationSpec :: TestEvidenceCertificationSpec
surfaceConformanceCertificationSpec = TestEvidenceCertificationSpec
  { testSpecProfile = "surface-conformance"
  , testSpecObligation = ObligationId "PHIL-SURFACE-CONF-001"
  , testSpecClaim =
      "For the frozen Phase 0 upload witness corpus, whole-component checking accepts both normative upload role programs and rejects each of the twenty negative witnesses with its declared semantic rejection class; checker timeout/nontermination is a conformance failure, and the expectation table is not consulted by the checker."
  , testSpecKind = "Surface frozen corpus conformance"
  , testSpecOrigin =
      "src/Phil/Surface/Check.hs; src/Phil/Surface/Phase0.hs; test/SurfaceConformanceMain.hs; examples/upload; examples/rejected"
  , testSpecScope = "frozen Phase 0 upload witness corpus"
  , testSpecRepresentation =
      "content-bound DifferentialTested evidence over the exact 22-file witness corpus"
  , testSpecSubjects =
      [ "2 normative upload programs"
      , "20 declared negative witness programs"
      , "exact semantic rejection classes"
      , "2s per-fixture termination bound"
      ]
  , testSpecAssuranceKind = DifferentialTested
  , testSpecCheckerRef = ArtifactRef "test/SurfaceConformanceMain.hs"
  , testSpecInputRefs = map ArtifactRef surfaceConformanceInputPaths
  , testSpecResultRef = ArtifactRef "artifact:phil:surface:phase0:conformance:test-log:v1"
  , testSpecCertificateRef = ArtifactRef "certificate:test:PHIL-SURFACE-CONF-001:v1"
  , testSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SURFACE-CONF-001.differential.v1"
  , testSpecExpectedMarkers = map ("PASS: " <>) surfaceConformanceFixturePaths
  , testSpecForbiddenMarkers = ["FAIL:"]
  , testSpecValidity = ValidityScope (Map.fromList
      [ ("evidence_kind", "DifferentialTested")
      , ("checker_profile", "ghc-9.6.7/cabal/surface-conformance/v1")
      , ("corpus", "phase0-upload-frozen-22")
      , ("certificate_profile", "test-evidence-certificate/v1")
      ])
  , testSpecProducer = "cabal test phil-surface-conformance-tests --test-show-details=direct"
  , testSpecCheckerProfile =
      "GHC 9.6.7; Cabal; SurfaceConformanceMain; successful exit plus exact PASS markers; test-evidence-certificate/v1"
  , testSpecResidualBoundary =
      "This certification establishes only the frozen 22-fixture conformance claim. It is not a universal parser/checker soundness or completeness theorem. GHC/Cabal/host execution, the Haskell implementation, System.Timeout behavior, fixture instrumentation, and the test-evidence certifier/manifest verifier remain explicit trust boundaries."
  }

knownTestEvidenceCertificationSpec :: Text -> Maybe TestEvidenceCertificationSpec
knownTestEvidenceCertificationSpec profile
  | profile == testSpecProfile surfaceConformanceCertificationSpec =
      Just surfaceConformanceCertificationSpec
  | otherwise = Nothing

certifyTestEvidence
  :: TestEvidenceCertificationSpec
  -> ByteString.ByteString
  -> [(ArtifactRef, ByteString.ByteString)]
  -> ByteString.ByteString
  -> Either TestEvidenceCertificationError TestEvidenceCertificationBundle
certifyTestEvidence spec checkerBytes suppliedInputs resultBytes = do
  unless (testSpecAssuranceKind spec `elem` [DifferentialTested, PropertyTested]) $
    Left (TestEvidenceUnsupportedKind (testSpecAssuranceKind spec))

  let expectedRefs = testSpecInputRefs spec
      suppliedRefs = map fst suppliedInputs
  unless (expectedRefs == suppliedRefs) $
    Left (TestEvidenceInputReferenceMismatch expectedRefs suppliedRefs)

  resultText <- case TextEncoding.decodeUtf8' resultBytes of
    Left _ -> Left TestEvidenceResultIsNotUtf8
    Right value -> Right value
  mapM_ (requireMarker resultText) (testSpecExpectedMarkers spec)
  mapM_ (forbidMarker resultText) (testSpecForbiddenMarkers spec)

  let revision = specRevision spec
      checkerArtifact = ArtifactIdentity
        (testSpecCheckerRef spec)
        (digestRawBytes checkerBytes)
      inputArtifacts =
        [ ArtifactIdentity ref (digestRawBytes bytes)
        | (ref, bytes) <- suppliedInputs
        ]
      resultArtifact = ArtifactIdentity
        (testSpecResultRef spec)
        (digestRawBytes resultBytes)
      certificate = TestEvidenceCertificate
        { testCertificateObligation = revisionObligationId revision
        , testCertificateRevision = revisionId revision
        , testCertificateClaimDigest = revisionStatementDigest revision
        , testCertificateAssuranceKind = testSpecAssuranceKind spec
        , testCertificateCheckerArtifact = checkerArtifact
        , testCertificateInputArtifacts = inputArtifacts
        , testCertificateResultArtifact = resultArtifact
        , testCertificateExpectedMarkers = testSpecExpectedMarkers spec
        , testCertificateValidity = testSpecValidity spec
        , testCertificateProducer = testSpecProducer spec
        , testCertificateCheckerProfile = testSpecCheckerProfile spec
        , testCertificateResidualBoundary = testSpecResidualBoundary spec
        }
      certArtifact = ArtifactIdentity
        (testSpecCertificateRef spec)
        (digestText (renderTestEvidenceCertificate certificate))
      evidence = specEvidence spec revision certificate certArtifact
      ledger = emptyLedger
        { ledgerRevisions = Map.singleton (revisionId revision) revision
        , ledgerEvidence = Map.singleton (evidenceEntryId evidence) evidence
        }
      obligationText = unObligationId (testSpecObligation spec)
      architectureDigest = digestText (obligationText <> " test-evidence certification architecture/v1")
      coreDigest = digestText "Phil assurance test-evidence certificate boundary/v1"
      loweringRoot = digestText "no-lowering/test-evidence-certificate/v1"
      validityContext = validityDimensions (testSpecValidity spec)
      profileText = assuranceKindText (testSpecAssuranceKind spec)
      provisionalManifest = emptyManifest
        { manifestArchitectureDigest = architectureDigest
        , manifestPhilCoreDigest = coreDigest
        , manifestImplementationDigest = artifactDigest certArtifact
        , manifestTarget = "test-evidence/" <> obligationText
        , manifestCompilationProfile =
            "test-evidence-certificate/v1/" <> testSpecProfile spec <> "/" <> profileText
        , manifestObligationRevisions = Set.singleton (revisionId revision)
        , manifestCertificationScope = Set.singleton (revisionId revision)
        , manifestEvidenceEntries = Set.singleton (evidenceEntryId evidence)
        , manifestLoweringLedgerRoot = loweringRoot
        , manifestValidityContext = validityContext
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId ledger provisionalManifest }
      context = emptyVerificationContext
        { verificationArchitectureDigest = architectureDigest
        , verificationPhilCoreDigest = coreDigest
        , verificationImplementationDigest = artifactDigest certArtifact
        , verificationTarget = manifestTarget manifest
        , verificationCompilationProfile = manifestCompilationProfile manifest
        , verificationExpectedObligations = Set.singleton (revisionId revision)
        , verificationAvailableArtifacts = Map.singleton
            (artifactReference certArtifact)
            (artifactDigest certArtifact)
        , verificationLoweringLedgerRoot = loweringRoot
        , verificationValidityContext = validityContext
        }

  case verifyManifest context ledger manifest of
    Left err -> Left (TestEvidenceManifestRejected err)
    Right () -> Right TestEvidenceCertificationBundle
      { testBundleCertificate = certificate
      , testBundleCertificateArtifact = certArtifact
      , testBundleLedger = ledger
      , testBundleManifest = manifest
      , testBundleVerificationContext = context
      }
  where
    requireMarker resultText marker =
      unless (marker `Text.isInfixOf` resultText) $
        Left (TestEvidenceExpectedMarkerMissing marker)
    forbidMarker resultText marker =
      when (marker `Text.isInfixOf` resultText) $
        Left (TestEvidenceForbiddenMarkerPresent marker)

renderTestEvidenceCertificate :: TestEvidenceCertificate -> Text
renderTestEvidenceCertificate certificate = Text.intercalate "\n" $
  [ "phil-test-evidence-certificate/v1"
  , field "obligation" (unObligationId (testCertificateObligation certificate))
  , field "revision" (unRevisionId (testCertificateRevision certificate))
  , field "claim_sha256" (unDigest (testCertificateClaimDigest certificate))
  , field "assurance_kind" (assuranceKindText (testCertificateAssuranceKind certificate))
  , artifactField "checker" (testCertificateCheckerArtifact certificate)
  ]
  <> zipWith inputField [(1 :: Int) ..] (testCertificateInputArtifacts certificate)
  <> [ artifactField "result" (testCertificateResultArtifact certificate)
     , field "expected_markers" (Text.intercalate "|" (testCertificateExpectedMarkers certificate))
     , field "validity" (renderValidity (testCertificateValidity certificate))
     , field "producer" (testCertificateProducer certificate)
     , field "checker_profile" (testCertificateCheckerProfile certificate)
     , field "residual_boundary" (testCertificateResidualBoundary certificate)
     , ""
     ]
  where
    field key value = key <> "=" <> value
    artifactField prefix artifact = Text.intercalate ";"
      [ prefix <> "_ref=" <> unArtifactRef (artifactReference artifact)
      , prefix <> "_sha256=" <> unDigest (artifactDigest artifact)
      ]
    inputField index artifact = artifactField ("input" <> Text.pack (show index)) artifact

specRevision :: TestEvidenceCertificationSpec -> ObligationRevision
specRevision spec = provisional { revisionId = deriveRevisionId provisional }
  where
    provisional = ObligationRevision
      { revisionObligationId = testSpecObligation spec
      , revisionId = RevisionId ""
      , revisionStatement = testSpecClaim spec
      , revisionStatementDigest = digestText (testSpecClaim spec)
      , revisionKind = testSpecKind spec
      , revisionOrigin = testSpecOrigin spec
      , revisionScope = testSpecScope spec
      , revisionRequiredAt = "certification"
      , revisionRepresentation = testSpecRepresentation spec
      , revisionSubjectIds = testSpecSubjects spec
      , revisionContextIds =
          [ key <> "=" <> value
          | (key, value) <- Map.toAscList (validityDimensions (testSpecValidity spec))
          ]
      , revisionAcceptanceRule =
          AcceptEntry (testSpecAssuranceKind spec) (EvidenceRole "establishes")
      , revisionGeneratedFrom = []
      }

specEvidence
  :: TestEvidenceCertificationSpec
  -> ObligationRevision
  -> TestEvidenceCertificate
  -> ArtifactIdentity
  -> EvidenceEntry
specEvidence spec revision certificate certArtifact = provisional
  { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = testSpecEvidenceId spec
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
      , evidenceAssuranceKind = testSpecAssuranceKind spec
      , evidenceRole = EvidenceRole "establishes"
      , evidenceProducer = testSpecProducer spec
      , evidenceChecker =
          "successful test execution + expected/forbidden result-marker validation + Phil.Assurance.Verify.verifyManifest"
      , evidenceArtifact = Just certArtifact
      , evidenceInputDigests =
          artifactDigest (testCertificateCheckerArtifact certificate)
          : artifactDigest (testCertificateResultArtifact certificate)
          : map artifactDigest (testCertificateInputArtifacts certificate)
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = testSpecValidity spec
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = testSpecSubjects spec
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

renderValidity :: ValidityScope -> Text
renderValidity (ValidityScope dimensions) = Text.intercalate ";"
  [ key <> "=" <> value
  | (key, value) <- Map.toAscList dimensions
  ]

assuranceKindText :: AssuranceKind -> Text
assuranceKindText kind = case kind of
  KernelChecked -> "KernelChecked"
  ProofAssistantTheorem -> "ProofAssistantTheorem"
  CertificateChecked -> "CertificateChecked"
  TranslationValidated -> "TranslationValidated"
  DifferentialTested -> "DifferentialTested"
  PropertyTested -> "PropertyTested"
  RuntimeEnforced -> "RuntimeEnforced"
  Assumed -> "Assumed"

digestRawBytes :: ByteString.ByteString -> Digest
digestRawBytes value = Digest . Text.pack . concatMap hexByte . ByteString.unpack $
  SHA256.hash value
  where
    hexByte :: Word8 -> String
    hexByte byte = [hexDigit (byte `shiftR` 4), hexDigit (byte .&. 0x0f)]

    hexDigit :: Word8 -> Char
    hexDigit nibble
      | nibble < 10 = toEnum (fromEnum '0' + fromIntegral nibble)
      | otherwise = toEnum (fromEnum 'a' + fromIntegral nibble - 10)

surfaceConformanceFixturePaths :: [Text]
surfaceConformanceFixturePaths =
  [ "examples/upload/client.phil"
  , "examples/upload/server.phil"
  , "examples/rejected/01-reuse-consumed-endpoint.phil"
  , "examples/rejected/02-drop-live-endpoint.phil"
  , "examples/rejected/03-wrong-protocol-order.phil"
  , "examples/rejected/04-nonexhaustive-offer.phil"
  , "examples/rejected/05-raw-field-access.phil"
  , "examples/rejected/06-parsed-used-as-validated.phil"
  , "examples/rejected/07-unrelated-payload-length.phil"
  , "examples/rejected/08-incompatible-branch-join.phil"
  , "examples/rejected/09-continue-after-fatal-recognition-failure.phil"
  , "examples/rejected/10-accept-before-digest-check.phil"
  , "examples/rejected/11-copy-authority-capability.phil"
  , "examples/rejected/12-ignore-cancellation-cleanup.phil"
  , "examples/rejected/13-commit-unrelated-parsed.phil"
  , "examples/rejected/14-copy-owned-payload.phil"
  , "examples/rejected/15-drop-pending-receive.phil"
  , "examples/rejected/16-escape-shared-loan.phil"
  , "examples/rejected/17-use-evidence-wrong-context.phil"
  , "examples/rejected/18-prove-opaque-digest.phil"
  , "examples/rejected/19-label-does-not-transfer-proof.phil"
  , "examples/rejected/20-unchecked-wraparound-proof.phil"
  ]

surfaceConformanceInputPaths :: [Text]
surfaceConformanceInputPaths =
  [ "phil-core.cabal"
  , "src/Phil/Surface/Syntax.hs"
  , "src/Phil/Surface/Parser.hs"
  , "src/Phil/Surface/Elaborate.hs"
  , "src/Phil/Surface/Check.hs"
  , "src/Phil/Surface/Check/Types.hs"
  , "src/Phil/Surface/Check/Support.hs"
  , "src/Phil/Surface/Check/Preflight.hs"
  , "src/Phil/Surface/Check/Engine.hs"
  , "src/Phil/Surface/Phase0.hs"
  , "src/Phil/Assurance/TestEvidenceCertification.hs"
  , "src/Phil/Assurance/Verify.hs"
  ] <> surfaceConformanceFixturePaths
