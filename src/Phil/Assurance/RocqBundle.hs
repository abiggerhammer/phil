{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqBundle
  ( RocqProofPartSpec (..)
  , RocqProofBundleSpec (..)
  , RocqProofPartResult (..)
  , RocqProofBundleResult (..)
  , RocqBundleCertificationError (..)
  , packageTrustedRocqProofBundle
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
import Phil.Assurance.Rocq (RocqProofCertificate (..), renderRocqProofCertificate)
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))

data RocqProofPartSpec = RocqProofPartSpec
  { rocqPartRole :: EvidenceRole
  , rocqPartTheorems :: [Text]
  , rocqPartSourceRef :: ArtifactRef
  , rocqPartCompiledRef :: ArtifactRef
  , rocqPartCertificateRef :: ArtifactRef
  , rocqPartEvidenceId :: EvidenceEntryId
  }
  deriving (Eq, Show)

data RocqProofBundleSpec = RocqProofBundleSpec
  { rocqBundleProfile :: Text
  , rocqBundleObligation :: ObligationId
  , rocqBundleClaim :: Text
  , rocqBundleKind :: Text
  , rocqBundleOrigin :: Text
  , rocqBundleScope :: Text
  , rocqBundleRepresentation :: Text
  , rocqBundleSubjects :: [Text]
  , rocqBundleParts :: [RocqProofPartSpec]
  , rocqBundleResidualBoundary :: Text
  }
  deriving (Eq, Show)

data RocqProofPartResult = RocqProofPartResult
  { rocqPartResultSpec :: RocqProofPartSpec
  , rocqPartResultCertificate :: RocqProofCertificate
  , rocqPartResultCertificateArtifact :: ArtifactIdentity
  }
  deriving (Eq, Show)

data RocqProofBundleResult = RocqProofBundleResult
  { rocqBundleResultRevision :: ObligationRevision
  , rocqBundleResultParts :: [RocqProofPartResult]
  , rocqBundleResultLedger :: AssuranceLedger
  , rocqBundleResultManifest :: AssuranceManifest
  , rocqBundleResultVerificationContext :: VerificationContext
  }
  deriving (Eq, Show)

data RocqBundleCertificationError
  = RocqBundlePartCountMismatch Int Int
  | RocqBundleHasNoParts
  | RocqBundleDuplicateRole EvidenceRole
  | RocqBundleDuplicateEvidenceId EvidenceEntryId
  | RocqBundleDuplicateCertificateRef ArtifactRef
  | RocqBundleEmptyTheoremSet EvidenceRole
  | RocqBundleSourceIsNotUtf8 ArtifactRef
  | RocqBundleObligationMarkerMissing ArtifactRef Text
  | RocqBundleExpectedTheoremMissing ArtifactRef Text
  | RocqBundleManifestRejected ManifestError
  deriving (Eq, Show)

checkerProfile :: Text
checkerProfile = "rocq/9.2.0 externally checked; trusted-packaging/proof-assistant-theorem/v1"

certificationValidity :: ValidityScope
certificationValidity = ValidityScope (Map.fromList
  [ ("proof_assistant", "Rocq")
  , ("rocq_version", "9.2.0")
  , ("certificate_profile", "proof-assistant-theorem/v1")
  ])

certificationValidityContext :: Map.Map Text Text
certificationValidityContext = validityDimensions certificationValidity

-- | Package a bundle of proof bytes already checked by a trusted Rocq producer.
--
-- This pure boundary hashes and binds supplied source/object bytes but does not
-- run or authenticate Rocq; successful checking is an explicit caller premise.
packageTrustedRocqProofBundle
  :: RocqProofBundleSpec
  -> [(ByteString.ByteString, ByteString.ByteString)]
  -> Either RocqBundleCertificationError RocqProofBundleResult
packageTrustedRocqProofBundle spec inputs = do
  validateSpec spec
  let parts = rocqBundleParts spec
  unless (length parts == length inputs) $
    Left (RocqBundlePartCountMismatch (length parts) (length inputs))

  let revision = bundleRevision spec
  results <- sequence
    [ certifyPart spec revision part sourceBytes compiledBytes
    | (part, (sourceBytes, compiledBytes)) <- zip parts inputs
    ]
  let certificateArtifacts = map rocqPartResultCertificateArtifact results
      evidenceEntries =
        [ bundleEvidence revision result
        | result <- results
        ]
      ledger = emptyLedger
        { ledgerRevisions = Map.singleton (revisionId revision) revision
        , ledgerEvidence = Map.fromList
            [ (evidenceEntryId entry, entry)
            | entry <- evidenceEntries
            ]
        }
      obligationText = unObligationId (rocqBundleObligation spec)
      architectureDigest = digestText (obligationText <> " Rocq proof bundle architecture/v1")
      coreDigest = digestText "Phil assurance Rocq proof-bundle boundary/v1"
      implementationDigest = bundleImplementationDigest certificateArtifacts
      loweringRoot = digestText "no-lowering/rocq-proof-bundle/v1"
      provisionalManifest = emptyManifest
        { manifestArchitectureDigest = architectureDigest
        , manifestPhilCoreDigest = coreDigest
        , manifestImplementationDigest = implementationDigest
        , manifestTarget = "rocq-proof-bundle/" <> obligationText
        , manifestCompilationProfile = "rocq-9.2.0/proof-assistant-theorem-bundle/v1"
        , manifestObligationRevisions = Set.singleton (revisionId revision)
        , manifestCertificationScope = Set.singleton (revisionId revision)
        , manifestEvidenceEntries = Set.fromList (map evidenceEntryId evidenceEntries)
        , manifestLoweringLedgerRoot = loweringRoot
        , manifestValidityContext = certificationValidityContext
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId ledger provisionalManifest }
      context = emptyVerificationContext
        { verificationArchitectureDigest = architectureDigest
        , verificationPhilCoreDigest = coreDigest
        , verificationImplementationDigest = implementationDigest
        , verificationTarget = manifestTarget manifest
        , verificationCompilationProfile = manifestCompilationProfile manifest
        , verificationExpectedObligations = Set.singleton (revisionId revision)
        , verificationAvailableArtifacts = Map.fromList
            [ (artifactReference artifact, artifactDigest artifact)
            | artifact <- certificateArtifacts
            ]
        , verificationLoweringLedgerRoot = loweringRoot
        , verificationValidityContext = certificationValidityContext
        }

  case verifyManifest context ledger manifest of
    Left err -> Left (RocqBundleManifestRejected err)
    Right () -> Right RocqProofBundleResult
      { rocqBundleResultRevision = revision
      , rocqBundleResultParts = results
      , rocqBundleResultLedger = ledger
      , rocqBundleResultManifest = manifest
      , rocqBundleResultVerificationContext = context
      }

validateSpec :: RocqProofBundleSpec -> Either RocqBundleCertificationError ()
validateSpec spec = do
  let parts = rocqBundleParts spec
  when (null parts) (Left RocqBundleHasNoParts)
  mapM_ requireTheorems parts
  requireUnique RocqBundleDuplicateRole rocqPartRole parts
  requireUnique RocqBundleDuplicateEvidenceId rocqPartEvidenceId parts
  requireUnique RocqBundleDuplicateCertificateRef rocqPartCertificateRef parts
  where
    requireTheorems part =
      when (null (rocqPartTheorems part)) $
        Left (RocqBundleEmptyTheoremSet (rocqPartRole part))

    requireUnique
      :: Ord key
      => (key -> RocqBundleCertificationError)
      -> (RocqProofPartSpec -> key)
      -> [RocqProofPartSpec]
      -> Either RocqBundleCertificationError ()
    requireUnique mkError project = go Set.empty
      where
        go _ [] = Right ()
        go seen (part : rest)
          | Set.member key seen = Left (mkError key)
          | otherwise = go (Set.insert key seen) rest
          where
            key = project part

bundleRevision :: RocqProofBundleSpec -> ObligationRevision
bundleRevision spec = provisional { revisionId = deriveRevisionId provisional }
  where
    provisional = ObligationRevision
      { revisionObligationId = rocqBundleObligation spec
      , revisionId = RevisionId ""
      , revisionStatement = rocqBundleClaim spec
      , revisionStatementDigest = digestText (rocqBundleClaim spec)
      , revisionKind = rocqBundleKind spec
      , revisionOrigin = rocqBundleOrigin spec
      , revisionScope = rocqBundleScope spec
      , revisionRequiredAt = "certification"
      , revisionRepresentation = rocqBundleRepresentation spec
      , revisionSubjectIds = rocqBundleSubjects spec
      , revisionContextIds =
          [ "rocq/9.2.0"
          , "proof-assistant-theorem-bundle/v1"
          ]
      , revisionAcceptanceRule = AcceptAll
          [ AcceptEntry ProofAssistantTheorem (rocqPartRole part)
          | part <- rocqBundleParts spec
          ]
      , revisionGeneratedFrom = []
      }

certifyPart
  :: RocqProofBundleSpec
  -> ObligationRevision
  -> RocqProofPartSpec
  -> ByteString.ByteString
  -> ByteString.ByteString
  -> Either RocqBundleCertificationError RocqProofPartResult
certifyPart spec revision part sourceBytes compiledBytes = do
  sourceText <- case TextEncoding.decodeUtf8' sourceBytes of
    Left _ -> Left (RocqBundleSourceIsNotUtf8 (rocqPartSourceRef part))
    Right value -> Right value
  let marker = unObligationId (rocqBundleObligation spec)
  unless (marker `Text.isInfixOf` sourceText) $
    Left (RocqBundleObligationMarkerMissing (rocqPartSourceRef part) marker)
  mapM_ (requireDeclaration sourceText) (rocqPartTheorems part)

  let sourceArtifact = ArtifactIdentity
        (rocqPartSourceRef part)
        (digestRawBytes sourceBytes)
      compiledArtifact = ArtifactIdentity
        (rocqPartCompiledRef part)
        (digestRawBytes compiledBytes)
      certificate = RocqProofCertificate
        { rocqCertificateObligation = revisionObligationId revision
        , rocqCertificateRevision = revisionId revision
        , rocqCertificateClaimDigest = revisionStatementDigest revision
        , rocqCertificateSourceArtifact = sourceArtifact
        , rocqCertificateCompiledArtifact = compiledArtifact
        , rocqCertificateTheorems = rocqPartTheorems part
        , rocqCertificateCheckerProfile = checkerProfile
        , rocqCertificateResidualBoundary = rocqBundleResidualBoundary spec
        }
      certificateArtifact = ArtifactIdentity
        { artifactReference = rocqPartCertificateRef part
        , artifactDigest = digestText (renderRocqProofCertificate certificate)
        }
  Right RocqProofPartResult
    { rocqPartResultSpec = part
    , rocqPartResultCertificate = certificate
    , rocqPartResultCertificateArtifact = certificateArtifact
    }
  where
    requireDeclaration sourceText theoremName =
      unless (any (`Text.isInfixOf` sourceText)
          [ "Theorem " <> theoremName
          , "Lemma " <> theoremName
          , "Corollary " <> theoremName
          ]) $
        Left (RocqBundleExpectedTheoremMissing (rocqPartSourceRef part) theoremName)

bundleEvidence :: ObligationRevision -> RocqProofPartResult -> EvidenceEntry
bundleEvidence revision result = provisional
  { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    part = rocqPartResultSpec result
    certificate = rocqPartResultCertificate result
    provisional = EvidenceEntry
      { evidenceEntryId = rocqPartEvidenceId part
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
      , evidenceAssuranceKind = ProofAssistantTheorem
      , evidenceRole = rocqPartRole part
      , evidenceProducer = "trusted externally checked Rocq 9.2.0 inputs"
      , evidenceChecker = "Phil trusted proof-bundle packaging boundary; successful Rocq checking is an explicit caller precondition"
      , evidenceArtifact = Just (rocqPartResultCertificateArtifact result)
      , evidenceInputDigests =
          [ artifactDigest (rocqCertificateSourceArtifact certificate)
          , artifactDigest (rocqCertificateCompiledArtifact certificate)
          ]
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = certificationValidity
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = rocqPartTheorems part
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

bundleImplementationDigest :: [ArtifactIdentity] -> Digest
bundleImplementationDigest artifacts = digestText . Text.intercalate "\n" $
  "phil-rocq-proof-bundle/v1" :
  [ unArtifactRef (artifactReference artifact) <> "=" <> unDigest (artifactDigest artifact)
  | artifact <- artifacts
  ]

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
