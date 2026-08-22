{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.Rocq
  ( RocqProofCertificate (..)
  , RocqCertificationBundle (..)
  , RocqCertificationError (..)
  , coreScalarCertificationClaim
  , coreScalarTheorems
  , renderRocqProofCertificate
  , certifyCoreScalarRocqProof
  ) where

import Control.Monad (unless)
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
import Phil.Core.Syntax (ObligationId (..))

data RocqProofCertificate = RocqProofCertificate
  { rocqCertificateObligation :: ObligationId
  , rocqCertificateRevision :: RevisionId
  , rocqCertificateClaimDigest :: Digest
  , rocqCertificateSourceArtifact :: ArtifactIdentity
  , rocqCertificateCompiledArtifact :: ArtifactIdentity
  , rocqCertificateTheorems :: [Text]
  , rocqCertificateCheckerProfile :: Text
  , rocqCertificateResidualBoundary :: Text
  }
  deriving (Eq, Show)

data RocqCertificationBundle = RocqCertificationBundle
  { rocqBundleCertificate :: RocqProofCertificate
  , rocqBundleCertificateArtifact :: ArtifactIdentity
  , rocqBundleLedger :: AssuranceLedger
  , rocqBundleManifest :: AssuranceManifest
  , rocqBundleVerificationContext :: VerificationContext
  }
  deriving (Eq, Show)

data RocqCertificationError
  = RocqSourceIsNotUtf8
  | RocqObligationMarkerMissing Text
  | RocqExpectedTheoremMissing Text
  | RocqManifestRejected ManifestError
  deriving (Eq, Show)

coreScalarCertificationClaim :: Text
coreScalarCertificationClaim =
  "Closed scalar literals have an intrinsic scalar type; Bool literals are always valid, and UInt[w] literals are valid exactly when w > 0 and 0 <= value < 2^w. Width and value are part of the literal identity rather than ambient convention."

coreScalarTheorems :: [Text]
coreScalarTheorems =
  [ "scalar_literal_has_intrinsic_type"
  , "scalar_literal_type_is_deterministic"
  , "boolean_literals_are_valid"
  , "valid_uint_has_positive_width"
  , "valid_uint_is_below_modulus"
  , "zero_width_uint_is_invalid"
  , "uint_at_modulus_is_invalid"
  ]

coreScalarRevision :: ObligationRevision
coreScalarRevision = provisional { revisionId = deriveRevisionId provisional }
  where
    provisional = ObligationRevision
      { revisionObligationId = ObligationId "PHIL-CORE-SCALAR-001"
      , revisionId = RevisionId ""
      , revisionStatement = coreScalarCertificationClaim
      , revisionStatementDigest = digestText coreScalarCertificationClaim
      , revisionKind = "Core scalar semantics"
      , revisionOrigin = "src/Phil/Core/Scalar.hs; proof/Phil/Core/Scalar.v"
      , revisionScope = "Phil.Core.Scalar"
      , revisionRequiredAt = "certification"
      , revisionRepresentation = "normalized Rocq proof model"
      , revisionSubjectIds = ["ScalarType", "ScalarLiteral", "ScalarLiteralValid"]
      , revisionContextIds = ["rocq/9.2.0", "proof-assistant-theorem/v1"]
      , revisionAcceptanceRule =
          AcceptEntry ProofAssistantTheorem (EvidenceRole "establishes")
      , revisionGeneratedFrom = []
      }

coreScalarValidity :: ValidityScope
coreScalarValidity = ValidityScope (Map.fromList
  [ ("proof_assistant", "Rocq")
  , ("rocq_version", "9.2.0")
  , ("certificate_profile", "proof-assistant-theorem/v1")
  ])

coreScalarValidityContext :: Map.Map Text Text
coreScalarValidityContext = validityDimensions coreScalarValidity

sourceRef :: ArtifactRef
sourceRef = ArtifactRef "proof/Phil/Core/Scalar.v"

compiledRef :: ArtifactRef
compiledRef = ArtifactRef "proof/Phil/Core/Scalar.vo"

certificateRef :: ArtifactRef
certificateRef = ArtifactRef "certificate:rocq:PHIL-CORE-SCALAR-001:v1"

checkerProfile :: Text
checkerProfile = "rocq/9.2.0 container; rocq c; proof-assistant-theorem/v1"

residualBoundary :: Text
residualBoundary =
  "Rocq kernel/toolchain correctness and the reviewed correspondence from PHIL-CORE-SCALAR-001 to the normalized theorem family remain explicit trust boundaries."

renderRocqProofCertificate :: RocqProofCertificate -> Text
renderRocqProofCertificate certificate = Text.intercalate "\n"
  [ "phil-rocq-proof-certificate/v1"
  , field "obligation" (unObligationId (rocqCertificateObligation certificate))
  , field "revision" (unRevisionId (rocqCertificateRevision certificate))
  , field "claim_sha256" (unDigest (rocqCertificateClaimDigest certificate))
  , artifactField "source" (rocqCertificateSourceArtifact certificate)
  , artifactField "compiled" (rocqCertificateCompiledArtifact certificate)
  , field "checker_profile" (rocqCertificateCheckerProfile certificate)
  , field "theorems" (Text.intercalate "," (rocqCertificateTheorems certificate))
  , field "residual_boundary" (rocqCertificateResidualBoundary certificate)
  , ""
  ]
  where
    field key value = key <> "=" <> value
    artifactField prefix artifact = Text.intercalate ";"
      [ prefix <> "_ref=" <> unArtifactRef (artifactReference artifact)
      , prefix <> "_sha256=" <> unDigest (artifactDigest artifact)
      ]

certificateArtifact :: RocqProofCertificate -> ArtifactIdentity
certificateArtifact certificate = ArtifactIdentity
  { artifactReference = certificateRef
  , artifactDigest = digestText (renderRocqProofCertificate certificate)
  }

coreScalarEvidence :: RocqProofCertificate -> ArtifactIdentity -> EvidenceEntry
coreScalarEvidence certificate artifact = provisional
  { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = EvidenceEntryId "evidence.PHIL-CORE-SCALAR-001.rocq.v1"
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId coreScalarRevision
      , evidenceAssuranceKind = ProofAssistantTheorem
      , evidenceRole = EvidenceRole "establishes"
      , evidenceProducer = "Rocq 9.2.0"
      , evidenceChecker = "Rocq kernel through successful `rocq c`, then Phil assurance manifest verification"
      , evidenceArtifact = Just artifact
      , evidenceInputDigests =
          [ artifactDigest (rocqCertificateSourceArtifact certificate)
          , artifactDigest (rocqCertificateCompiledArtifact certificate)
          ]
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = coreScalarValidity
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = coreScalarTheorems
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

certifyCoreScalarRocqProof
  :: ByteString.ByteString
  -> ByteString.ByteString
  -> Either RocqCertificationError RocqCertificationBundle
certifyCoreScalarRocqProof sourceBytes compiledBytes = do
  sourceText <- case TextEncoding.decodeUtf8' sourceBytes of
    Left _ -> Left RocqSourceIsNotUtf8
    Right value -> Right value
  let marker = "PHIL-CORE-SCALAR-001"
  unless (marker `Text.isInfixOf` sourceText) $
    Left (RocqObligationMarkerMissing marker)
  mapM_ (requireTheorem sourceText) coreScalarTheorems

  let sourceArtifact = ArtifactIdentity sourceRef (digestRawBytes sourceBytes)
      compiledArtifact = ArtifactIdentity compiledRef (digestRawBytes compiledBytes)
      certificate = RocqProofCertificate
        { rocqCertificateObligation = revisionObligationId coreScalarRevision
        , rocqCertificateRevision = revisionId coreScalarRevision
        , rocqCertificateClaimDigest = revisionStatementDigest coreScalarRevision
        , rocqCertificateSourceArtifact = sourceArtifact
        , rocqCertificateCompiledArtifact = compiledArtifact
        , rocqCertificateTheorems = coreScalarTheorems
        , rocqCertificateCheckerProfile = checkerProfile
        , rocqCertificateResidualBoundary = residualBoundary
        }
      certArtifact = certificateArtifact certificate
      evidence = coreScalarEvidence certificate certArtifact
      ledger = emptyLedger
        { ledgerRevisions = Map.singleton (revisionId coreScalarRevision) coreScalarRevision
        , ledgerEvidence = Map.singleton (evidenceEntryId evidence) evidence
        }
      architectureDigest = digestText "PHIL-CORE-SCALAR-001 Rocq certification architecture/v1"
      coreDigest = digestText "Phil assurance Rocq proof-certificate boundary/v1"
      loweringRoot = digestText "no-lowering/rocq-proof-certificate/v1"
      provisionalManifest = emptyManifest
        { manifestArchitectureDigest = architectureDigest
        , manifestPhilCoreDigest = coreDigest
        , manifestImplementationDigest = artifactDigest certArtifact
        , manifestTarget = "rocq-proof/PHIL-CORE-SCALAR-001"
        , manifestCompilationProfile = "rocq-9.2.0/proof-assistant-theorem/v1"
        , manifestObligationRevisions = Set.singleton (revisionId coreScalarRevision)
        , manifestCertificationScope = Set.singleton (revisionId coreScalarRevision)
        , manifestEvidenceEntries = Set.singleton (evidenceEntryId evidence)
        , manifestLoweringLedgerRoot = loweringRoot
        , manifestValidityContext = coreScalarValidityContext
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId ledger provisionalManifest }
      context = emptyVerificationContext
        { verificationArchitectureDigest = architectureDigest
        , verificationPhilCoreDigest = coreDigest
        , verificationImplementationDigest = artifactDigest certArtifact
        , verificationTarget = manifestTarget manifest
        , verificationCompilationProfile = manifestCompilationProfile manifest
        , verificationExpectedObligations = Set.singleton (revisionId coreScalarRevision)
        , verificationAvailableArtifacts = Map.singleton
            (artifactReference certArtifact)
            (artifactDigest certArtifact)
        , verificationLoweringLedgerRoot = loweringRoot
        , verificationValidityContext = coreScalarValidityContext
        }

  case verifyManifest context ledger manifest of
    Left err -> Left (RocqManifestRejected err)
    Right () -> Right RocqCertificationBundle
      { rocqBundleCertificate = certificate
      , rocqBundleCertificateArtifact = certArtifact
      , rocqBundleLedger = ledger
      , rocqBundleManifest = manifest
      , rocqBundleVerificationContext = context
      }
  where
    requireTheorem sourceText theoremName =
      unless (("Theorem " <> theoremName) `Text.isInfixOf` sourceText) $
        Left (RocqExpectedTheoremMissing theoremName)

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
