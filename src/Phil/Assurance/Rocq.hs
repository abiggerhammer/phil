{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.Rocq
  ( RocqCertificationSpec (..)
  , RocqProofCertificate (..)
  , RocqCertificationBundle (..)
  , RocqCertificationError (..)
  , coreScalarCertificationSpec
  , systemsFieldProjectionCertificationSpec
  , llvmFieldProjectionCertificationSpec
  , knownRocqCertificationSpec
  , coreScalarCertificationClaim
  , coreScalarTheorems
  , renderRocqProofCertificate
  , certifyRocqProof
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

data RocqCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile :: Text
  , rocqSpecObligation :: ObligationId
  , rocqSpecClaim :: Text
  , rocqSpecKind :: Text
  , rocqSpecOrigin :: Text
  , rocqSpecScope :: Text
  , rocqSpecRepresentation :: Text
  , rocqSpecSubjects :: [Text]
  , rocqSpecTheorems :: [Text]
  , rocqSpecSourceRef :: ArtifactRef
  , rocqSpecCompiledRef :: ArtifactRef
  , rocqSpecCertificateRef :: ArtifactRef
  , rocqSpecEvidenceId :: EvidenceEntryId
  , rocqSpecResidualBoundary :: Text
  }
  deriving (Eq, Show)

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
  = RocqUnknownCertificationProfile Text
  | RocqSourceIsNotUtf8
  | RocqObligationMarkerMissing Text
  | RocqExpectedTheoremMissing Text
  | RocqManifestRejected ManifestError
  deriving (Eq, Show)

checkerProfile :: Text
checkerProfile = "rocq/9.2.0 container; rocq c; proof-assistant-theorem/v1"

certificationValidity :: ValidityScope
certificationValidity = ValidityScope (Map.fromList
  [ ("proof_assistant", "Rocq")
  , ("rocq_version", "9.2.0")
  , ("certificate_profile", "proof-assistant-theorem/v1")
  ])

certificationValidityContext :: Map.Map Text Text
certificationValidityContext = validityDimensions certificationValidity

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

coreScalarCertificationSpec :: RocqCertificationSpec
coreScalarCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "core-scalar"
  , rocqSpecObligation = ObligationId "PHIL-CORE-SCALAR-001"
  , rocqSpecClaim = coreScalarCertificationClaim
  , rocqSpecKind = "Core scalar semantics"
  , rocqSpecOrigin = "src/Phil/Core/Scalar.hs; proof/Phil/Core/Scalar.v"
  , rocqSpecScope = "Phil.Core.Scalar"
  , rocqSpecRepresentation = "normalized Rocq proof model"
  , rocqSpecSubjects = ["ScalarType", "ScalarLiteral", "ScalarLiteralValid"]
  , rocqSpecTheorems = coreScalarTheorems
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/Scalar.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/Scalar.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CORE-SCALAR-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CORE-SCALAR-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness and the reviewed correspondence from PHIL-CORE-SCALAR-001 to the normalized theorem family remain explicit trust boundaries."
  }

systemsFieldProjectionCertificationSpec :: RocqCertificationSpec
systemsFieldProjectionCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-field-projection"
  , rocqSpecObligation = ObligationId "PHIL-SYS-FIELD-PROJ-001"
  , rocqSpecClaim =
      "A verified recognized field projection preserves the witness's pending-ingress grammar and recognition-success path, schema field and scalar type, matching commit ordering, exact projection call shape and content-bound lowering decision, and exact-receive consumer; the projected scalar has one preceding/dominating definition through PHIL-SYS-SSA-001, and schema/order/decision/consumer drift rejects."
  , rocqSpecKind = "Systems recognized field projection"
  , rocqSpecOrigin = "src/Phil/Systems/FieldProjection.hs; proof/Phil/Systems/FieldProjection.v"
  , rocqSpecScope = "Phil.Systems.FieldProjection"
  , rocqSpecRepresentation = "normalized Rocq witness/provenance model"
  , rocqSpecSubjects = ["FieldProjectionWitness", "TypedScalar", "TermReceiveExact"]
  , rocqSpecTheorems =
      [ "verified_field_projection_preserves_recognition_identity"
      , "verified_field_projection_preserves_schema_identity_and_type"
      , "verified_field_projection_occurs_after_matching_commit"
      , "verified_field_projection_has_exact_call_shape_and_decision"
      , "verified_field_projection_feeds_exact_receive"
      , "verified_field_projection_output_has_unique_preceding_definition"
      , "field_projection_schema_drift_is_rejected"
      , "field_projection_before_commit_is_rejected"
      , "field_projection_decision_drift_is_rejected"
      , "field_projection_wrong_exact_receive_target_is_rejected"
      , "field_projection_non_dominating_output_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/FieldProjection.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/FieldProjection.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-FIELD-PROJ-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-FIELD-PROJ-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus correspondence from concrete Haskell Text/ValueId/BlockId identities, container enumeration, schema lookup, operation indexing, runtime-call rendering, and CFG dominance to the normalized proof model remain explicit trust boundaries."
  }

llvmFieldProjectionCertificationSpec :: RocqCertificationSpec
llvmFieldProjectionCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-field-projection"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-FIELD-PROJ-001"
  , rocqSpecClaim =
      "For a verified field-projection candidate, conservative Systems-to-LLVM translation preserves the exact ordinary semantic operation representing the recognized field projection, and loss or drift rejects. This claim does not select or assert a concrete recognized-record ABI or i64 load."
  , rocqSpecKind = "LLVM field-projection preservation"
  , rocqSpecOrigin = "src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/FieldProjection.v"
  , rocqSpecScope = "Phil.LLVM field projection"
  , rocqSpecRepresentation = "ordinary-operation projection digest"
  , rocqSpecSubjects = ["ordinary operation projection", "recognized Begin.length"]
  , rocqSpecTheorems =
      [ "verified_llvm_field_projection_rechecks_systems_source"
      , "verified_llvm_field_projection_preserves_exact_ordinary_operation"
      , "llvm_field_projection_loss_or_drift_is_rejected"
      , "llvm_field_projection_requires_generic_preservation_boundary"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/FieldProjection.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/FieldProjection.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-FIELD-PROJ-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-FIELD-PROJ-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness and correspondence from Phil.LLVM.Lower/Verify ordinary-operation projection digests to the normalized proof model remain explicit trust boundaries. The concrete recognized-record ABI remains deliberately unselected."
  }

knownRocqCertificationSpec :: Text -> Maybe RocqCertificationSpec
knownRocqCertificationSpec profile
  | profile == rocqSpecProfile coreScalarCertificationSpec = Just coreScalarCertificationSpec
  | profile == rocqSpecProfile systemsFieldProjectionCertificationSpec = Just systemsFieldProjectionCertificationSpec
  | profile == rocqSpecProfile llvmFieldProjectionCertificationSpec = Just llvmFieldProjectionCertificationSpec
  | otherwise = Nothing

specRevision :: RocqCertificationSpec -> ObligationRevision
specRevision spec = provisional { revisionId = deriveRevisionId provisional }
  where
    provisional = ObligationRevision
      { revisionObligationId = rocqSpecObligation spec
      , revisionId = RevisionId ""
      , revisionStatement = rocqSpecClaim spec
      , revisionStatementDigest = digestText (rocqSpecClaim spec)
      , revisionKind = rocqSpecKind spec
      , revisionOrigin = rocqSpecOrigin spec
      , revisionScope = rocqSpecScope spec
      , revisionRequiredAt = "certification"
      , revisionRepresentation = rocqSpecRepresentation spec
      , revisionSubjectIds = rocqSpecSubjects spec
      , revisionContextIds = ["rocq/9.2.0", "proof-assistant-theorem/v1"]
      , revisionAcceptanceRule =
          AcceptEntry ProofAssistantTheorem (EvidenceRole "establishes")
      , revisionGeneratedFrom = []
      }

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

certificateArtifact :: RocqCertificationSpec -> RocqProofCertificate -> ArtifactIdentity
certificateArtifact spec certificate = ArtifactIdentity
  { artifactReference = rocqSpecCertificateRef spec
  , artifactDigest = digestText (renderRocqProofCertificate certificate)
  }

specEvidence
  :: RocqCertificationSpec
  -> ObligationRevision
  -> RocqProofCertificate
  -> ArtifactIdentity
  -> EvidenceEntry
specEvidence spec revision certificate artifact = provisional
  { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = rocqSpecEvidenceId spec
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
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
      , evidenceValidityScope = certificationValidity
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = rocqSpecTheorems spec
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

certifyRocqProof
  :: RocqCertificationSpec
  -> ByteString.ByteString
  -> ByteString.ByteString
  -> Either RocqCertificationError RocqCertificationBundle
certifyRocqProof spec sourceBytes compiledBytes = do
  sourceText <- case TextEncoding.decodeUtf8' sourceBytes of
    Left _ -> Left RocqSourceIsNotUtf8
    Right value -> Right value
  let marker = unObligationId (rocqSpecObligation spec)
  unless (marker `Text.isInfixOf` sourceText) $
    Left (RocqObligationMarkerMissing marker)
  mapM_ (requireTheorem sourceText) (rocqSpecTheorems spec)

  let revision = specRevision spec
      sourceArtifact = ArtifactIdentity (rocqSpecSourceRef spec) (digestRawBytes sourceBytes)
      compiledArtifact = ArtifactIdentity (rocqSpecCompiledRef spec) (digestRawBytes compiledBytes)
      certificate = RocqProofCertificate
        { rocqCertificateObligation = revisionObligationId revision
        , rocqCertificateRevision = revisionId revision
        , rocqCertificateClaimDigest = revisionStatementDigest revision
        , rocqCertificateSourceArtifact = sourceArtifact
        , rocqCertificateCompiledArtifact = compiledArtifact
        , rocqCertificateTheorems = rocqSpecTheorems spec
        , rocqCertificateCheckerProfile = checkerProfile
        , rocqCertificateResidualBoundary = rocqSpecResidualBoundary spec
        }
      certArtifact = certificateArtifact spec certificate
      evidence = specEvidence spec revision certificate certArtifact
      ledger = emptyLedger
        { ledgerRevisions = Map.singleton (revisionId revision) revision
        , ledgerEvidence = Map.singleton (evidenceEntryId evidence) evidence
        }
      obligationText = unObligationId (rocqSpecObligation spec)
      architectureDigest = digestText (obligationText <> " Rocq certification architecture/v1")
      coreDigest = digestText "Phil assurance Rocq proof-certificate boundary/v1"
      loweringRoot = digestText "no-lowering/rocq-proof-certificate/v1"
      provisionalManifest = emptyManifest
        { manifestArchitectureDigest = architectureDigest
        , manifestPhilCoreDigest = coreDigest
        , manifestImplementationDigest = artifactDigest certArtifact
        , manifestTarget = "rocq-proof/" <> obligationText
        , manifestCompilationProfile = "rocq-9.2.0/proof-assistant-theorem/v1"
        , manifestObligationRevisions = Set.singleton (revisionId revision)
        , manifestCertificationScope = Set.singleton (revisionId revision)
        , manifestEvidenceEntries = Set.singleton (evidenceEntryId evidence)
        , manifestLoweringLedgerRoot = loweringRoot
        , manifestValidityContext = certificationValidityContext
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
        , verificationValidityContext = certificationValidityContext
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

certifyCoreScalarRocqProof
  :: ByteString.ByteString
  -> ByteString.ByteString
  -> Either RocqCertificationError RocqCertificationBundle
certifyCoreScalarRocqProof = certifyRocqProof coreScalarCertificationSpec

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
