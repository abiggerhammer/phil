{-# LANGUAGE OverloadedStrings #-}

module Phil.Handoff.Phase1RuntimeBuild
  ( Phase1RealizationSummary (..)
  , Phase1SystemsSummary (..)
  , Phase1StageContractSummary (..)
  , Phase1LoweringSummary (..)
  , Phase1CostSummary (..)
  , Phase1LoweringDecisionSummary (..)
  , Phase1RuntimeCostBasisSummary (..)
  , Phase1CostContributionSummary (..)
  , Phase1CostChargeSummary (..)
  , Phase1RuntimeBuildDecodeError (..)
  , realizationFormatV1
  , systemsFormatV1
  , stageContractFormatV1
  , loweringFormatV1
  , costFormatV1
  , renderRealizationSummary
  , renderSystemsSummary
  , renderStageContractSummary
  , renderLoweringSummary
  , renderCostSummary
  , decodeRealizationSummary
  , decodeSystemsSummary
  , decodeStageContractSummary
  , decodeLoweringSummary
  , decodeCostSummary
  ) where

import Control.Monad (foldM)
import qualified Data.ByteString as ByteString
import Data.Char (isDigit)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Numeric (showHex)
import Phil.Assurance.Types (Digest (..), digestText)

data Phase1RealizationSummary = Phase1RealizationSummary
  { realizationInstanceKey :: Text
  , realizationInstanceRevision :: Text
  , realizationRevision :: Text
  , realizationContextRevision :: Text
  , realizationCanonical :: Text
  }
  deriving (Eq, Show)

data Phase1SystemsSummary = Phase1SystemsSummary
  { systemsArtifactRevision :: Text
  , systemsRevisionCanonical :: Text
  , systemsArtifactSha256 :: Text
  , systemsArtifactCanonical :: Text
  , systemsProgramSha256 :: Text
  , systemsProgramCanonical :: Text
  , systemsStageContractSha256 :: Text
  , systemsStageContractCanonical :: Text
  }
  deriving (Eq, Show)

data Phase1StageContractSummary = Phase1StageContractSummary
  { stagePhase1Revision :: Text
  , stagePhase1Canonical :: Text
  , stageClosedRevision :: Text
  , stageClosedCanonical :: Text
  , stageNextRequirementRevision :: Text
  , stageVerifierProfile :: Text
  }
  deriving (Eq, Show)

data Phase1LoweringDecisionSummary = Phase1LoweringDecisionSummary
  { loweringDecisionKey :: Text
  , loweringDecisionSha256 :: Text
  , loweringDecisionCanonical :: Text
  }
  deriving (Eq, Ord, Show)

data Phase1LoweringSummary = Phase1LoweringSummary
  { loweringRootSha256 :: Text
  , loweringDecisions :: [Phase1LoweringDecisionSummary]
  }
  deriving (Eq, Show)

data Phase1RuntimeCostBasisSummary = Phase1RuntimeCostBasisSummary
  { runtimeCostProfile :: Text
  , runtimeCostDecision :: Text
  , runtimeCostCharge :: Text
  }
  deriving (Eq, Ord, Show)

data Phase1CostContributionSummary
  = RuntimeCostContributionSummary
      { costContributionIdentity :: Text
      , costContributionCharge :: Text
      }
  | StagingCostContributionSummary
      { costContributionIdentity :: Text
      , costContributionCharge :: Text
      }
  deriving (Eq, Ord, Show)

data Phase1CostChargeSummary = Phase1CostChargeSummary
  { costChargeIdentity :: Text
  , costChargeClass :: Text
  , costChargeContributionCount :: Int
  , costChargeClaimCount :: Int
  }
  deriving (Eq, Ord, Show)

data Phase1CostSummary = Phase1CostSummary
  { costStageRevision :: Text
  , costStageCanonical :: Text
  , costRuntimeBases :: [Phase1RuntimeCostBasisSummary]
  , costContributions :: [Phase1CostContributionSummary]
  , costCharges :: [Phase1CostChargeSummary]
  }
  deriving (Eq, Show)

newtype Phase1RuntimeBuildDecodeError = Phase1RuntimeBuildDecodeError Text
  deriving (Eq, Show)

realizationFormatV1, systemsFormatV1, stageContractFormatV1, loweringFormatV1, costFormatV1 :: Text
realizationFormatV1 = "PHIL-PHASE1-ARCHITECTURE-REALIZATION-V1"
systemsFormatV1 = "PHIL-PHASE1-SYSTEMS-ARTIFACT-V1"
stageContractFormatV1 = "PHIL-PHASE1-STAGE-CONTRACT-V1"
loweringFormatV1 = "PHIL-PHASE1-LOWERING-V1"
costFormatV1 = "PHIL-PHASE1-COST-ARTIFACT-V1"

renderRealizationSummary :: Phase1RealizationSummary -> Text
renderRealizationSummary value = Text.unlines
  [ realizationFormatV1
  , row ["instance-key", realizationInstanceKey value]
  , row ["instance-revision", realizationInstanceRevision value]
  , row ["realization-revision", realizationRevision value]
  , row ["context-revision", realizationContextRevision value]
  , row ["canonical", hexText (realizationCanonical value)]
  ]

renderSystemsSummary :: Phase1SystemsSummary -> Text
renderSystemsSummary value = Text.unlines
  [ systemsFormatV1
  , row ["systems-revision", systemsArtifactRevision value]
  , row ["revision-canonical", hexText (systemsRevisionCanonical value)]
  , row ["artifact", systemsArtifactSha256 value]
  , row ["artifact-canonical", hexText (systemsArtifactCanonical value)]
  , row ["program", systemsProgramSha256 value]
  , row ["program-canonical", hexText (systemsProgramCanonical value)]
  , row ["stage-contract", systemsStageContractSha256 value]
  , row ["stage-contract-canonical", hexText (systemsStageContractCanonical value)]
  ]

renderStageContractSummary :: Phase1StageContractSummary -> Text
renderStageContractSummary value = Text.unlines
  [ stageContractFormatV1
  , row ["phase1-stage", stagePhase1Revision value]
  , row ["phase1-canonical", hexText (stagePhase1Canonical value)]
  , row ["closed-stage", stageClosedRevision value]
  , row ["closed-canonical", hexText (stageClosedCanonical value)]
  , row ["next-stage", stageNextRequirementRevision value]
  , row ["verifier-profile", stageVerifierProfile value]
  ]

renderLoweringSummary :: Phase1LoweringSummary -> Text
renderLoweringSummary value = Text.unlines $
  [ loweringFormatV1
  , row ["root", loweringRootSha256 value]
  ]
  <> [ row
        [ "decision"
        , loweringDecisionKey decision
        , loweringDecisionSha256 decision
        , hexText (loweringDecisionCanonical decision)
        ]
     | decision <- loweringDecisions value
     ]

renderCostSummary :: Phase1CostSummary -> Text
renderCostSummary value = Text.unlines $
  [ costFormatV1
  , row ["stage", costStageRevision value]
  , row ["canonical", hexText (costStageCanonical value)]
  ]
  <> [ row ["basis", runtimeCostProfile basis, runtimeCostDecision basis, runtimeCostCharge basis]
     | basis <- costRuntimeBases value
     ]
  <> [ case contribution of
         RuntimeCostContributionSummary identity charge ->
           row ["contribution-runtime", identity, charge]
         StagingCostContributionSummary identity charge ->
           row ["contribution-staging", identity, charge]
     | contribution <- costContributions value
     ]
  <> [ row
        [ "charge"
        , costChargeIdentity charge
        , costChargeClass charge
        , Text.pack (show (costChargeContributionCount charge))
        , Text.pack (show (costChargeClaimCount charge))
        ]
     | charge <- costCharges value
     ]

decodeRealizationSummary :: Text -> Either Phase1RuntimeBuildDecodeError Phase1RealizationSummary
decodeRealizationSummary source = do
  rows <- parseRows realizationFormatV1 source
  instanceKey <- requireOne "instance-key" rows
  instanceRevision <- requireOne "instance-revision" rows
  revision <- requireOne "realization-revision" rows
  contextRevision <- requireOne "context-revision" rows
  canonical <- requireOne "canonical" rows >>= decodeHex
  requireEqual "ArchitectureRealization revision"
    ("phil.realization.canonical.v1:" <> canonical) revision
  Right Phase1RealizationSummary
    { realizationInstanceKey = instanceKey
    , realizationInstanceRevision = instanceRevision
    , realizationRevision = revision
    , realizationContextRevision = contextRevision
    , realizationCanonical = canonical
    }

decodeSystemsSummary :: Text -> Either Phase1RuntimeBuildDecodeError Phase1SystemsSummary
decodeSystemsSummary source = do
  rows <- parseRows systemsFormatV1 source
  revision <- requireOne "systems-revision" rows
  revisionCanonical <- requireOne "revision-canonical" rows >>= decodeHex
  artifactDigest <- requireOne "artifact" rows >>= requireDigest
  artifactCanonical <- requireOne "artifact-canonical" rows >>= decodeHex
  programDigest <- requireOne "program" rows >>= requireDigest
  programCanonical <- requireOne "program-canonical" rows >>= decodeHex
  contractDigest <- requireOne "stage-contract" rows >>= requireDigest
  contractCanonical <- requireOne "stage-contract-canonical" rows >>= decodeHex
  requireBareDigestMatches "SystemsArtifactRevision" revisionCanonical revision
  requireDigestMatches "Systems artifact" artifactCanonical artifactDigest
  requireDigestMatches "Systems program" programCanonical programDigest
  requireDigestMatches "Systems StageContract" contractCanonical contractDigest
  Right Phase1SystemsSummary
    { systemsArtifactRevision = revision
    , systemsRevisionCanonical = revisionCanonical
    , systemsArtifactSha256 = artifactDigest
    , systemsArtifactCanonical = artifactCanonical
    , systemsProgramSha256 = programDigest
    , systemsProgramCanonical = programCanonical
    , systemsStageContractSha256 = contractDigest
    , systemsStageContractCanonical = contractCanonical
    }

decodeStageContractSummary :: Text -> Either Phase1RuntimeBuildDecodeError Phase1StageContractSummary
decodeStageContractSummary source = do
  rows <- parseRows stageContractFormatV1 source
  phase1Revision <- requireOne "phase1-stage" rows
  phase1Canonical <- requireOne "phase1-canonical" rows >>= decodeHex
  closedRevision <- requireOne "closed-stage" rows
  closedCanonical <- requireOne "closed-canonical" rows >>= decodeHex
  nextRevision <- requireOne "next-stage" rows
  verifier <- requireOne "verifier-profile" rows
  requireEqual "Phase-1 StageContract revision"
    ("phil.phase1.stage.canonical.v1:" <> phase1Canonical)
    phase1Revision
  requireEqual "closed StageContract revision"
    ("phil.phase1.stage.closed.canonical.v1:" <> closedCanonical)
    closedRevision
  Right Phase1StageContractSummary
    { stagePhase1Revision = phase1Revision
    , stagePhase1Canonical = phase1Canonical
    , stageClosedRevision = closedRevision
    , stageClosedCanonical = closedCanonical
    , stageNextRequirementRevision = nextRevision
    , stageVerifierProfile = verifier
    }

decodeLoweringSummary :: Text -> Either Phase1RuntimeBuildDecodeError Phase1LoweringSummary
decodeLoweringSummary source = do
  rows <- parseRows loweringFormatV1 source
  root <- requireOne "root" rows >>= requireDigest
  decisions <- mapM decodeDecision (Map.findWithDefault [] "decision" rows)
  let ordered = sort decisions
  ensureUnique "lowering decision" loweringDecisionKey ordered
  mapM_ validateDecision ordered
  requireEqual "lowering ledger root"
    (loweringRootFor ordered) root
  Right Phase1LoweringSummary
    { loweringRootSha256 = root
    , loweringDecisions = ordered
    }
  where
    decodeDecision fields = case fields of
      [key, digest, rawCanonical] -> do
        checked <- requireDigest digest
        canonical <- decodeHex rawCanonical
        Right (Phase1LoweringDecisionSummary key checked canonical)
      _ -> malformed "malformed lowering decision row"

    validateDecision decision =
      requireDigestMatches "lowering decision"
        (loweringDecisionCanonical decision)
        (loweringDecisionSha256 decision)

decodeCostSummary :: Text -> Either Phase1RuntimeBuildDecodeError Phase1CostSummary
decodeCostSummary source = do
  rows <- parseRows costFormatV1 source
  stage <- requireOne "stage" rows
  canonical <- requireOne "canonical" rows >>= decodeHex
  requireEqual "cost-attribution stage revision"
    ("phil.phase1.stage.cost-attribution.canonical.v1:" <> canonical)
    stage
  bases <- mapM decodeBasis (Map.findWithDefault [] "basis" rows)
  runtime <- mapM (decodeContribution True)
    (Map.findWithDefault [] "contribution-runtime" rows)
  staging <- mapM (decodeContribution False)
    (Map.findWithDefault [] "contribution-staging" rows)
  charges <- mapM decodeCharge (Map.findWithDefault [] "charge" rows)
  let orderedBases = sort bases
      orderedContributions = sort (runtime <> staging)
      orderedCharges = sort charges
  ensureUnique "runtime cost profile" runtimeCostProfile orderedBases
  ensureUnique "cost contribution" costContributionIdentity orderedContributions
  ensureUnique "cost charge" costChargeIdentity orderedCharges
  Right Phase1CostSummary
    { costStageRevision = stage
    , costStageCanonical = canonical
    , costRuntimeBases = orderedBases
    , costContributions = orderedContributions
    , costCharges = orderedCharges
    }
  where
    decodeBasis fields = case fields of
      [profile, decision, charge] ->
        Right (Phase1RuntimeCostBasisSummary profile decision charge)
      _ -> malformed "malformed runtime cost basis row"

    decodeContribution isRuntime fields = case fields of
      [identity, charge]
        | isRuntime -> Right (RuntimeCostContributionSummary identity charge)
        | otherwise -> Right (StagingCostContributionSummary identity charge)
      _ -> malformed "malformed cost contribution row"

    decodeCharge fields = case fields of
      [identity, className, contributionCount, claimCount] -> do
        contributions <- parseCount contributionCount
        claims <- parseCount claimCount
        Right (Phase1CostChargeSummary identity className contributions claims)
      _ -> malformed "malformed cost charge row"

loweringRootFor :: [Phase1LoweringDecisionSummary] -> Text
loweringRootFor decisions =
  digestToken . digestText . Text.intercalate "|" $
    [ loweringDecisionKey decision <> "="
        <> bareDigest (loweringDecisionSha256 decision)
    | decision <- sort decisions
    ]

parseRows
  :: Text
  -> Text
  -> Either Phase1RuntimeBuildDecodeError (Map.Map Text [[Text]])
parseRows expected source =
  case Text.lines source of
    [] -> malformed "empty runtime/build summary"
    header : body
      | Text.strip header /= expected ->
          malformed ("unexpected header: " <> Text.strip header)
      | otherwise -> foldM add Map.empty (zip [2 :: Int ..] body)
  where
    add rows (lineNumber, raw)
      | Text.null (Text.strip raw) = Right rows
      | "#" `Text.isPrefixOf` Text.strip raw = Right rows
      | otherwise =
          case Text.splitOn "\t" raw of
            [] -> malformedAt lineNumber "empty row"
            key : fields
              | Text.null key -> malformedAt lineNumber "empty row key"
              | otherwise -> Right (Map.insertWith (<>) key [fields] rows)

requireOne
  :: Text
  -> Map.Map Text [[Text]]
  -> Either Phase1RuntimeBuildDecodeError Text
requireOne key rows =
  case Map.lookup key rows of
    Just [[value]]
      | not (Text.null value) -> Right value
    Nothing -> malformed ("missing row: " <> key)
    _ -> malformed ("duplicate or malformed row: " <> key)

requireDigest :: Text -> Either Phase1RuntimeBuildDecodeError Text
requireDigest raw =
  case Text.stripPrefix "sha256:" raw of
    Just digest
      | Text.length digest == 64
      , Text.all lowerHex digest -> Right raw
    _ -> malformed ("malformed SHA-256 digest: " <> raw)
  where
    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')

requireDigestMatches :: Text -> Text -> Text -> Either Phase1RuntimeBuildDecodeError ()
requireDigestMatches label canonical expected =
  requireEqual label (digestToken (digestText canonical)) expected

requireBareDigestMatches :: Text -> Text -> Text -> Either Phase1RuntimeBuildDecodeError ()
requireBareDigestMatches label canonical expected = do
  requireBareDigest expected
  requireEqual label (bareDigest (digestToken (digestText canonical))) expected

requireBareDigest :: Text -> Either Phase1RuntimeBuildDecodeError ()
requireBareDigest raw
  | Text.length raw == 64
  , Text.all lowerHex raw = Right ()
  | otherwise = malformed ("malformed bare SHA-256 digest: " <> raw)
  where
    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')

requireEqual :: Text -> Text -> Text -> Either Phase1RuntimeBuildDecodeError ()
requireEqual label expected actual
  | expected == actual = Right ()
  | otherwise = malformed
      (label <> " mismatch: expected " <> expected <> ", got " <> actual)

ensureUnique
  :: Ord key
  => Text
  -> (value -> key)
  -> [value]
  -> Either Phase1RuntimeBuildDecodeError ()
ensureUnique label project values =
  if Set.size keys == length values
    then Right ()
    else malformed ("duplicate " <> label)
  where
    keys = Set.fromList (map project values)

parseCount :: Text -> Either Phase1RuntimeBuildDecodeError Int
parseCount raw =
  case reads (Text.unpack raw) of
    [(value, "")]
      | value >= 0 -> Right value
    _ -> malformed ("malformed nonnegative count: " <> raw)

hexText :: Text -> Text
hexText value =
  Text.pack (concatMap hexByte (ByteString.unpack (TextEncoding.encodeUtf8 value)))
  where
    hexByte byte = case showHex byte "" of
      [digit] -> ['0', digit]
      digits -> digits

decodeHex :: Text -> Either Phase1RuntimeBuildDecodeError Text
decodeHex raw
  | odd (Text.length raw) = malformed "odd-length canonical hex text"
  | Text.any (not . lowerHex) raw = malformed "invalid canonical hex text"
  | otherwise =
      case TextEncoding.decodeUtf8' (ByteString.pack (decodeBytes (Text.unpack raw))) of
        Left _ -> malformed "canonical hex text is not valid UTF-8"
        Right value -> Right value
  where
    decodeBytes [] = []
    decodeBytes (high : low : rest) =
      fromIntegral (hexValue high * 16 + hexValue low) : decodeBytes rest
    decodeBytes _ = []
    hexValue character
      | isDigit character = fromEnum character - fromEnum '0'
      | otherwise = 10 + fromEnum character - fromEnum 'a'
    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')

digestToken :: Digest -> Text
digestToken (Digest value) = "sha256:" <> value

bareDigest :: Text -> Text
bareDigest raw = maybe raw id (Text.stripPrefix "sha256:" raw)

row :: [Text] -> Text
row = Text.intercalate "\t"

malformed :: Text -> Either Phase1RuntimeBuildDecodeError a
malformed = Left . Phase1RuntimeBuildDecodeError

malformedAt :: Int -> Text -> Either Phase1RuntimeBuildDecodeError a
malformedAt lineNumber detail =
  malformed ("line " <> Text.pack (show lineNumber) <> ": " <> detail)
