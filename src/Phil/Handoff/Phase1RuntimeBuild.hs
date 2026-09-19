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
import Data.Char (isDigit)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text

data Phase1RealizationSummary = Phase1RealizationSummary
  { realizationInstanceRevision :: Text
  , realizationRevision :: Text
  , realizationContextRevision :: Text
  , realizationSemanticsSha256 :: Text
  }
  deriving (Eq, Show)

data Phase1SystemsSummary = Phase1SystemsSummary
  { systemsArtifactRevision :: Text
  , systemsArtifactSha256 :: Text
  , systemsProgramSha256 :: Text
  , systemsStageContractSha256 :: Text
  }
  deriving (Eq, Show)

data Phase1StageContractSummary = Phase1StageContractSummary
  { stagePhase1Revision :: Text
  , stageClosedRevision :: Text
  , stageNextRequirementRevision :: Text
  , stageVerifierProfile :: Text
  }
  deriving (Eq, Show)

data Phase1LoweringDecisionSummary = Phase1LoweringDecisionSummary
  { loweringDecisionKey :: Text
  , loweringDecisionSha256 :: Text
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
  , row ["instance-revision", realizationInstanceRevision value]
  , row ["realization-revision", realizationRevision value]
  , row ["context-revision", realizationContextRevision value]
  , row ["semantics", realizationSemanticsSha256 value]
  ]

renderSystemsSummary :: Phase1SystemsSummary -> Text
renderSystemsSummary value = Text.unlines
  [ systemsFormatV1
  , row ["systems-revision", systemsArtifactRevision value]
  , row ["artifact", systemsArtifactSha256 value]
  , row ["program", systemsProgramSha256 value]
  , row ["stage-contract", systemsStageContractSha256 value]
  ]

renderStageContractSummary :: Phase1StageContractSummary -> Text
renderStageContractSummary value = Text.unlines
  [ stageContractFormatV1
  , row ["phase1-stage", stagePhase1Revision value]
  , row ["closed-stage", stageClosedRevision value]
  , row ["next-stage", stageNextRequirementRevision value]
  , row ["verifier-profile", stageVerifierProfile value]
  ]

renderLoweringSummary :: Phase1LoweringSummary -> Text
renderLoweringSummary value = Text.unlines $
  [ loweringFormatV1
  , row ["root", loweringRootSha256 value]
  ]
  <> [ row ["decision", loweringDecisionKey decision, loweringDecisionSha256 decision]
     | decision <- loweringDecisions value
     ]

renderCostSummary :: Phase1CostSummary -> Text
renderCostSummary value = Text.unlines $
  [ costFormatV1
  , row ["stage", costStageRevision value]
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
  Phase1RealizationSummary
    <$> requireOne "instance-revision" rows
    <*> requireOne "realization-revision" rows
    <*> requireOne "context-revision" rows
    <*> (requireOne "semantics" rows >>= requireDigest)

decodeSystemsSummary :: Text -> Either Phase1RuntimeBuildDecodeError Phase1SystemsSummary
decodeSystemsSummary source = do
  rows <- parseRows systemsFormatV1 source
  Phase1SystemsSummary
    <$> requireOne "systems-revision" rows
    <*> (requireOne "artifact" rows >>= requireDigest)
    <*> (requireOne "program" rows >>= requireDigest)
    <*> (requireOne "stage-contract" rows >>= requireDigest)

decodeStageContractSummary :: Text -> Either Phase1RuntimeBuildDecodeError Phase1StageContractSummary
decodeStageContractSummary source = do
  rows <- parseRows stageContractFormatV1 source
  Phase1StageContractSummary
    <$> requireOne "phase1-stage" rows
    <*> requireOne "closed-stage" rows
    <*> requireOne "next-stage" rows
    <*> requireOne "verifier-profile" rows

decodeLoweringSummary :: Text -> Either Phase1RuntimeBuildDecodeError Phase1LoweringSummary
decodeLoweringSummary source = do
  rows <- parseRows loweringFormatV1 source
  root <- requireOne "root" rows >>= requireDigest
  decisions <- mapM decodeDecision (Map.findWithDefault [] "decision" rows)
  ensureUnique "lowering decision" loweringDecisionKey decisions
  Right Phase1LoweringSummary
    { loweringRootSha256 = root
    , loweringDecisions = decisions
    }
  where
    decodeDecision fields = case fields of
      [key, digest] -> do
        checked <- requireDigest digest
        Right (Phase1LoweringDecisionSummary key checked)
      _ -> malformed "malformed lowering decision row"

decodeCostSummary :: Text -> Either Phase1RuntimeBuildDecodeError Phase1CostSummary
decodeCostSummary source = do
  rows <- parseRows costFormatV1 source
  stage <- requireOne "stage" rows
  bases <- mapM decodeBasis (Map.findWithDefault [] "basis" rows)
  runtime <- mapM (decodeContribution True)
    (Map.findWithDefault [] "contribution-runtime" rows)
  staging <- mapM (decodeContribution False)
    (Map.findWithDefault [] "contribution-staging" rows)
  charges <- mapM decodeCharge (Map.findWithDefault [] "charge" rows)
  ensureUnique "runtime cost profile" runtimeCostProfile bases
  ensureUnique "cost contribution" costContributionIdentity (runtime <> staging)
  ensureUnique "cost charge" costChargeIdentity charges
  Right Phase1CostSummary
    { costStageRevision = stage
    , costRuntimeBases = bases
    , costContributions = runtime <> staging
    , costCharges = charges
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

row :: [Text] -> Text
row = Text.intercalate "\t"

malformed :: Text -> Either Phase1RuntimeBuildDecodeError a
malformed = Left . Phase1RuntimeBuildDecodeError

malformedAt :: Int -> Text -> Either Phase1RuntimeBuildDecodeError a
malformedAt lineNumber detail =
  malformed ("line " <> Text.pack (show lineNumber) <> ": " <> detail)
