{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types (Digest (..))
import Phil.Core.Static
  ( ArchitectureInstanceIdentity (..)
  , ArchitectureRealizationDescriptor (..)
  , InstanceKey
  , InstanceRevision (..)
  , RealizationRevision (..)
  , deriveArchitectureRealizationIdentity
  , identityRealizationRevision
  , renderArchitectureRealizationCanonical
  , unInstanceKey
  )
import Phil.Examples.Phase1.StageClosureWitnesses
  ( steveStageClosureBundle
  , uploadStageClosureBundle
  )
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveCoreProgram
  , steveQualifiedRealizationContext
  , steveStageInstanceKey
  , uploadCoreProgram
  , uploadRealizationContext
  , uploadStageInstanceKey
  )
import Phil.Handoff.Phase1RuntimeBuild
import Phil.Systems.CostAttribution
  ( AttributedCost (..)
  , CostAttributionStageBundle (..)
  , CostAttributionStageRevision (..)
  , renderCostAttributionStageCanonical
  , CostContributionIdentity (..)
  , CostChargeIdentity (..)
  , RuntimeCostBasis (..)
  )
import Phil.Systems.GenericLowering
  ( CoreSystemsProgram
  , GenericRealizationContext (..)
  , genericRealizationSemanticForm
  )
import Phil.Systems.IR
  ( CostClass (..)
  , DecisionId (..)
  , LoweringDecision (..)
  , LoweringLedger (..)
  , SystemsArtifact (..)
  , renderLoweringDecisionCanonical
  , renderStageContractCanonical
  , renderSystemsArtifactCanonical
  , renderSystemsProgramCanonical
  , stageContractDigest
  , systemsArtifactDigest
  , systemsProgramDigest
  )
import Phil.Systems.NextStageRequirement
  ( NextStageRequirementStageBundle (..)
  , NextStageRequirementStageRevision (..)
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  , Phase1StageContractRevision (..)
  , SystemsArtifactRevision (..)
  , normalizePhase1SystemsArtifact
  , renderPhase1StageContractCanonical
  )
import Phil.Systems.RuntimeClaimBinding
  ( PhysicalRuntimeCostIdentity (..)
  )
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveProfileRef (..)
  )
import Phil.Systems.StageClosure
  ( ClosedStageContractRevision (..)
  , StageClosureBundle (..)
  , concreteSubjectStage
  , renderClosedStageContractCanonical
  , verifyStageClosureBundle
  )
import Phil.Systems.StagingEffect
  ( StagingCostIdentity (..)
  )
import Phil.Systems.SubjectCorrespondence (SubjectStageBundle (..))
import System.Exit (exitFailure)

data WitnessRuntimeBuild = WitnessRuntimeBuild
  { witnessLabel :: String
  , witnessStage :: StageClosureBundle
  , witnessInstanceKey :: InstanceKey
  , witnessProgram :: CoreSystemsProgram
  , witnessContext :: GenericRealizationContext
  , witnessPrefix :: FilePath
  }

main :: IO ()
main = do
  upload <- requireWitness
    "Upload"
    uploadStageClosureBundle
    uploadStageInstanceKey
    uploadCoreProgram
    uploadRealizationContext
    "handoff/phase1/runtime/upload"
  steveContext <- case steveQualifiedRealizationContext of
    Left detail -> putStrLn ("FAIL: INT-007 Steve realization context -- " <> detail)
      >> exitFailure
    Right value -> pure value
  steve <- requireWitness
    "Steve"
    steveStageClosureBundle
    steveStageInstanceKey
    steveCoreProgram
    steveContext
    "handoff/phase1/runtime/steve"

  witnessResults <- mapM checkWitness [upload, steve]
  negativeResults <- sequence
    [ test "INT-007 runtime/build malformed realization digest fails closed"
        malformedRealizationDigestRejects
    , test "INT-007 runtime/build duplicate lowering decision fails closed"
        duplicateLoweringDecisionRejects
    , test "INT-007 runtime/build duplicate cost contribution fails closed"
        duplicateCostContributionRejects
    ]
  if and witnessResults && and negativeResults then pure () else exitFailure

requireWitness
  :: String
  -> Either String StageClosureBundle
  -> InstanceKey
  -> CoreSystemsProgram
  -> GenericRealizationContext
  -> FilePath
  -> IO WitnessRuntimeBuild
requireWitness label stageResult instanceKey program context prefix =
  case stageResult of
    Left detail -> putStrLn ("FAIL: INT-007 " <> label <> " StageClosure -- " <> detail)
      >> exitFailure
    Right stage -> case verifyStageClosureBundle stage of
      Left errorValue -> putStrLn
        ("FAIL: INT-007 " <> label <> " StageClosure verification -- " <> show errorValue)
        >> exitFailure
      Right () -> pure WitnessRuntimeBuild
        { witnessLabel = label
        , witnessStage = stage
        , witnessInstanceKey = instanceKey
        , witnessProgram = program
        , witnessContext = context
        , witnessPrefix = prefix
        }

checkWitness :: WitnessRuntimeBuild -> IO Bool
checkWitness witness = do
  derived <- case deriveWitnessSummaries witness of
    Left detail -> putStrLn ("FAIL: INT-007 " <> witnessLabel witness <> " " <> detail)
      >> pure Nothing
    Right value -> pure (Just value)
  case derived of
    Nothing -> pure False
    Just (realization, systems, stageContract, lowering, cost) -> do
      results <- sequence
        [ compareArtifact witness "realization"
            decodeRealizationSummary renderRealizationSummary realization
        , compareArtifact witness "systems"
            decodeSystemsSummary renderSystemsSummary systems
        , compareArtifact witness "stage-contract"
            decodeStageContractSummary renderStageContractSummary stageContract
        , compareArtifact witness "lowering"
            decodeLoweringSummary renderLoweringSummary lowering
        , compareArtifact witness "cost"
            decodeCostSummary renderCostSummary cost
        ]
      pure (and results)

compareArtifact
  :: (Eq a, Show e)
  => WitnessRuntimeBuild
  -> String
  -> (Text.Text -> Either e a)
  -> (a -> Text.Text)
  -> a
  -> IO Bool
compareArtifact witness kind decode render actual = do
  let path = witnessPrefix witness <> "-" <> kind <> "-v1.tsv"
  expectedSource <- TextIO.readFile path
  case decode expectedSource of
    Left errorValue -> do
      putStrLn ("FAIL: INT-007 " <> witnessLabel witness <> " " <> kind
        <> " decode -- " <> show errorValue)
      pure False
    Right expected
      | expected == actual -> do
          putStrLn ("PASS: INT-007 " <> witnessLabel witness <> " " <> kind
            <> " reconstructs exactly")
          pure True
      | otherwise -> do
          putStrLn ("FAIL: INT-007 " <> witnessLabel witness <> " " <> kind
            <> " summary drift")
          putStrLn ("ACTUAL " <> witnessLabel witness <> " "
            <> kind <> " SUMMARY BEGIN")
          TextIO.putStr (render actual)
          putStrLn ("ACTUAL " <> witnessLabel witness <> " "
            <> kind <> " SUMMARY END")
          pure False

deriveWitnessSummaries
  :: WitnessRuntimeBuild
  -> Either String
      ( Phase1RealizationSummary
      , Phase1SystemsSummary
      , Phase1StageContractSummary
      , Phase1LoweringSummary
      , Phase1CostSummary
      )
deriveWitnessSummaries witness = do
  let stage = witnessStage witness
      common = subjectStageBase (concreteSubjectStage (stageClosureConcrete stage))
      artifact = phase1StageSystemsArtifact common
      instanceRevision = phase1StageInstanceRevision common
      storedRealization = phase1StageRealizationRevision common
      instanceIdentity = ArchitectureInstanceIdentity
        { identityInstanceKey = witnessInstanceKey witness
        , identityInstanceRevision = instanceRevision
        }
      semantics = genericRealizationSemanticForm
        (witnessProgram witness) (witnessContext witness)
      realizationDescriptor = ArchitectureRealizationDescriptor
        { realizationInstanceIdentity = instanceIdentity
        , realizationSemantics = semantics
        }
      rederivedRealization = identityRealizationRevision
        (deriveArchitectureRealizationIdentity realizationDescriptor)
  if rederivedRealization /= storedRealization
    then Left ("artifact-side ArchitectureRealization revision mismatch: stored="
      <> show storedRealization <> ", rederived=" <> show rederivedRealization)
    else Right ()
  let normalizedArtifact = normalizePhase1SystemsArtifact artifact
      realization = Phase1RealizationSummary
        { realizationInstanceKey = unInstanceKey (witnessInstanceKey witness)
        , realizationInstanceRevision = unInstanceRevision instanceRevision
        , realizationRevision = unRealizationRevision storedRealization
        , realizationContextRevision =
            genericContextRevision (witnessContext witness)
        , realizationCanonical =
            renderArchitectureRealizationCanonical realizationDescriptor
        }
      systems = Phase1SystemsSummary
        { systemsArtifactRevision =
            unSystemsArtifactRevision (stageClosureSystemsArtifactRevision stage)
        , systemsRevisionCanonical =
            renderSystemsArtifactCanonical normalizedArtifact
        , systemsArtifactSha256 = digestToken (systemsArtifactDigest artifact)
        , systemsArtifactCanonical = renderSystemsArtifactCanonical artifact
        , systemsProgramSha256 =
            digestToken (systemsProgramDigest (systemsArtifactProgram artifact))
        , systemsProgramCanonical =
            renderSystemsProgramCanonical (systemsArtifactProgram artifact)
        , systemsStageContractSha256 =
            digestToken (stageContractDigest (systemsArtifactStageContract artifact))
        , systemsStageContractCanonical =
            renderStageContractCanonical (systemsArtifactStageContract artifact)
        }
      stageContract = Phase1StageContractSummary
        { stagePhase1Revision =
            unPhase1StageContractRevision (phase1StageContractRevision common)
        , stagePhase1Canonical = renderPhase1StageContractCanonical common
        , stageClosedRevision =
            unClosedStageContractRevision (stageClosureContractRevision stage)
        , stageClosedCanonical = renderClosedStageContractCanonical stage
        , stageNextRequirementRevision =
            unNextStageRequirementStageRevision
              (nextStageRequirementStageRevision (stageClosureNextStage stage))
        , stageVerifierProfile = phase1StageVerifierProfileRevision common
        }
      ledger = systemsArtifactLoweringLedger artifact
      lowering = Phase1LoweringSummary
        { loweringRootSha256 = digestToken (loweringLedgerRoot ledger)
        , loweringDecisions =
            [ Phase1LoweringDecisionSummary
                (unDecisionId decisionId)
                (digestToken (loweringDecisionDigest decision))
                (renderLoweringDecisionCanonical decision)
            | (decisionId, decision) <- Map.toAscList
                (loweringLedgerDecisions ledger)
            ]
        }
      costBundle = nextStageRequirementStageBase (stageClosureNextStage stage)
      cost = deriveCostSummary costBundle
  Right (realization, systems, stageContract, lowering, cost)

deriveCostSummary :: CostAttributionStageBundle -> Phase1CostSummary
deriveCostSummary bundle = Phase1CostSummary
  { costStageRevision =
      unCostAttributionStageRevision (costAttributionStageRevision bundle)
  , costStageCanonical = renderCostAttributionStageCanonical bundle
  , costRuntimeBases =
      [ Phase1RuntimeCostBasisSummary
          (unRuntimePrimitiveProfileRef profile)
          (unDecisionId (runtimeCostBasisDecision basis))
          (unCostChargeIdentity (runtimeCostBasisCharge basis))
      | (profile, basis) <- Map.toAscList
          (costAttributionStageRuntimeBases bundle)
      ]
  , costContributions =
      [ contributionSummary identity charge
      | (identity, charge) <- Map.toAscList
          (costAttributionStageContributionCharges bundle)
      ]
  , costCharges =
      [ Phase1CostChargeSummary
          (unCostChargeIdentity chargeId)
          (costClassToken (attributedCostClass charge))
          (Set.size (attributedCostContributions charge))
          (Set.size (attributedCostRuntimeClaims charge))
      | (chargeId, charge) <- Map.toAscList
          (costAttributionStageCharges bundle)
      ]
  }
  where
    contributionSummary identity charge = case identity of
      RuntimeCostContribution physical ->
        RuntimeCostContributionSummary
          (unPhysicalRuntimeCostIdentity physical)
          (unCostChargeIdentity charge)
      StagingCostContribution staging ->
        StagingCostContributionSummary
          (unStagingCostIdentity staging)
          (unCostChargeIdentity charge)

costClassToken :: CostClass -> Text.Text
costClassToken value = case value of
  SemanticRequired -> "semantic-required"
  RuntimeAssuranceRequired -> "runtime-assurance-required"
  TargetRequired -> "target-required"
  DefensiveProfile -> "defensive-profile"
  ConservativeLowering -> "conservative-lowering"

digestToken :: Digest -> Text.Text
digestToken (Digest value) = "sha256:" <> value


malformedRealizationDigestRejects :: Either String ()
malformedRealizationDigestRejects =
  expectFailure (decodeRealizationSummary (Text.unlines
    [ realizationFormatV1
    , "instance-key\ti"
    , "instance-revision\ti"
    , "realization-revision\tphil.realization.canonical.v1:seed"
    , "context-revision\tc"
    , "canonical\tzz"
    ]))

duplicateLoweringDecisionRejects :: Either String ()
duplicateLoweringDecisionRejects =
  expectFailure (decodeLoweringSummary (Text.unlines
    [ loweringFormatV1
    , "root\tsha256:0000000000000000000000000000000000000000000000000000000000000000"
    , "decision\td\tsha256:0000000000000000000000000000000000000000000000000000000000000000"
    , "decision\td\tsha256:0000000000000000000000000000000000000000000000000000000000000000"
    ]))

duplicateCostContributionRejects :: Either String ()
duplicateCostContributionRejects =
  expectFailure (decodeCostSummary (Text.unlines
    [ costFormatV1
    , "stage\ts"
    , "contribution-runtime\tc\tq"
    , "contribution-runtime\tc\tq"
    ]))

expectFailure :: Either a b -> Either String ()
expectFailure result = case result of
  Left _ -> Right ()
  Right _ -> Left "expected portable runtime/build summary rejection"

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False
