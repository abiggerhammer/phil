{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Compiler.RuntimeChoicePayload
import Phil.Compiler.RuntimeChoiceSystems
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveCoreProgram
  , stevePhase1StageBundle
  , uploadCoreProgram
  , uploadPhase1StageBundle
  )
import Phil.Systems.IR
import Phil.Systems.Phase1Stage
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("certified payload plan binds into a resealed Steve stage", positive)
        , ("computed content id survives into put.install", computedPayload)
        , ("found bytes survive into get.check", foundPayload)
        , ("payload binding changes Systems and stage identity", identityChanges)
        , ("payload plan rejects a different checked-Core program", wrongCoreRejects)
        , ("payload plan rejects a different Systems stage", wrongStageRejects)
        , ("payload binding cannot be applied twice", duplicateBindingRejects)
        ]
  results <- mapM report checks
  if and results then pure () else exitFailure

report :: (String, Bool) -> IO Bool
report (label, ok) = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> "INT-006 " <> label)
  pure ok

positive :: Bool
positive = case boundStage of
  Left _ -> False
  Right (_, bound) -> verifyPhase1StageBundle bound == Right ()

computedPayload :: Bool
computedPayload =
  payloadAt "StevePut" "put.entry" "computed" == Just (ValueId "put.id")

foundPayload :: Bool
foundPayload =
  payloadAt "SteveGet" "get.entry" "found" == Just (ValueId "get.bytes")

identityChanges :: Bool
identityChanges = case boundStage of
  Left _ -> False
  Right (base, bound) ->
    phase1StageSystemsArtifactRevision base /= phase1StageSystemsArtifactRevision bound
      && phase1StageContractRevision base /= phase1StageContractRevision bound
      && loweringLedgerRoot
          (systemsArtifactLoweringLedger (phase1StageSystemsArtifact base))
        /= loweringLedgerRoot
          (systemsArtifactLoweringLedger (phase1StageSystemsArtifact bound))

wrongCoreRejects :: Bool
wrongCoreRejects = case stevePlan of
  Left _ -> False
  Right plan -> case bindRuntimeChoicePayloadPlan
      uploadCoreProgram plan uploadPhase1StageBundle of
    Left _ -> True
    Right _ -> False

wrongStageRejects :: Bool
wrongStageRejects = case stevePlan of
  Left _ -> False
  Right plan -> case bindRuntimeChoicePayloadPlan
      steveCoreProgram plan uploadPhase1StageBundle of
    Left RuntimeChoiceSystemsFunctionMissing {} -> True
    Left RuntimeChoiceSystemsBlockMissing {} -> True
    _ -> False

duplicateBindingRejects :: Bool
duplicateBindingRejects = case boundStage of
  Left _ -> False
  Right (_, bound) -> case stevePlan of
    Left _ -> False
    Right plan -> case bindRuntimeChoicePayloadPlan steveCoreProgram plan bound of
      Left RuntimeChoiceSystemsDecisionCollision {} -> True
      _ -> False

payloadAt :: Text.Text -> Text.Text -> Text.Text -> Maybe ValueId
payloadAt functionName blockName label = do
  (_, bound) <- either (const Nothing) Just boundStage
  function <- Map.lookup functionName
    (systemsProgramFunctions
      (systemsArtifactProgram (phase1StageSystemsArtifact bound)))
  blockValue <- Map.lookup (BlockId blockName) (systemsFunctionBlocks function)
  case systemsBlockTerminator blockValue of
    TermRuntimeChoice { runtimeChoiceArms = arms } -> do
      armValue <- Map.lookup label arms
      runtimeChoiceArmPayloadBinding armValue
    _ -> Nothing

boundStage :: Either String (Phase1StageBundle, Phase1StageBundle)
boundStage = do
  base <- stevePhase1StageBundle
  plan <- mapLeft show $
    certifyRuntimeChoicePayloadPlan steveCoreProgram stevePayloadSpecs
  bound <- mapLeft show $
    bindRuntimeChoicePayloadPlan steveCoreProgram plan base
  pure (base, bound)

stevePlan :: Either String RuntimeChoicePayloadPlan
stevePlan = mapLeft show $
  certifyRuntimeChoicePayloadPlan steveCoreProgram stevePayloadSpecs

stevePayloadSpecs :: [RuntimeChoicePayloadSpec]
stevePayloadSpecs =
  [ spec "StevePut" "put.entry"
      [arm "computed" "put.install" (Just "put.id")]
  , spec "StevePut" "put.install"
      [ arm "installed" "put.ok" Nothing
      , arm "already-exists" "put.ok" Nothing
      , arm "storage-failure" "put.failure" Nothing
      ]
  , spec "SteveGet" "get.entry"
      [ arm "found" "get.check" (Just "get.bytes")
      , arm "not-found" "get.not-found" Nothing
      , arm "storage-failure" "get.failure" Nothing
      ]
  , spec "SteveGet" "get.check"
      [ arm "accepted" "get.ok" Nothing
      , arm "rejected" "get.integrity-failure" Nothing
      ]
  ]

spec
  :: Text.Text
  -> Text.Text
  -> [(Text.Text, RuntimeChoicePayloadArm)]
  -> RuntimeChoicePayloadSpec
spec functionName blockName arms = RuntimeChoicePayloadSpec
  { runtimeChoicePayloadSite = RuntimeChoiceSite functionName blockName
  , runtimeChoicePayloadArms = Map.fromList arms
  }

arm
  :: Text.Text
  -> Text.Text
  -> Maybe Text.Text
  -> (Text.Text, RuntimeChoicePayloadArm)
arm label target payload =
  ( label
  , RuntimeChoicePayloadArm
      { runtimeChoicePayloadTarget = target
      , runtimeChoicePayloadValue = payload
      }
  )

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
