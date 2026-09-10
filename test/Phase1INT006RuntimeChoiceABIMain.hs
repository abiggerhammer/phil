{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Compiler.RuntimeChoiceABI
import Phil.Compiler.RuntimeChoicePayload
import Phil.Compiler.RuntimeChoiceSystems
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveCoreProgram
  , stevePhase1StageBundle
  )
import Phil.Systems.IR (ValueId (..))
import Phil.Systems.Phase1Stage (Phase1StageBundle)
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("sealed Steve Systems stage certifies a runtime-choice ABI", positive)
        , ("ABI certificate is deterministic", deterministic)
        , ("compute returns ContentId through the computed arm", computedCarrier)
        , ("read returns owned bytes through the found arm", foundCarrier)
        , ("provider inputs retain exact semantic carriers", inputCarriers)
        , ("arm tags are deterministic ascending-label ordinals", stableTags)
        , ("unbound Systems stage is rejected", unboundStageRejects)
        ]
  results <- mapM report checks
  if and results then pure () else exitFailure

report :: (String, Bool) -> IO Bool
report (label, ok) = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> "INT-006 " <> label)
  pure ok

positive :: Bool
positive = case steveABI of
  Left _ -> False
  Right plan -> Map.size (runtimeChoiceABISites plan) == 4

deterministic :: Bool
deterministic =
  case (steveABI, steveABIWith (reverse stevePayloadSpecs)) of
    (Right left, Right right) ->
      runtimeChoiceABIPlanDigest left == runtimeChoiceABIPlanDigest right
    _ -> False

computedCarrier :: Bool
computedCarrier =
  armPayload "StevePut" "put.entry" "computed"
    == Just (ValueId "put.id", ABIRuntimeScalar "ContentId[SHA256]")

foundCarrier :: Bool
foundCarrier =
  armPayload "SteveGet" "get.entry" "found"
    == Just (ValueId "get.bytes", ABIOwnedBuffer "OwnedBytes")

inputCarriers :: Bool
inputCarriers =
  case steveABI of
    Left _ -> False
    Right plan ->
      let sites = runtimeChoiceABISites plan
          install = Map.lookup (RuntimeChoiceSite "StevePut" "put.install") sites
          check = Map.lookup (RuntimeChoiceSite "SteveGet" "get.check") sites
      in fmap runtimeChoiceABIInputs install
          == Just
            [ RuntimeChoiceABIInput
                (ValueId "put.id")
                (ABIRuntimeScalar "ContentId[SHA256]")
            , RuntimeChoiceABIInput
                (ValueId "put.install-view")
                (ABIBorrowedSlice (ValueId "put.candidate"))
            ]
          && fmap runtimeChoiceABIInputs check
            == Just
              [ RuntimeChoiceABIInput
                  (ValueId "get.id")
                  (ABIRuntimeScalar "ContentId[SHA256]")
              , RuntimeChoiceABIInput
                  (ValueId "get.bytes-view")
                  (ABIBorrowedSlice (ValueId "get.bytes"))
              ]

stableTags :: Bool
stableTags =
  armTag "StevePut" "put.install" "already-exists" == Just 0
    && armTag "StevePut" "put.install" "installed" == Just 1
    && armTag "StevePut" "put.install" "storage-failure" == Just 2
    && armTag "SteveGet" "get.entry" "found" == Just 0
    && armTag "SteveGet" "get.entry" "not-found" == Just 1
    && armTag "SteveGet" "get.entry" "storage-failure" == Just 2

unboundStageRejects :: Bool
unboundStageRejects = case (stevePlan, stevePhase1StageBundle) of
  (Right payloadPlan, Right unbound) ->
    case certifyRuntimeChoiceABIPlan steveCoreProgram payloadPlan unbound of
      Left RuntimeChoiceABIArmPayloadMismatch {} -> True
      _ -> False
  _ -> False

armPayload
  :: Text.Text
  -> Text.Text
  -> Text.Text
  -> Maybe (ValueId, RuntimeChoiceABICarrier)
armPayload functionName blockName label = do
  plan <- either (const Nothing) Just steveABI
  site <- Map.lookup (RuntimeChoiceSite functionName blockName) (runtimeChoiceABISites plan)
  arm <- Map.lookup label (runtimeChoiceABIArms site)
  runtimeChoiceABIArmPayload arm

armTag :: Text.Text -> Text.Text -> Text.Text -> Maybe Int
armTag functionName blockName label = do
  plan <- either (const Nothing) Just steveABI
  site <- Map.lookup (RuntimeChoiceSite functionName blockName) (runtimeChoiceABISites plan)
  arm <- Map.lookup label (runtimeChoiceABIArms site)
  pure (runtimeChoiceABIArmTag arm)

steveABI :: Either String RuntimeChoiceABIPlan
steveABI = steveABIWith stevePayloadSpecs

steveABIWith :: [RuntimeChoicePayloadSpec] -> Either String RuntimeChoiceABIPlan
steveABIWith specs = do
  base <- mapLeft show stevePhase1StageBundle
  payloadPlan <- mapLeft show (certifyRuntimeChoicePayloadPlan steveCoreProgram specs)
  bound <- mapLeft show (bindRuntimeChoicePayloadPlan steveCoreProgram payloadPlan base)
  mapLeft show (certifyRuntimeChoiceABIPlan steveCoreProgram payloadPlan bound)

stevePlan :: Either String RuntimeChoicePayloadPlan
stevePlan = mapLeft show (certifyRuntimeChoicePayloadPlan steveCoreProgram stevePayloadSpecs)

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
