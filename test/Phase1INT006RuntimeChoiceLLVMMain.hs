{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types (digestText)
import Phil.Compiler.RuntimeChoiceABI
import Phil.Compiler.RuntimeChoiceLLVM
import Phil.Compiler.RuntimeChoicePayload
import Phil.Compiler.RuntimeChoiceSystems
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveCoreProgram
  , stevePhase1StageBundle
  )
import Phil.Systems.IR (systemsArtifactDigest)
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle
  , phase1StageSystemsArtifact
  )
import System.Environment (getArgs)
import System.Exit (exitFailure)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["emit"] -> case steveLowered of
      Left err -> failWith err
      Right (_, _, artifact) -> TextIO.putStr (runtimeChoiceLLVMText artifact)
    [] -> do
      let checks =
            [ ("sealed Steve ABI lowers to provider LLVM", positive)
            , ("LLVM artifact binds exact Systems and ABI identities", identityBound)
            , ("public function inputs are exact semantic roots", functionInputs)
            , ("all four qualified provider calls are explicit", providerCalls)
            , ("payload out-slots load only on selected successors", selectedPayloadLoads)
            , ("canonical arm tags survive as switch cases", stableTags)
            , ("invalid provider tags trap closed", invalidTagsTrap)
            , ("ambient runtime-choice state is absent", noAmbientChoiceState)
            , ("unbound Systems stage is rejected", unboundStageRejects)
            ]
      results <- mapM report checks
      if and results then pure () else exitFailure
    _ -> failWith "usage: Phase1INT006RuntimeChoiceLLVMMain [emit]"

failWith :: String -> IO a
failWith message = do
  putStrLn ("FAIL: INT-006 " <> message)
  exitFailure

report :: (String, Bool) -> IO Bool
report (label, ok) = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> "INT-006 " <> label)
  pure ok

positive :: Bool
positive = case steveLowered of
  Right {} -> True
  Left _ -> False

identityBound :: Bool
identityBound = case steveLowered of
  Left _ -> False
  Right (stage, abiPlan, artifact) ->
    runtimeChoiceLLVMSourceSystemsDigest artifact
      == systemsArtifactDigest (phase1StageSystemsArtifact stage)
      && runtimeChoiceLLVMABIDigest artifact == runtimeChoiceABIPlanDigest abiPlan
      && runtimeChoiceLLVMTextDigest artifact == digestText (runtimeChoiceLLVMText artifact)
      && runtimeChoiceLLVMTarget artifact == phase1RuntimeChoiceLLVMTarget

functionInputs :: Bool
functionInputs = case steveLLVMText of
  Nothing -> False
  Just rendered ->
    "define i32 @StevePut(ptr %put_candidate) {" `Text.isInfixOf` rendered
      && "define i32 @SteveGet(ptr %get_id) {" `Text.isInfixOf` rendered

providerCalls :: Bool
providerCalls = case steveLLVMText of
  Nothing -> False
  Just rendered -> all (`Text.isInfixOf` rendered)
    [ "@phil_runtime_choice_StevePut_put_entry_DigestProvider_compute"
    , "@phil_runtime_choice_StevePut_put_install_BlobProvider_install_if_absent"
    , "@phil_runtime_choice_SteveGet_get_entry_BlobProvider_read"
    , "@phil_runtime_choice_SteveGet_get_check_DigestProvider_check"
    ]

selectedPayloadLoads :: Bool
selectedPayloadLoads = case steveLLVMText of
  Nothing -> False
  Just rendered ->
    let putLoad = "%put_id = load ptr, ptr %phil_runtime_choice_payload_slot_StevePut_put_entry_put_id"
        getLoad = "%get_bytes = load ptr, ptr %phil_runtime_choice_payload_slot_SteveGet_get_entry_get_bytes"
        putInstall = blockText "put_install:" rendered
        getCheck = blockText "get_check:" rendered
        getNotFound = blockText "get_not_found:" rendered
        getFailure = blockText "get_failure:" rendered
    in putLoad `Text.isInfixOf` putInstall
        && getLoad `Text.isInfixOf` getCheck
        && not (getLoad `Text.isInfixOf` getNotFound)
        && not (getLoad `Text.isInfixOf` getFailure)
        && Text.count putLoad rendered == 1
        && Text.count getLoad rendered == 1

stableTags :: Bool
stableTags = case steveLLVMText of
  Nothing -> False
  Just rendered ->
    let install = blockText "put_install:" rendered
        readEntry = blockText "get_entry:" rendered
        checkBlock = blockText "get_check:" rendered
    in all (`Text.isInfixOf` install)
        [ "i32 0, label %put_ok"
        , "i32 1, label %put_ok"
        , "i32 2, label %put_failure"
        ]
        && all (`Text.isInfixOf` readEntry)
          [ "i32 0, label %get_check"
          , "i32 1, label %get_not_found"
          , "i32 2, label %get_failure"
          ]
        && all (`Text.isInfixOf` checkBlock)
          [ "i32 0, label %get_ok"
          , "i32 1, label %get_integrity_failure"
          ]

invalidTagsTrap :: Bool
invalidTagsTrap = case steveLLVMText of
  Nothing -> False
  Just rendered ->
    Text.count "call void @llvm.trap()" rendered == 4
      && Text.count "unreachable" rendered == 4

noAmbientChoiceState :: Bool
noAmbientChoiceState = case steveLLVMText of
  Nothing -> False
  Just rendered ->
    not ("phil_current_" `Text.isInfixOf` rendered)
      && not ("phil_branch_condition" `Text.isInfixOf` rendered)

unboundStageRejects :: Bool
unboundStageRejects = case (stevePlan, stevePhase1StageBundle) of
  (Right payloadPlan, Right unbound) ->
    case bindRuntimeChoicePayloadPlan steveCoreProgram payloadPlan unbound of
      Left _ -> False
      Right bound -> case certifyRuntimeChoiceABIPlan steveCoreProgram payloadPlan bound of
        Left _ -> False
        Right abiPlan -> case lowerRuntimeChoiceABIToLLVM
            phase1RuntimeChoiceLLVMTarget abiPlan unbound of
          Left RuntimeChoiceLLVMArmPayloadMismatch {} -> True
          Left RuntimeChoiceLLVMInputCarrierMismatch {} -> True
          Left RuntimeChoiceLLVMPayloadCarrierMismatch {} -> True
          _ -> False
  _ -> False

blockText :: Text -> Text -> Text
blockText label rendered =
  case Text.breakOn label rendered of
    (_, rest) | Text.null rest -> ""
    (_, rest) ->
      let after = Text.drop (Text.length label) rest
          body = Text.takeWhileInclusive (/= '\n') after
          following = Text.unlines . takeWhile (not . isLabel) . Text.lines $ after
      in label <> body <> following
  where
    isLabel line =
      not (Text.null line)
        && Text.last line == ':'
        && not (Text.isPrefixOf " " line)

steveLLVMText :: Maybe Text
steveLLVMText = case steveLowered of
  Left _ -> Nothing
  Right (_, _, artifact) -> Just (runtimeChoiceLLVMText artifact)

steveLowered
  :: Either String (Phase1StageBundle, RuntimeChoiceABIPlan, RuntimeChoiceLLVMArtifact)
steveLowered = do
  base <- stevePhase1StageBundle
  payloadPlan <- mapLeft show
    (certifyRuntimeChoicePayloadPlan steveCoreProgram stevePayloadSpecs)
  bound <- mapLeft show
    (bindRuntimeChoicePayloadPlan steveCoreProgram payloadPlan base)
  abiPlan <- mapLeft show
    (certifyRuntimeChoiceABIPlan steveCoreProgram payloadPlan bound)
  artifact <- mapLeft show
    (lowerRuntimeChoiceABIToLLVM phase1RuntimeChoiceLLVMTarget abiPlan bound)
  pure (bound, abiPlan, artifact)

stevePlan :: Either RuntimeChoicePayloadError RuntimeChoicePayloadPlan
stevePlan = certifyRuntimeChoicePayloadPlan steveCoreProgram stevePayloadSpecs

stevePayloadSpecs :: [RuntimeChoicePayloadSpec]
stevePayloadSpecs =
  [ spec "StevePut" "put.entry"
      [armSpec "computed" "put.install" (Just "put.id")]
  , spec "StevePut" "put.install"
      [ armSpec "installed" "put.ok" Nothing
      , armSpec "already-exists" "put.ok" Nothing
      , armSpec "storage-failure" "put.failure" Nothing
      ]
  , spec "SteveGet" "get.entry"
      [ armSpec "found" "get.check" (Just "get.bytes")
      , armSpec "not-found" "get.not-found" Nothing
      , armSpec "storage-failure" "get.failure" Nothing
      ]
  , spec "SteveGet" "get.check"
      [ armSpec "accepted" "get.ok" Nothing
      , armSpec "rejected" "get.integrity-failure" Nothing
      ]
  ]

spec
  :: Text
  -> Text
  -> [(Text, RuntimeChoicePayloadArm)]
  -> RuntimeChoicePayloadSpec
spec functionName blockName arms = RuntimeChoicePayloadSpec
  { runtimeChoicePayloadSite = RuntimeChoiceSite functionName blockName
  , runtimeChoicePayloadArms = Map.fromList arms
  }

armSpec
  :: Text
  -> Text
  -> Maybe Text
  -> (Text, RuntimeChoicePayloadArm)
armSpec label target payload =
  ( label
  , RuntimeChoicePayloadArm
      { runtimeChoicePayloadTarget = target
      , runtimeChoicePayloadValue = payload
      }
  )

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
