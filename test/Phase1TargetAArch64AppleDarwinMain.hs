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
import Phil.Compiler.RuntimeChoiceTargets
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveCoreProgram
  , stevePhase1StageBundle
  )
import Phil.LLVM.IR (LLVMTargetProfile (..))
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
    ["emit"] -> case steveLoweredDarwin of
      Left err -> failWith err
      Right (_, _, artifact) -> TextIO.putStr (runtimeChoiceLLVMText artifact)
    [] -> do
      let checks =
            [ ("Darwin target profile is exact", targetProfileExact)
            , ("Darwin provider ABI identity is target-specific", targetABIExact)
            , ("canonical Steve lowers under Darwin target", positive)
            , ("lowered artifact binds Darwin target and source identities", identityBound)
            , ("Darwin LLVM header is exact", headerExact)
            , ("qualified provider calls survive target change", providerCalls)
            ]
      results <- mapM report checks
      if and results then pure () else exitFailure
    _ -> failWith "usage: Phase1TargetAArch64AppleDarwinMain [emit]"

failWith :: String -> IO a
failWith message = do
  putStrLn ("FAIL: TARGET-AARCH64-APPLE-DARWIN " <> message)
  exitFailure

report :: (String, Bool) -> IO Bool
report (label, ok) = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> "TARGET-AARCH64-APPLE-DARWIN " <> label)
  pure ok

targetProfileExact :: Bool
targetProfileExact =
  llvmTargetLanguageVersion target == "LLVM IR 18 opaque-pointer subset"
    && llvmTargetToolVersion target == "llvm-as 18.x expected"
    && llvmTargetTripleName target == "aarch64-apple-darwin"
    && llvmTargetDataLayout target == "e-m:o-i64:64-i128:128-n32:64-S128"
    && llvmTargetRuntimeABIProfile target == "phil-runtime/phase1/runtime-choice-provider-v1"

targetABIExact :: Bool
targetABIExact =
  "target=aarch64-apple-darwin" `Text.isInfixOf` runtimeChoiceAArch64AppleDarwinABIDescriptor
    && not ("target=x86_64-unknown-linux-gnu" `Text.isInfixOf` runtimeChoiceAArch64AppleDarwinABIDescriptor)
    && llvmTargetRuntimeABIDigest target == digestText runtimeChoiceAArch64AppleDarwinABIDescriptor
    && llvmTargetRuntimeABIDigest target /= llvmTargetRuntimeABIDigest phase1RuntimeChoiceLLVMTarget

positive :: Bool
positive = case steveLoweredDarwin of
  Right _ -> True
  Left _ -> False

identityBound :: Bool
identityBound = case steveLoweredDarwin of
  Left _ -> False
  Right (stage, abiPlan, artifact) ->
    runtimeChoiceLLVMSourceSystemsDigest artifact
      == systemsArtifactDigest (phase1StageSystemsArtifact stage)
      && runtimeChoiceLLVMABIDigest artifact == runtimeChoiceABIPlanDigest abiPlan
      && runtimeChoiceLLVMTextDigest artifact == digestText (runtimeChoiceLLVMText artifact)
      && runtimeChoiceLLVMTarget artifact == target

headerExact :: Bool
headerExact = case steveLLVMTextDarwin of
  Nothing -> False
  Just rendered ->
    "target datalayout = \"e-m:o-i64:64-i128:128-n32:64-S128\"" `Text.isInfixOf` rendered
      && "target triple = \"aarch64-apple-darwin\"" `Text.isInfixOf` rendered

providerCalls :: Bool
providerCalls = case steveLLVMTextDarwin of
  Nothing -> False
  Just rendered -> all (`Text.isInfixOf` rendered)
    [ "@phil_runtime_choice_StevePut_put_entry_DigestProvider_compute"
    , "@phil_runtime_choice_StevePut_put_install_BlobProvider_install_if_absent"
    , "@phil_runtime_choice_SteveGet_get_entry_BlobProvider_read"
    , "@phil_runtime_choice_SteveGet_get_check_DigestProvider_check"
    ]

steveLLVMTextDarwin :: Maybe Text
steveLLVMTextDarwin = case steveLoweredDarwin of
  Left _ -> Nothing
  Right (_, _, artifact) -> Just (runtimeChoiceLLVMText artifact)

steveLoweredDarwin
  :: Either String (Phase1StageBundle, RuntimeChoiceABIPlan, RuntimeChoiceLLVMArtifact)
steveLoweredDarwin = do
  base <- stevePhase1StageBundle
  payloadPlan <- mapLeft show
    (certifyRuntimeChoicePayloadPlan steveCoreProgram stevePayloadSpecs)
  bound <- mapLeft show
    (bindRuntimeChoicePayloadPlan steveCoreProgram payloadPlan base)
  abiPlan <- mapLeft show
    (certifyRuntimeChoiceABIPlan steveCoreProgram payloadPlan bound)
  artifact <- mapLeft show
    (lowerRuntimeChoiceABIToLLVM target abiPlan bound)
  pure (bound, abiPlan, artifact)

target :: LLVMTargetProfile
target = phase1RuntimeChoiceAArch64AppleDarwinTarget

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
armSpec label targetBlock payload =
  ( label
  , RuntimeChoicePayloadArm
      { runtimeChoicePayloadTarget = targetBlock
      , runtimeChoicePayloadValue = payload
      }
  )

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
