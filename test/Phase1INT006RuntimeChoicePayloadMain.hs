{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.SystemsWitnesses (steveCoreProgram)
import Phil.Compiler.RuntimeChoicePayload
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("Steve runtime-choice payload plan certifies", positive)
        , ("payload plan is deterministic", deterministic)
        , ("payload plan rejects missing arm", missingArmRejects)
        , ("payload plan rejects target drift", targetDriftRejects)
        , ("payload plan rejects unknown retained value", unknownValueRejects)
        , ("payload plan rejects duplicate site", duplicateSiteRejects)
        ]
  results <- mapM report checks
  if and results then pure () else exitFailure

report :: (String, Bool) -> IO Bool
report (label, ok) = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> "INT-006 " <> label)
  pure ok

positive :: Bool
positive = case certifyRuntimeChoicePayloadPlan steveCoreProgram stevePayloadSpecs of
  Left _ -> False
  Right plan ->
    Map.size (runtimeChoicePayloadPlanSpecs plan) == 4
      && retainedValue plan (RuntimeChoiceSite "StevePut" "put.entry") "computed"
          == Just "put.id"
      && retainedValue plan (RuntimeChoiceSite "SteveGet" "get.entry") "found"
          == Just "get.bytes"

deterministic :: Bool
deterministic =
  case
    ( certifyRuntimeChoicePayloadPlan steveCoreProgram stevePayloadSpecs
    , certifyRuntimeChoicePayloadPlan steveCoreProgram (reverse stevePayloadSpecs)
    ) of
      (Right left, Right right) ->
        runtimeChoicePayloadPlanDigest left == runtimeChoicePayloadPlanDigest right
      _ -> False

missingArmRejects :: Bool
missingArmRejects =
  case certifyRuntimeChoicePayloadPlan steveCoreProgram
      (replaceSpec (RuntimeChoiceSite "SteveGet" "get.entry") missingGetEntry) of
    Left RuntimeChoicePayloadArmDomainMismatch {} -> True
    _ -> False
  where
    missingGetEntry = spec "SteveGet" "get.entry"
      [ arm "found" "get.check" (Just "get.bytes")
      , arm "not-found" "get.not-found" Nothing
      ]

targetDriftRejects :: Bool
targetDriftRejects =
  case certifyRuntimeChoicePayloadPlan steveCoreProgram
      (replaceSpec (RuntimeChoiceSite "StevePut" "put.entry") driftedPutEntry) of
    Left RuntimeChoicePayloadTargetMismatch {} -> True
    _ -> False
  where
    driftedPutEntry = spec "StevePut" "put.entry"
      [arm "computed" "put.failure" (Just "put.id")]

unknownValueRejects :: Bool
unknownValueRejects =
  case certifyRuntimeChoicePayloadPlan steveCoreProgram
      (replaceSpec (RuntimeChoiceSite "SteveGet" "get.entry") badGetEntry) of
    Left RuntimeChoicePayloadValueMissing {} -> True
    _ -> False
  where
    badGetEntry = spec "SteveGet" "get.entry"
      [ arm "found" "get.check" (Just "get.nonexistent")
      , arm "not-found" "get.not-found" Nothing
      , arm "storage-failure" "get.failure" Nothing
      ]

duplicateSiteRejects :: Bool
duplicateSiteRejects =
  case certifyRuntimeChoicePayloadPlan steveCoreProgram
      (head stevePayloadSpecs : stevePayloadSpecs) of
    Left RuntimeChoicePayloadDuplicateSite {} -> True
    _ -> False

retainedValue
  :: RuntimeChoicePayloadPlan
  -> RuntimeChoiceSite
  -> String
  -> Maybe String
retainedValue plan site label = do
  payloadSpec <- Map.lookup site (runtimeChoicePayloadPlanSpecs plan)
  payloadArm <- Map.lookup (fromString label) (runtimeChoicePayloadArms payloadSpec)
  fmap toString (runtimeChoicePayloadValue payloadArm)

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

spec :: String -> String -> [(String, RuntimeChoicePayloadArm)] -> RuntimeChoicePayloadSpec
spec functionName blockName arms = RuntimeChoicePayloadSpec
  { runtimeChoicePayloadSite = RuntimeChoiceSite (fromString functionName) (fromString blockName)
  , runtimeChoicePayloadArms = Map.fromList [(fromString label, value) | (label, value) <- arms]
  }

arm :: String -> String -> Maybe String -> (String, RuntimeChoicePayloadArm)
arm label target payload =
  ( label
  , RuntimeChoicePayloadArm
      { runtimeChoicePayloadTarget = fromString target
      , runtimeChoicePayloadValue = fmap fromString payload
      }
  )

replaceSpec :: RuntimeChoiceSite -> RuntimeChoicePayloadSpec -> [RuntimeChoicePayloadSpec]
replaceSpec wanted replacement =
  [ if runtimeChoicePayloadSite current == wanted then replacement else current
  | current <- stevePayloadSpecs
  ]

fromString :: String -> Data.Text.Text
fromString = Data.Text.pack

toString :: Data.Text.Text -> String
toString = Data.Text.unpack
