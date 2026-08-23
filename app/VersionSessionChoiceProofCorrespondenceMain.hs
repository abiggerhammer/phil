{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Systems
import Phil.Systems.VersionSessionChoiceProofCheck
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "exact version session choice proof witness verifies" candidateVerifies
    , test "duplicate unsupported semantic select is rejected" duplicateUnsupportedRejects
    , test "duplicate version semantic select is rejected" duplicateVersionRejects
    , test "server selected-version binder rejects alternate predecessor" serverBinderAlternatePredecessorRejects
    , test "client received-version binder rejects alternate predecessor" clientBinderAlternatePredecessorRejects
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies = withBundle $ \bundle ->
  verifyVersionSessionChoiceProofWitness
    (versionSessionChoiceArtifact bundle)
    (versionSessionChoiceWitness bundle)
    == Right ()

duplicateUnsupportedRejects :: Bool
duplicateUnsupportedRejects = withBundle $ \bundle ->
  let witness = versionSessionChoiceWitness bundle
      mutated = mapServerBlock bundle (versionChoiceServerUnsupportedBlock witness) $ \blockValue ->
        blockValue
          { systemsBlockOps = duplicateFirstSessionSelect (systemsBlockOps blockValue) }
  in case verifyVersionSessionChoiceProofWitness mutated witness of
      Left (VersionSessionChoiceServerSelectMultiplicity _ _ 2) -> True
      _ -> False

duplicateVersionRejects :: Bool
duplicateVersionRejects = withBundle $ \bundle ->
  let witness = versionSessionChoiceWitness bundle
      mutated = mapServerBlock bundle (versionChoiceServerVersionBlock witness) $ \blockValue ->
        blockValue
          { systemsBlockOps = duplicateFirstSessionSelect (systemsBlockOps blockValue) }
  in case verifyVersionSessionChoiceProofWitness mutated witness of
      Left (VersionSessionChoiceServerSelectMultiplicity _ _ 2) -> True
      _ -> False

serverBinderAlternatePredecessorRejects :: Bool
serverBinderAlternatePredecessorRejects = withBundle $ \bundle ->
  let witness = versionSessionChoiceWitness bundle
      mutated = mapServerBlock bundle (versionChoiceServerUnsupportedBlock witness) $ \blockValue ->
        blockValue { systemsBlockTerminator = TermJump (versionChoiceServerVersionBlock witness) }
  in case verifyVersionSessionChoiceProofWitness mutated witness of
      Left (VersionSessionChoiceServerBinderPredecessors _) -> True
      _ -> False

clientBinderAlternatePredecessorRejects :: Bool
clientBinderAlternatePredecessorRejects = withBundle $ \bundle ->
  let witness = versionSessionChoiceWitness bundle
      mutated = mapClientBlock bundle (versionChoiceClientUnsupportedTarget witness) $ \blockValue ->
        blockValue { systemsBlockTerminator = TermJump (versionChoiceClientVersionTarget witness) }
  in case verifyVersionSessionChoiceProofWitness mutated witness of
      Left (VersionSessionChoiceClientBinderPredecessors _) -> True
      _ -> False

duplicateFirstSessionSelect :: [SystemsOp] -> [SystemsOp]
duplicateFirstSessionSelect operations =
  case break isSessionSelect operations of
    (before, operation : after) -> before <> [operation, operation] <> after
    _ -> operations
  where
    isSessionSelect OpSessionSelect {} = True
    isSessionSelect _ = False

withBundle :: (VersionSessionChoiceBundle -> Bool) -> Bool
withBundle action = case phase0VersionSessionChoiceBundle of
  Left _ -> False
  Right bundle -> action bundle

mapServerBlock
  :: VersionSessionChoiceBundle
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapServerBlock bundle blockId transform =
  mapFunctionBlock bundle "UploadServer" blockId transform

mapClientBlock
  :: VersionSessionChoiceBundle
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapClientBlock bundle blockId transform =
  mapFunctionBlock bundle "UploadClient" blockId transform

mapFunctionBlock
  :: VersionSessionChoiceBundle
  -> String
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapFunctionBlock bundle functionName blockId transform =
  let artifact = versionSessionChoiceArtifact bundle
      program = systemsArtifactProgram artifact
      functions = systemsProgramFunctions program
      functions' = Map.adjust
        (\function -> function
          { systemsFunctionBlocks = Map.adjust transform blockId (systemsFunctionBlocks function) })
        (Text.pack functionName)
        functions
      program' = program { systemsProgramFunctions = functions' }
  in artifact { systemsArtifactProgram = program' }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
