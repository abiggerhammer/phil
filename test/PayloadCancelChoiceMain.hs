{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "payload/cancel Systems candidate verifies" candidateVerifies
    , test "server payload/cancel is an exact semantic session offer" exactServerOffer
    , test "client payload/cancel are exact semantic session selects" exactClientSelects
    , test "legacy payload/cancel Bool discriminator is absent" legacyDiscriminatorAbsent
    , test "should_cancel_upload remains a local Bool TermBranch" localDecisionPreserved
    , test "final accepted/rejected session choice remains valid" finalChoicePreserved
    , test "wrong server label mapping is rejected" wrongServerLabelRejects
    , test "legacy client select representation is rejected" legacyClientSelectRejects
    , test "protocol choice cannot replace the local decision branch" localDecisionDriftRejects
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies = case phase0PayloadCancelChoiceBundle of
  Right bundle -> case verifyPayloadCancelChoiceBundle bundle of
    Right () -> True
    Left _ -> False
  Left _ -> False

exactServerOffer :: Bool
exactServerOffer = withBundle $ \bundle ->
  let witness = payloadCancelChoiceWitness bundle
      expected = Map.fromList
        [ ( payloadCancelPayloadLabel witness
          , SystemsChoiceArm Nothing (payloadCancelPayloadTarget witness)
          )
        , ( payloadCancelCancelLabel witness
          , SystemsChoiceArm Nothing (payloadCancelCancelTarget witness)
          )
        ]
  in case lookupBlock bundle
      (payloadCancelServerFunction witness)
      (payloadCancelServerOfferBlock witness) of
      Just blockValue ->
        systemsBlockTerminator blockValue
          == TermSessionOffer (payloadCancelServerTransport witness) expected
      Nothing -> False

exactClientSelects :: Bool
exactClientSelects = withBundle $ \bundle ->
  let witness = payloadCancelChoiceWitness bundle
  in selectAt bundle
      (payloadCancelClientFunction witness)
      (payloadCancelClientPayloadSelectBlock witness)
      (payloadCancelClientTransport witness)
      (payloadCancelPayloadLabel witness)
      (payloadCancelSelectDecision witness)
    && selectAt bundle
      (payloadCancelClientFunction witness)
      (payloadCancelClientCancelSelectBlock witness)
      (payloadCancelClientTransport witness)
      (payloadCancelCancelLabel witness)
      (payloadCancelSelectDecision witness)

legacyDiscriminatorAbsent :: Bool
legacyDiscriminatorAbsent = withBundle $ \bundle ->
  let witness = payloadCancelChoiceWitness bundle
      program = systemsArtifactProgram (payloadCancelChoiceArtifact bundle)
  in case Map.lookup
      (payloadCancelServerFunction witness)
      (systemsProgramFunctions program) of
      Nothing -> False
      Just function ->
        Map.notMember
          (payloadCancelLegacyDiscriminator witness)
          (systemsFunctionValues function)

localDecisionPreserved :: Bool
localDecisionPreserved = withBundle $ \bundle ->
  let witness = payloadCancelChoiceWitness bundle
  in case lookupBlock bundle
      (payloadCancelClientFunction witness)
      (payloadCancelClientDecisionBlock witness) of
      Just blockValue ->
        systemsBlockTerminator blockValue
          == TermBranch
              (payloadCancelClientDecisionValue witness)
              (payloadCancelClientCancelSelectBlock witness)
              (payloadCancelClientPayloadSelectBlock witness)
      Nothing -> False

finalChoicePreserved :: Bool
finalChoicePreserved = withBundle $ \bundle ->
  case verifySessionChoiceWitness
    (payloadCancelChoiceArtifact bundle)
    phase0FinalResponseChoiceWitness of
      Right () -> True
      Left _ -> False

wrongServerLabelRejects :: Bool
wrongServerLabelRejects = withBundle $ \bundle ->
  let witness = payloadCancelChoiceWitness bundle
      mutated = mapBlock
        bundle
        (payloadCancelServerFunction witness)
        (payloadCancelServerOfferBlock witness) $ \blockValue ->
          blockValue
            { systemsBlockTerminator = case systemsBlockTerminator blockValue of
                TermSessionOffer transport arms ->
                  TermSessionOffer transport $
                    Map.insert "not-payload"
                      (SystemsChoiceArm Nothing (payloadCancelPayloadTarget witness)) $
                    Map.delete (payloadCancelPayloadLabel witness) arms
                other -> other
            }
  in case verifyPayloadCancelChoiceWitness mutated witness of
      Left PayloadCancelServerOfferMismatch {} -> True
      _ -> False

legacyClientSelectRejects :: Bool
legacyClientSelectRejects = withBundle $ \bundle ->
  let witness = payloadCancelChoiceWitness bundle
      blockId = payloadCancelClientPayloadSelectBlock witness
      mutated = mapBlock bundle (payloadCancelClientFunction witness) blockId $ \blockValue ->
        blockValue
          { systemsBlockOps = case systemsBlockOps blockValue of
              OpSessionSelect {} : rest ->
                OpRuntimeCall
                  { runtimeCallName = "select payload"
                  , runtimeCallInputs = [payloadCancelClientTransport witness]
                  , runtimeCallOutputs = []
                  , runtimeCallSite = Nothing
                  , runtimeCallDecision = DecisionId "lower.runtime.semantic_call"
                  } : rest
              operations -> operations
          }
  in case verifyPayloadCancelChoiceWitness mutated witness of
      Left PayloadCancelClientSelectMismatch {} -> True
      _ -> False

localDecisionDriftRejects :: Bool
localDecisionDriftRejects = withBundle $ \bundle ->
  let witness = payloadCancelChoiceWitness bundle
      blockId = payloadCancelClientDecisionBlock witness
      mutated = mapBlock bundle (payloadCancelClientFunction witness) blockId $ \blockValue ->
        blockValue
          { systemsBlockTerminator = TermSessionOffer
              (payloadCancelClientTransport witness)
              (Map.fromList
                [ (payloadCancelPayloadLabel witness,
                    SystemsChoiceArm Nothing (payloadCancelClientPayloadSelectBlock witness))
                , (payloadCancelCancelLabel witness,
                    SystemsChoiceArm Nothing (payloadCancelClientCancelSelectBlock witness))
                ])
          }
  in case verifyPayloadCancelChoiceWitness mutated witness of
      Left PayloadCancelLocalDecisionMismatch {} -> True
      _ -> False

selectAt
  :: PayloadCancelChoiceBundle
  -> Text
  -> BlockId
  -> ValueId
  -> Text
  -> DecisionId
  -> Bool
selectAt bundle functionName blockId transport label decisionId =
  case lookupBlock bundle functionName blockId of
    Just blockValue -> case systemsBlockOps blockValue of
      OpSessionSelect actualTransport actualLabel Nothing actualDecision : _ ->
        actualTransport == transport
          && actualLabel == label
          && actualDecision == decisionId
      _ -> False
    Nothing -> False

withBundle :: (PayloadCancelChoiceBundle -> Bool) -> Bool
withBundle action = case phase0PayloadCancelChoiceBundle of
  Left _ -> False
  Right bundle -> action bundle

lookupBlock
  :: PayloadCancelChoiceBundle
  -> Text
  -> BlockId
  -> Maybe SystemsBlock
lookupBlock bundle functionName blockId = do
  function <- Map.lookup
    functionName
    (systemsProgramFunctions (systemsArtifactProgram (payloadCancelChoiceArtifact bundle)))
  Map.lookup blockId (systemsFunctionBlocks function)

mapBlock
  :: PayloadCancelChoiceBundle
  -> Text
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapBlock bundle functionName blockId transform =
  let artifact = payloadCancelChoiceArtifact bundle
      program = systemsArtifactProgram artifact
      functions = systemsProgramFunctions program
      functions' = Map.adjust
        (\function -> function
          { systemsFunctionBlocks = Map.adjust transform blockId (systemsFunctionBlocks function) })
        functionName
        functions
      program' = program { systemsProgramFunctions = functions' }
  in artifact { systemsArtifactProgram = program' }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
