{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "session-choice candidate verifies" candidatePasses
    , test "final response uses semantic session offer" exactOfferPresent
    , test "legacy result Bool is removed" legacyDiscriminatorRemoved
    , test "accepted UploadId is recorded on accepted arm" acceptedPayloadRecorded
    , test "wrong accepted payload target is rejected" wrongAcceptedTargetRejects
    , test "legacy generic final-response receive is rejected" legacyReceiveRejects
    , test "accepted payload escaping to rejected arm is rejected" payloadEscapeRejects
    ]
  if and results then pure () else exitFailure

candidatePasses :: Bool
candidatePasses = case phase0SessionChoiceBundle of
  Right _ -> True
  Left _ -> False

exactOfferPresent :: Bool
exactOfferPresent = withBundle $ \bundle ->
  let witness = sessionChoiceWitness bundle
  in case lookupBlockFrom bundle (sessionChoiceOfferBlock witness) of
      Just blockValue -> case systemsBlockTerminator blockValue of
        TermSessionOffer transport arms ->
          transport == sessionChoiceTransport witness
            && Map.lookup (sessionChoiceAcceptedLabel witness) arms
              == Just (SystemsChoiceArm
                  (Just (sessionChoiceAcceptedPayload witness))
                  (sessionChoiceAcceptedTarget witness))
            && Map.lookup (sessionChoiceRejectedLabel witness) arms
              == Just (SystemsChoiceArm
                  (Just (sessionChoiceRejectedPayload witness))
                  (sessionChoiceRejectedTarget witness))
        _ -> False
      Nothing -> False

legacyDiscriminatorRemoved :: Bool
legacyDiscriminatorRemoved = withBundle $ \bundle ->
  let witness = sessionChoiceWitness bundle
  in case lookupFunctionFrom bundle of
      Just function -> not (Map.member
        (sessionChoiceLegacyDiscriminator witness)
        (systemsFunctionValues function))
      Nothing -> False

acceptedPayloadRecorded :: Bool
acceptedPayloadRecorded = withBundle $ \bundle ->
  let witness = sessionChoiceWitness bundle
  in case lookupBlockFrom bundle (sessionChoiceAcceptedTarget witness) of
      Just SystemsBlock
        { systemsBlockOps =
            [OpRuntimeCall name inputs [] Nothing decisionId]
        , systemsBlockTerminator = TermEnd "success"
        } ->
          name == sessionChoiceRecordOperation witness
            && inputs == [sessionChoiceAcceptedPayload witness]
            && decisionId == sessionChoiceRecordDecision witness
      _ -> False

wrongAcceptedTargetRejects :: Bool
wrongAcceptedTargetRejects = withBundle $ \bundle ->
  let witness = sessionChoiceWitness bundle
      artifact = mapOffer bundle $ \blockValue ->
        blockValue
          { systemsBlockTerminator = case systemsBlockTerminator blockValue of
              TermSessionOffer transport arms -> TermSessionOffer transport
                (Map.adjust
                  (\arm -> arm { choiceArmTarget = sessionChoiceRejectedTarget witness })
                  (sessionChoiceAcceptedLabel witness)
                  arms)
              other -> other
          }
  in case verifySessionChoiceWitness artifact witness of
      Left SessionChoiceOfferMismatch {} -> True
      _ -> False

legacyReceiveRejects :: Bool
legacyReceiveRejects = withBundle $ \bundle ->
  let witness = sessionChoiceWitness bundle
      legacy = OpRuntimeCall
        (sessionChoiceLegacyReceiveCall witness)
        [sessionChoiceTransport witness]
        [sessionChoiceLegacyDiscriminator witness]
        Nothing
        (sessionChoiceRecordDecision witness)
      artifact = mapOffer bundle $ \blockValue ->
        blockValue { systemsBlockOps = systemsBlockOps blockValue <> [legacy] }
  in case verifySessionChoiceWitness artifact witness of
      Left SessionChoiceLegacyReceivePresent {} -> True
      _ -> False

payloadEscapeRejects :: Bool
payloadEscapeRejects = withBundle $ \bundle ->
  let witness = sessionChoiceWitness bundle
      artifact = mapBlock bundle (sessionChoiceRejectedTarget witness) $ \blockValue ->
        blockValue
          { systemsBlockOps =
              [ OpRuntimeCall
                  "inspect"
                  [sessionChoiceAcceptedPayload witness]
                  []
                  Nothing
                  (sessionChoiceRecordDecision witness)
              ]
          }
  in case verifySessionChoiceWitness artifact witness of
      Left SessionChoicePayloadUseEscapes {} -> True
      _ -> False

withBundle :: (SessionChoiceBundle -> Bool) -> Bool
withBundle action = case phase0SessionChoiceBundle of
  Left _ -> False
  Right bundle -> action bundle

lookupFunctionFrom :: SessionChoiceBundle -> Maybe SystemsFunction
lookupFunctionFrom bundle =
  let witness = sessionChoiceWitness bundle
  in Map.lookup
      (sessionChoiceFunction witness)
      (systemsProgramFunctions (systemsArtifactProgram (sessionChoiceArtifact bundle)))

lookupBlockFrom :: SessionChoiceBundle -> BlockId -> Maybe SystemsBlock
lookupBlockFrom bundle blockId = do
  function <- lookupFunctionFrom bundle
  Map.lookup blockId (systemsFunctionBlocks function)

mapOffer
  :: SessionChoiceBundle
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapOffer bundle =
  mapBlock bundle (sessionChoiceOfferBlock (sessionChoiceWitness bundle))

mapBlock
  :: SessionChoiceBundle
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapBlock bundle blockId transform =
  let artifact = sessionChoiceArtifact bundle
      witness = sessionChoiceWitness bundle
      program = systemsArtifactProgram artifact
      functions = systemsProgramFunctions program
      functions' = Map.adjust
        (\function -> function
          { systemsFunctionBlocks = Map.adjust
              transform
              blockId
              (systemsFunctionBlocks function)
          })
        (sessionChoiceFunction witness)
        functions
  in artifact
      { systemsArtifactProgram = program { systemsProgramFunctions = functions' } }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
