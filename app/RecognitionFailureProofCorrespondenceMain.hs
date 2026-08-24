{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types (Digest)
import Phil.Systems.ClientOutbound
import Phil.Systems.IR
import Phil.Systems.RecognitionFailure
import Phil.Systems.StorageFailure
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "current StorageFailure successor verifies" currentSuccessorVerifies
    , test "current successor preserves RecognitionFailure witnesses" currentSuccessorPreservesRecognition
    , test "current successor preserves certified ClientOutbound witness" currentSuccessorPreservesClientOutbound
    , test "Hello and Begin recognition failure flows are exact" exactFailureFlows
    , test "recognition success paths are unchanged by StorageFailure successor" successPathsUnchanged
    , test "recognition failure decision is rebound to current successor" decisionRebound
    , test "cross-grammar reason identity drift is rejected" reasonIdentityDriftRejects
    , test "failure cleanup/effect order drift is rejected" cleanupOrderDriftRejects
    ]
  if and results then pure () else exitFailure

currentSuccessorVerifies :: Bool
currentSuccessorVerifies = withCurrent $ \bundle ->
  verifyStorageFailureBundle bundle == Right ()

currentSuccessorPreservesRecognition :: Bool
currentSuccessorPreservesRecognition = withCurrent $ \bundle ->
  verifyRecognitionFailureWitnesses
    (storageFailureArtifact bundle)
    phase0RecognitionFailureWitnesses == Right ()

currentSuccessorPreservesClientOutbound :: Bool
currentSuccessorPreservesClientOutbound = withCurrent $ \bundle ->
  verifyClientOutboundWitness
    (storageFailureArtifact bundle)
    phase0ClientOutboundWitness == Right ()

exactFailureFlows :: Bool
exactFailureFlows = withCurrent $ \bundle ->
  let artifact = storageFailureArtifact bundle
  in distinctReasons phase0RecognitionFailureWitnesses
      && all (exactWitness artifact) phase0RecognitionFailureWitnesses

exactWitness :: SystemsArtifact -> RecognitionFailureWitness -> Bool
exactWitness artifact witness =
  let program = systemsArtifactProgram artifact
      functionName = recognitionFailureFunction witness
      decision = DecisionId "lower.recognition.failure_detail"
      expectedReasonRole = RuntimeOpaque
        ("RecognitionReason[" <> recognitionFailureGrammar witness <> "]")
  in doBool $ do
      function <- Map.lookup functionName (systemsProgramFunctions program)
      reasonValue <- Map.lookup
        (recognitionFailureReason witness)
        (systemsFunctionValues function)
      recognitionBlock <- Map.lookup
        (recognitionFailureRecognitionBlock witness)
        (systemsFunctionBlocks function)
      failureBlock <- Map.lookup
        (recognitionFailureFailureBlock witness)
        (systemsFunctionBlocks function)
      let gateExact = case systemsBlockTerminator recognitionBlock of
            TermRecognize pending _raw site _success failure ->
              pending == recognitionFailurePending witness
                && runtimeSiteKind site == RecognitionBoundary (recognitionFailureGrammar witness)
                && failure == recognitionFailureFailureBlock witness
            _ -> False
          flowExact = case systemsBlockOps failureBlock of
            [ OpRuntimeCall materializeName [materializePending] [reason] Nothing materializeDecision
              , OpRuntimeCall effectName [effectPending, effectReason] [] Nothing effectDecision
              , OpDestroyPending destroyPending destroyFrame _cleanupDecision
              ] ->
                materializeName == recognitionFailureMaterializeCall witness
                  && materializePending == recognitionFailurePending witness
                  && reason == recognitionFailureReason witness
                  && materializeDecision == decision
                  && effectName == recognitionFailureEffectCall witness
                  && effectPending == recognitionFailurePending witness
                  && effectReason == recognitionFailureReason witness
                  && effectDecision == decision
                  && destroyPending == recognitionFailurePending witness
                  && destroyFrame == recognitionFailureFrameOwner witness
            _ -> False
          reasonUses = semanticUses
            (recognitionFailureReason witness)
            function
      pure
        ( systemsValueRole reasonValue == expectedReasonRole
        && gateExact
        && flowExact
        && systemsBlockTerminator failureBlock ==
            TermFatal (recognitionFailureFatalClass witness)
        && reasonUses ==
            [ ( recognitionFailureFailureBlock witness
              , "runtime-call:" <> recognitionFailureEffectCall witness
              )
            ]
        )

successPathsUnchanged :: Bool
successPathsUnchanged = withCurrent $ \bundle ->
  let currentProgram = systemsArtifactProgram (storageFailureArtifact bundle)
      predecessor = storageFailurePredecessor bundle
      predecessorProgram = systemsArtifactProgram (recognitionFailureArtifact predecessor)
  in all (sameGate currentProgram predecessorProgram) phase0RecognitionFailureWitnesses
  where
    sameGate currentProgram predecessorProgram witness = doBool $ do
      currentFunction <- Map.lookup
        (recognitionFailureFunction witness)
        (systemsProgramFunctions currentProgram)
      predecessorFunction <- Map.lookup
        (recognitionFailureFunction witness)
        (systemsProgramFunctions predecessorProgram)
      currentBlock <- Map.lookup
        (recognitionFailureRecognitionBlock witness)
        (systemsFunctionBlocks currentFunction)
      predecessorBlock <- Map.lookup
        (recognitionFailureRecognitionBlock witness)
        (systemsFunctionBlocks predecessorFunction)
      pure (systemsBlockTerminator currentBlock == systemsBlockTerminator predecessorBlock)

decisionRebound :: Bool
decisionRebound = withCurrent $ \bundle ->
  let artifact = storageFailureArtifact bundle
      targetDigest = systemsProgramDigest (systemsArtifactProgram artifact)
      decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
  in decisionTargets targetDigest decisions (DecisionId "lower.recognition.failure_detail")

decisionTargets
  :: Digest
  -> Map.Map DecisionId LoweringDecision
  -> DecisionId
  -> Bool
decisionTargets targetDigest decisions decisionId =
  case Map.lookup decisionId decisions of
    Just decision -> loweringTargetArtifactDigest decision == targetDigest
    Nothing -> False

reasonIdentityDriftRejects :: Bool
reasonIdentityDriftRejects = withCurrent $ \bundle ->
  case phase0RecognitionFailureWitnesses of
    firstWitness : secondWitness : _ ->
      let artifact = storageFailureArtifact bundle
          program = systemsArtifactProgram artifact
          functions' = Map.adjust
            (mutateFunction firstWitness secondWitness)
            (recognitionFailureFunction firstWitness)
            (systemsProgramFunctions program)
          mutatedProgram = program { systemsProgramFunctions = functions' }
          mutated = artifact { systemsArtifactProgram = mutatedProgram }
      in isLeft (verifyRecognitionFailureWitnesses mutated phase0RecognitionFailureWitnesses)
    _ -> False
  where
    mutateFunction firstWitness secondWitness function = function
      { systemsFunctionBlocks = Map.adjust
          (\blockValue -> blockValue
            { systemsBlockOps = map (mutateEffect firstWitness secondWitness)
                (systemsBlockOps blockValue)
            })
          (recognitionFailureFailureBlock firstWitness)
          (systemsFunctionBlocks function)
      }
    mutateEffect firstWitness secondWitness operation = case operation of
      OpRuntimeCall name [pending, _reason] [] Nothing decision
        | name == recognitionFailureEffectCall firstWitness ->
            OpRuntimeCall name
              [pending, recognitionFailureReason secondWitness]
              [] Nothing decision
      other -> other

cleanupOrderDriftRejects :: Bool
cleanupOrderDriftRejects = withCurrent $ \bundle ->
  case phase0RecognitionFailureWitnesses of
    firstWitness : _ ->
      let artifact = storageFailureArtifact bundle
          program = systemsArtifactProgram artifact
          functions' = Map.adjust
            (\function -> function
              { systemsFunctionBlocks = Map.adjust reorder
                  (recognitionFailureFailureBlock firstWitness)
                  (systemsFunctionBlocks function)
              })
            (recognitionFailureFunction firstWitness)
            (systemsProgramFunctions program)
          mutatedProgram = program { systemsProgramFunctions = functions' }
          mutated = artifact { systemsArtifactProgram = mutatedProgram }
      in isLeft (verifyRecognitionFailureWitnesses mutated phase0RecognitionFailureWitnesses)
    _ -> False
  where
    reorder blockValue = case systemsBlockOps blockValue of
      [materialize, effect, cleanup] ->
        blockValue { systemsBlockOps = [materialize, cleanup, effect] }
      _ -> blockValue

distinctReasons :: [RecognitionFailureWitness] -> Bool
distinctReasons witnesses =
  let reasons = map recognitionFailureReason witnesses
  in length reasons == length (Map.fromList [(reason, ()) | reason <- reasons])

semanticUses :: ValueId -> SystemsFunction -> [(BlockId, Text)]
semanticUses valueId function =
  [ (systemsBlockId blockValue, "runtime-call:" <> name)
  | blockValue <- Map.elems (systemsFunctionBlocks function)
  , OpRuntimeCall name inputs _outputs _site _decision <- systemsBlockOps blockValue
  , valueId `elem` inputs
  ]

withCurrent :: (StorageFailureBundle -> Bool) -> Bool
withCurrent action = case phase0StorageFailureBundle of
  Left _ -> False
  Right bundle -> action bundle

isLeft :: Either a b -> Bool
isLeft value = case value of
  Left _ -> True
  Right _ -> False

doBool :: Maybe Bool -> Bool
doBool = maybe False id

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
