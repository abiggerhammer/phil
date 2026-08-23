{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "recognition failure candidate verifies" candidateVerifies
    , test "Hello and Begin reasons are explicit and distinct" explicitDistinctReasons
    , test "recognition reasons flow through exact pending-specific fatal effects" exactFailureFlows
    , test "extra recognition reason observation is rejected" extraReasonUseRejects
    , test "wrong recognition pending provenance is rejected" wrongPendingRejects
    , test "client outbound semantics remain preserved" clientOutboundPreserved
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies =
  case phase0RecognitionFailureBundle of
    Right bundle -> verifyRecognitionFailureBundle bundle == Right ()
    Left _ -> False

explicitDistinctReasons :: Bool
explicitDistinctReasons = withBundle $ \bundle ->
  let artifact = recognitionFailureArtifact bundle
      program = systemsArtifactProgram artifact
      witnesses = recognitionFailureWitnesses bundle
      reasons = map recognitionFailureReason witnesses
  in length reasons == 2
      && reasons !! 0 /= reasons !! 1
      && all (reasonHasExpectedRole program) witnesses
  where
    reasonHasExpectedRole program witness = doBool $ do
      function <- Map.lookup
        (recognitionFailureFunction witness)
        (systemsProgramFunctions program)
      value <- Map.lookup
        (recognitionFailureReason witness)
        (systemsFunctionValues function)
      pure (systemsValueRole value ==
        RuntimeOpaque ("RecognitionReason[" <> recognitionFailureGrammar witness <> "]"))

exactFailureFlows :: Bool
exactFailureFlows = withBundle $ \bundle ->
  let artifact = recognitionFailureArtifact bundle
      program = systemsArtifactProgram artifact
  in all (exactFlow program) (recognitionFailureWitnesses bundle)
  where
    exactFlow program witness = doBool $ do
      function <- Map.lookup
        (recognitionFailureFunction witness)
        (systemsProgramFunctions program)
      failureBlock <- Map.lookup
        (recognitionFailureFailureBlock witness)
        (systemsFunctionBlocks function)
      pure $ case systemsBlockOps failureBlock of
        [ OpRuntimeCall materializeName [materializePending] [reason] Nothing materializeDecision
          , OpRuntimeCall effectName [effectPending, effectReason] [] Nothing effectDecision
          , OpDestroyPending destroyPending destroyFrame _cleanupDecision
          ] ->
            materializeName == recognitionFailureMaterializeCall witness
              && materializePending == recognitionFailurePending witness
              && reason == recognitionFailureReason witness
              && materializeDecision == DecisionId "lower.recognition.failure_detail"
              && effectName == recognitionFailureEffectCall witness
              && effectPending == recognitionFailurePending witness
              && effectReason == recognitionFailureReason witness
              && effectDecision == DecisionId "lower.recognition.failure_detail"
              && destroyPending == recognitionFailurePending witness
              && destroyFrame == recognitionFailureFrameOwner witness
              && systemsBlockTerminator failureBlock ==
                   TermFatal (recognitionFailureFatalClass witness)
        _ -> False

extraReasonUseRejects :: Bool
extraReasonUseRejects = withBundle $ \bundle ->
  case recognitionFailureWitnesses bundle of
    [] -> False
    witness : _ ->
      let artifact = recognitionFailureArtifact bundle
          program = systemsArtifactProgram artifact
          mutatedProgram = program
            { systemsProgramFunctions = Map.adjust
                (mutateFailure witness)
                (recognitionFailureFunction witness)
                (systemsProgramFunctions program)
            }
          mutated = artifact { systemsArtifactProgram = mutatedProgram }
      in isLeft (verifyRecognitionFailureWitnesses
          mutated
          (recognitionFailureWitnesses bundle))
  where
    mutateFailure witness function = function
      { systemsFunctionBlocks = Map.adjust
          (\blockValue -> blockValue
            { systemsBlockOps = systemsBlockOps blockValue <>
                [ OpRuntimeCall
                    "inspect recognition reason"
                    [recognitionFailureReason witness]
                    []
                    Nothing
                    (DecisionId "lower.recognition.failure_detail")
                ]
            })
          (recognitionFailureFailureBlock witness)
          (systemsFunctionBlocks function)
      }

wrongPendingRejects :: Bool
wrongPendingRejects = withBundle $ \bundle ->
  case recognitionFailureWitnesses bundle of
    firstWitness : secondWitness : _ ->
      let artifact = recognitionFailureArtifact bundle
          program = systemsArtifactProgram artifact
          mutatedProgram = program
            { systemsProgramFunctions = Map.adjust
                (mutateMaterialize firstWitness secondWitness)
                (recognitionFailureFunction firstWitness)
                (systemsProgramFunctions program)
            }
          mutated = artifact { systemsArtifactProgram = mutatedProgram }
      in isLeft (verifyRecognitionFailureWitnesses
          mutated
          (recognitionFailureWitnesses bundle))
    _ -> False
  where
    mutateMaterialize witness other function = function
      { systemsFunctionBlocks = Map.adjust
          (\blockValue -> blockValue
            { systemsBlockOps = case systemsBlockOps blockValue of
                OpRuntimeCall name _inputs outputs site decision : rest ->
                  OpRuntimeCall
                    name
                    [recognitionFailurePending other]
                    outputs
                    site
                    decision : rest
                operations -> operations
            })
          (recognitionFailureFailureBlock witness)
          (systemsFunctionBlocks function)
      }

clientOutboundPreserved :: Bool
clientOutboundPreserved = withBundle $ \bundle ->
  verifyClientOutboundWitness
    (recognitionFailureArtifact bundle)
    phase0ClientOutboundWitness
    == Right ()

withBundle :: (RecognitionFailureBundle -> Bool) -> Bool
withBundle action = case phase0RecognitionFailureBundle of
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
