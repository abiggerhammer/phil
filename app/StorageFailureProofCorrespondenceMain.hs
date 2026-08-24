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
    , test "current successor preserves RecognitionFailure witnesses" preservesRecognitionFailure
    , test "current successor preserves certified ClientOutbound witness" preservesClientOutbound
    , test "store ownership/result/site/continuations are unchanged" storeBoundaryUnchanged
    , test "storage failure error flow is exact" exactStorageErrorFlow
    , test "storage failure adds only the StorageError value" onlyStorageErrorValueAdded
    , test "storage failure decision is rebound to current successor" decisionRebound
    , test "error substitution drift is rejected" errorSubstitutionDriftRejects
    , test "post-transfer payload use drift is rejected" postTransferPayloadUseDriftRejects
    ]
  if and results then pure () else exitFailure

currentSuccessorVerifies :: Bool
currentSuccessorVerifies = withCurrent $ \bundle ->
  verifyStorageFailureBundle bundle == Right ()

preservesRecognitionFailure :: Bool
preservesRecognitionFailure = withCurrent $ \bundle ->
  verifyRecognitionFailureWitnesses
    (storageFailureArtifact bundle)
    phase0RecognitionFailureWitnesses == Right ()

preservesClientOutbound :: Bool
preservesClientOutbound = withCurrent $ \bundle ->
  verifyClientOutboundWitness
    (storageFailureArtifact bundle)
    phase0ClientOutboundWitness == Right ()

storeBoundaryUnchanged :: Bool
storeBoundaryUnchanged = withCurrent $ \bundle ->
  let witness = storageFailureWitness bundle
      currentProgram = systemsArtifactProgram (storageFailureArtifact bundle)
      predecessorProgram = systemsArtifactProgram
        (recognitionFailureArtifact (storageFailurePredecessor bundle))
  in doBool $ do
      currentFunction <- Map.lookup
        (storageFailureFunction witness)
        (systemsProgramFunctions currentProgram)
      predecessorFunction <- Map.lookup
        (storageFailureFunction witness)
        (systemsProgramFunctions predecessorProgram)
      currentBlock <- Map.lookup
        (storageFailureStoreBlock witness)
        (systemsFunctionBlocks currentFunction)
      predecessorBlock <- Map.lookup
        (storageFailureStoreBlock witness)
        (systemsFunctionBlocks predecessorFunction)
      let exactCurrent = case systemsBlockTerminator currentBlock of
            TermStore owner result site _success failure ->
              owner == storageFailureOwner witness
                && result == storageFailureSuccessResult witness
                && runtimeSiteKind site == StorageBoundary
                && failure == storageFailureFailureBlock witness
            _ -> False
      pure
        ( exactCurrent
        && systemsBlockTerminator currentBlock == systemsBlockTerminator predecessorBlock
        )

exactStorageErrorFlow :: Bool
exactStorageErrorFlow = withCurrent $ \bundle ->
  let witness = storageFailureWitness bundle
      artifact = storageFailureArtifact bundle
      program = systemsArtifactProgram artifact
  in doBool $ do
      function <- Map.lookup
        (storageFailureFunction witness)
        (systemsProgramFunctions program)
      errorValue <- Map.lookup
        (storageFailureErrorValue witness)
        (systemsFunctionValues function)
      failureBlock <- Map.lookup
        (storageFailureFailureBlock witness)
        (systemsFunctionBlocks function)
      let expectedOps =
            [ OpRuntimeCall
                (storageFailureMaterializeCall witness)
                []
                [storageFailureErrorValue witness]
                Nothing
                (storageFailureDecision witness)
            , OpRuntimeCall
                (storageFailureEffectCall witness)
                [ storageFailureTransport witness
                , storageFailureErrorValue witness
                ]
                []
                Nothing
                (storageFailureDecision witness)
            ]
          uses = errorUses
            (storageFailureErrorValue witness)
            function
      pure
        ( systemsValueRole errorValue == RuntimeOpaque "StorageError"
        && systemsBlockOps failureBlock == expectedOps
        && systemsBlockTerminator failureBlock ==
            TermFatal (storageFailureFatalClass witness)
        && uses ==
            [ ( storageFailureFailureBlock witness
              , "runtime-call:" <> storageFailureEffectCall witness
              )
            ]
        && not (valueUsedInBlock
            (storageFailureOwner witness)
            failureBlock)
        )

onlyStorageErrorValueAdded :: Bool
onlyStorageErrorValueAdded = withCurrent $ \bundle ->
  let witness = storageFailureWitness bundle
      currentProgram = systemsArtifactProgram (storageFailureArtifact bundle)
      predecessorProgram = systemsArtifactProgram
        (recognitionFailureArtifact (storageFailurePredecessor bundle))
  in doBool $ do
      currentFunction <- Map.lookup
        (storageFailureFunction witness)
        (systemsProgramFunctions currentProgram)
      predecessorFunction <- Map.lookup
        (storageFailureFunction witness)
        (systemsProgramFunctions predecessorProgram)
      let currentValues = systemsFunctionValues currentFunction
          predecessorValues = systemsFunctionValues predecessorFunction
      pure
        ( Map.member (storageFailureErrorValue witness) currentValues
        && Map.delete (storageFailureErrorValue witness) currentValues == predecessorValues
        )

decisionRebound :: Bool
decisionRebound = withCurrent $ \bundle ->
  let witness = storageFailureWitness bundle
      artifact = storageFailureArtifact bundle
      targetDigest = systemsProgramDigest (systemsArtifactProgram artifact)
      decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
  in decisionTargets targetDigest decisions (storageFailureDecision witness)

decisionTargets
  :: Digest
  -> Map.Map DecisionId LoweringDecision
  -> DecisionId
  -> Bool
decisionTargets targetDigest decisions decisionId =
  case Map.lookup decisionId decisions of
    Just decision -> loweringTargetArtifactDigest decision == targetDigest
    Nothing -> False

errorSubstitutionDriftRejects :: Bool
errorSubstitutionDriftRejects = withCurrent $ \bundle ->
  let witness = storageFailureWitness bundle
      artifact = storageFailureArtifact bundle
      program = systemsArtifactProgram artifact
      functions' = Map.adjust
        (\function -> function
          { systemsFunctionBlocks = Map.adjust
              (\blockValue -> blockValue
                { systemsBlockOps = map (substituteError witness)
                    (systemsBlockOps blockValue)
                })
              (storageFailureFailureBlock witness)
              (systemsFunctionBlocks function)
          })
        (storageFailureFunction witness)
        (systemsProgramFunctions program)
      mutated = artifact
        { systemsArtifactProgram = program { systemsProgramFunctions = functions' } }
  in isLeft (verifyStorageFailureWitness mutated witness)

substituteError :: StorageFailureWitness -> SystemsOp -> SystemsOp
substituteError witness operation = case operation of
  OpRuntimeCall name [transport, _error] [] Nothing decision
    | name == storageFailureEffectCall witness ->
        OpRuntimeCall name
          [transport, storageFailureOwner witness]
          [] Nothing decision
  other -> other

postTransferPayloadUseDriftRejects :: Bool
postTransferPayloadUseDriftRejects = withCurrent $ \bundle ->
  let witness = storageFailureWitness bundle
      artifact = storageFailureArtifact bundle
      program = systemsArtifactProgram artifact
      illegalUse = OpRuntimeCall
        "illegal post-transfer payload observation"
        [storageFailureOwner witness]
        [] Nothing
        (storageFailureDecision witness)
      functions' = Map.adjust
        (\function -> function
          { systemsFunctionBlocks = Map.adjust
              (\blockValue -> blockValue
                { systemsBlockOps = systemsBlockOps blockValue <> [illegalUse] })
              (storageFailureFailureBlock witness)
              (systemsFunctionBlocks function)
          })
        (storageFailureFunction witness)
        (systemsProgramFunctions program)
      mutated = artifact
        { systemsArtifactProgram = program { systemsProgramFunctions = functions' } }
  in isLeft (verifyStorageFailureWitness mutated witness)

errorUses :: ValueId -> SystemsFunction -> [(BlockId, Text)]
errorUses valueId function =
  [ (systemsBlockId blockValue, "runtime-call:" <> name)
  | blockValue <- Map.elems (systemsFunctionBlocks function)
  , OpRuntimeCall name inputs _outputs _site _decision <- systemsBlockOps blockValue
  , valueId `elem` inputs
  ]

valueUsedInBlock :: ValueId -> SystemsBlock -> Bool
valueUsedInBlock valueId blockValue =
  any (operationUses valueId) (systemsBlockOps blockValue)

operationUses :: ValueId -> SystemsOp -> Bool
operationUses valueId operation = case operation of
  OpRuntimeCall _ inputs _ _ _ -> valueId `elem` inputs
  OpBorrowView _ owner _ -> valueId == owner
  OpCopy source _ _ -> valueId == source
  OpDestroyPending pending frame _ -> valueId == pending || valueId == frame
  _ -> False

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
