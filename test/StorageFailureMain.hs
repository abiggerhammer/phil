{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "storage failure candidate verifies" candidateVerifies
    , test "recognition failure detail survives storage successor" recognitionFailurePreserved
    , test "storage failure binds exact error" exactErrorFlow
    , test "storage failure does not regain payload" payloadUnavailable
    , test "extra storage error observation is rejected" extraErrorUseRejects
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies =
  case phase0StorageFailureBundle of
    Right bundle -> verifyStorageFailureBundle bundle == Right ()
    Left _ -> False

recognitionFailurePreserved :: Bool
recognitionFailurePreserved = withBundle $ \bundle ->
  verifyRecognitionFailureWitnesses
    (storageFailureArtifact bundle)
    phase0RecognitionFailureWitnesses == Right ()

exactErrorFlow :: Bool
exactErrorFlow = withBundle $ \bundle ->
  let witness = storageFailureWitness bundle
      program = systemsArtifactProgram (storageFailureArtifact bundle)
  in doBool $ do
      server <- Map.lookup (storageFailureFunction witness) (systemsProgramFunctions program)
      failureBlock <- Map.lookup (storageFailureFailureBlock witness) (systemsFunctionBlocks server)
      errorValue <- Map.lookup (storageFailureErrorValue witness) (systemsFunctionValues server)
      pure $
        systemsValueRole errorValue == RuntimeOpaque "StorageError"
          && systemsBlockOps failureBlock ==
            [ OpRuntimeCall
                (storageFailureMaterializeCall witness)
                []
                [storageFailureErrorValue witness]
                Nothing
                (storageFailureDecision witness)
            , OpRuntimeCall
                (storageFailureEffectCall witness)
                [storageFailureTransport witness, storageFailureErrorValue witness]
                []
                Nothing
                (storageFailureDecision witness)
            ]
          && systemsBlockTerminator failureBlock == TermFatal (storageFailureFatalClass witness)

payloadUnavailable :: Bool
payloadUnavailable = withBundle $ \bundle ->
  let witness = storageFailureWitness bundle
      program = systemsArtifactProgram (storageFailureArtifact bundle)
  in doBool $ do
      server <- Map.lookup (storageFailureFunction witness) (systemsProgramFunctions program)
      failureBlock <- Map.lookup (storageFailureFailureBlock witness) (systemsFunctionBlocks server)
      pure $ all (not . usesPayload witness) (systemsBlockOps failureBlock)
  where
    usesPayload witness operation = case operation of
      OpRuntimeCall _ inputs _ _ _ -> storageFailureOwner witness `elem` inputs
      OpReleaseOwner owner _ -> owner == storageFailureOwner witness
      OpCleanupPartial owner _ -> owner == storageFailureOwner witness
      OpCopy source _ _ -> source == storageFailureOwner witness
      OpBorrowView _ owner _ -> owner == storageFailureOwner witness
      _ -> False

extraErrorUseRejects :: Bool
extraErrorUseRejects = withBundle $ \bundle ->
  let witness = storageFailureWitness bundle
      artifact = storageFailureArtifact bundle
      program = systemsArtifactProgram artifact
      mutatedProgram = program
        { systemsProgramFunctions = Map.adjust
            (\function -> function
              { systemsFunctionBlocks = Map.adjust
                  (\blockValue -> blockValue
                    { systemsBlockOps = systemsBlockOps blockValue <>
                        [ OpRuntimeCall
                            "inspect storage error"
                            [storageFailureErrorValue witness]
                            []
                            Nothing
                            (storageFailureDecision witness)
                        ]
                    })
                  (storageFailureFailureBlock witness)
                  (systemsFunctionBlocks function)
              })
            (storageFailureFunction witness)
            (systemsProgramFunctions program)
        }
      mutated = rebindArtifact bundle mutatedProgram
  in isLeft (verifyStorageFailureWitness mutated witness)

rebindArtifact :: StorageFailureBundle -> SystemsProgram -> SystemsArtifact
rebindArtifact bundle program =
  let artifact = storageFailureArtifact bundle
      contract0 = systemsArtifactStageContract artifact
      targetDigest = systemsProgramDigest program
      contract = contract0 { stageTargetArtifactDigest = targetDigest }
      decisions0 = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      decisions = Map.map (rebind targetDigest) decisions0
      root = deriveLoweringLedgerRoot decisions
  in SystemsArtifact program contract (LoweringLedger decisions root)
  where
    rebind targetDigest lowering = provisional
      { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
      where
        provisional = lowering { loweringTargetArtifactDigest = targetDigest }

withBundle :: (StorageFailureBundle -> Bool) -> Bool
withBundle action = case phase0StorageFailureBundle of
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
