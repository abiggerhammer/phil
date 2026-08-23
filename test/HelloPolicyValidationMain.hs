{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "HelloPolicy validation candidate verifies" candidateVerifies
    , test "HelloPolicy validator has exact explicit subjects" exactValidatorSubjects
    , test "HelloPolicy rejected reason reaches exact fatal effect" exactReasonFlow
    , test "extra HelloPolicy reason observation is rejected" extraReasonUseRejects
    , test "wrong HelloPolicy validator subject is rejected" wrongValidatorSubjectRejects
    , test "BeginPolicy physical target fails closed on new HelloPolicy choice" priorLLVMTargetFailsClosed
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies =
  case phase0HelloPolicyValidationBundle of
    Right bundle -> verifyHelloPolicyValidationBundle bundle == Right ()
    Left _ -> False

exactValidatorSubjects :: Bool
exactValidatorSubjects = withBundle $ \bundle ->
  let witness = helloPolicyValidationWitness bundle
      program = systemsArtifactProgram (helloPolicyValidationArtifact bundle)
  in doBool $ do
      server <- Map.lookup (helloPolicyServerFunction witness) (systemsProgramFunctions program)
      commitBlock <- Map.lookup (helloPolicyCommitBlock witness) (systemsFunctionBlocks server)
      pure $ case systemsBlockTerminator commitBlock of
        TermRuntimeChoice name inputs (Just site) arms ->
          name == helloPolicyRuntimeChoiceName witness
            && inputs == [helloPolicyPolicyContext witness, helloPolicyHelloRecord witness]
            && runtimeSiteKind site == ValidationBoundary "HelloPolicy"
            && arms == Map.fromList
              [ (helloPolicyAcceptedArm witness,
                  SystemsRuntimeChoiceArm Nothing (helloPolicyAcceptedTarget witness))
              , (helloPolicyRejectedArm witness,
                  SystemsRuntimeChoiceArm
                    (Just (helloPolicyRejectReason witness))
                    (helloPolicyRejectedTarget witness))
              ]
        _ -> False

exactReasonFlow :: Bool
exactReasonFlow = withBundle $ \bundle ->
  let witness = helloPolicyValidationWitness bundle
      program = systemsArtifactProgram (helloPolicyValidationArtifact bundle)
  in doBool $ do
      server <- Map.lookup (helloPolicyServerFunction witness) (systemsProgramFunctions program)
      failureBlock <- Map.lookup (helloPolicyRejectedTarget witness) (systemsFunctionBlocks server)
      pure $
        systemsBlockOps failureBlock ==
          [ OpRuntimeCall
              (helloPolicyFailureCall witness)
              [helloPolicyServerTransport witness, helloPolicyRejectReason witness]
              []
              Nothing
              (helloPolicyLoweringDecision witness)
          ]
        && systemsBlockTerminator failureBlock == TermFatal (helloPolicyFailureClass witness)

extraReasonUseRejects :: Bool
extraReasonUseRejects = withBundle $ \bundle ->
  let witness = helloPolicyValidationWitness bundle
      artifact = helloPolicyValidationArtifact bundle
      program = systemsArtifactProgram artifact
      mutatedProgram = program
        { systemsProgramFunctions = Map.adjust
            (mutateFailure witness)
            (helloPolicyServerFunction witness)
            (systemsProgramFunctions program)
        }
      mutated = rebindArtifact bundle mutatedProgram
  in isLeft (verifyHelloPolicyValidationWitness mutated witness)
  where
    mutateFailure witness function = function
      { systemsFunctionBlocks = Map.adjust
          (\blockValue -> blockValue
            { systemsBlockOps = systemsBlockOps blockValue <>
                [ OpRuntimeCall
                    "inspect HelloPolicy reason"
                    [helloPolicyRejectReason witness]
                    []
                    Nothing
                    (helloPolicyLoweringDecision witness)
                ]
            })
          (helloPolicyRejectedTarget witness)
          (systemsFunctionBlocks function)
      }

wrongValidatorSubjectRejects :: Bool
wrongValidatorSubjectRejects = withBundle $ \bundle ->
  let witness = helloPolicyValidationWitness bundle
      artifact = helloPolicyValidationArtifact bundle
      program = systemsArtifactProgram artifact
      wrongSubject = versionOperandsHelloVersions phase0VersionChoiceOperandsWitness
      mutatedProgram = program
        { systemsProgramFunctions = Map.adjust
            (\function -> function
              { systemsFunctionBlocks = Map.adjust
                  (\blockValue -> blockValue
                    { systemsBlockTerminator = case systemsBlockTerminator blockValue of
                        TermRuntimeChoice name _ site arms ->
                          TermRuntimeChoice name
                            [helloPolicyPolicyContext witness, wrongSubject]
                            site arms
                        other -> other
                    })
                  (helloPolicyCommitBlock witness)
                  (systemsFunctionBlocks function)
              })
            (helloPolicyServerFunction witness)
            (systemsProgramFunctions program)
        }
      mutated = rebindArtifact bundle mutatedProgram
  in isLeft (verifyHelloPolicyValidationWitness mutated witness)

priorLLVMTargetFailsClosed :: Bool
priorLLVMTargetFailsClosed = withBundle $ \bundle ->
  let systemsArtifact = helloPolicyValidationArtifact bundle
      target = phase0BeginPolicyChoiceLLVMTarget
      llvmArtifact = lowerSystemsBeginPolicyChoice target systemsArtifact
      context = LLVMVerificationContext
        { llvmSystemsContext = helloPolicyValidationContext bundle
        , llvmExpectedLanguageVersion = llvmTargetLanguageVersion target
        , llvmExpectedToolVersion = llvmTargetToolVersion target
        , llvmExpectedTargetTriple = llvmTargetTripleName target
        , llvmExpectedDataLayout = llvmTargetDataLayout target
        , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest target
        , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile target
        , llvmAuthorizedStrengthenings = mempty
        }
  in case verifyLLVMEmissionWith lowerSystemsBeginPolicyChoice context systemsArtifact llvmArtifact of
      Left (LLVMUnjustifiedUnreachable functionName blockId) ->
        functionName == "UploadServer" && blockId == LLVMBlockId "server.hello.commit"
      Left _ -> False
      Right () -> False

rebindArtifact :: HelloPolicyValidationBundle -> SystemsProgram -> SystemsArtifact
rebindArtifact bundle program =
  let artifact = helloPolicyValidationArtifact bundle
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

withBundle :: (HelloPolicyValidationBundle -> Bool) -> Bool
withBundle action = case phase0HelloPolicyValidationBundle of
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
