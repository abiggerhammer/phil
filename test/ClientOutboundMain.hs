{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "client outbound candidate verifies" candidateVerifies
    , test "Hello construction and send use exact supported-version record" exactHelloDataflow
    , test "Begin construction uses exact payload fields and SHA-256 digest" exactBeginDataflow
    , test "legacy bare Hello send is rejected" bareHelloSendRejects
    , test "wrong Begin digest operand is rejected" wrongBeginDigestRejects
    , test "predecessor semantic witnesses remain valid" predecessorWitnessesPreserved
    , test "PHIL-LLVM-CERT-013 does not cover successor Systems digest" cert013DoesNotCoverSuccessor
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies = case phase0ClientOutboundBundle of
  Right bundle -> verifyClientOutboundBundle bundle == Right ()
  Left _ -> False

exactHelloDataflow :: Bool
exactHelloDataflow = withBundle $ \bundle ->
  let witness = clientOutboundWitness bundle
      program = systemsArtifactProgram (clientOutboundArtifact bundle)
  in doBool $ do
      client <- Map.lookup (clientOutboundFunction witness) (systemsProgramFunctions program)
      blockValue <- Map.lookup (clientOutboundEntryBlock witness) (systemsFunctionBlocks client)
      pure (systemsBlockOps blockValue ==
        [ OpRuntimeCall
            (clientOutboundSupportedVersionsCall witness)
            []
            [clientOutboundSupportedVersions witness]
            Nothing
            (clientOutboundSemanticCallDecision witness)
        , OpRuntimeCall
            (clientOutboundConstructHelloCall witness)
            [clientOutboundSupportedVersions witness]
            [clientOutboundHelloRecord witness]
            Nothing
            (clientOutboundRecordDecision witness)
        , OpRuntimeCall
            (clientOutboundSendHelloCall witness)
            [clientOutboundTransport witness, clientOutboundHelloRecord witness]
            []
            Nothing
            (clientOutboundSemanticCallDecision witness)
        ])

exactBeginDataflow :: Bool
exactBeginDataflow = withBundle $ \bundle ->
  let witness = clientOutboundWitness bundle
      program = systemsArtifactProgram (clientOutboundArtifact bundle)
  in doBool $ do
      client <- Map.lookup (clientOutboundFunction witness) (systemsProgramFunctions program)
      blockValue <- Map.lookup (clientOutboundVersionBlock witness) (systemsFunctionBlocks client)
      pure (systemsBlockOps blockValue ==
        [ OpBorrowView
            (clientOutboundPayloadView witness)
            (clientOutboundPayload witness)
            (clientOutboundBorrowDecision witness)
        , OpRuntimeCall
            (clientOutboundDigestCall witness)
            [clientOutboundPayloadView witness]
            [clientOutboundDeclaredDigest witness]
            Nothing
            (clientOutboundDigestDecision witness)
        , OpRuntimeCall
            (clientOutboundProjectLengthCall witness)
            [clientOutboundPayload witness]
            [clientOutboundPayloadLength witness]
            Nothing
            (clientOutboundRecordDecision witness)
        , OpRuntimeCall
            (clientOutboundProjectKindCall witness)
            [clientOutboundPayload witness]
            [clientOutboundPayloadKind witness]
            Nothing
            (clientOutboundRecordDecision witness)
        , OpRuntimeCall
            (clientOutboundConstructBeginCall witness)
            [ clientOutboundPayloadLength witness
            , clientOutboundPayloadKind witness
            , clientOutboundDeclaredDigest witness
            ]
            [clientOutboundBeginRecord witness]
            Nothing
            (clientOutboundRecordDecision witness)
        , OpRuntimeCall
            (clientOutboundSendBeginCall witness)
            [clientOutboundTransport witness, clientOutboundBeginRecord witness]
            []
            Nothing
            (clientOutboundSemanticCallDecision witness)
        ])

bareHelloSendRejects :: Bool
bareHelloSendRejects = withBundle $ \bundle ->
  let witness = clientOutboundWitness bundle
      artifact = clientOutboundArtifact bundle
      program = systemsArtifactProgram artifact
      mutatedProgram = program
        { systemsProgramFunctions = Map.adjust
            (\client -> client
              { systemsFunctionBlocks = Map.adjust
                  (\blockValue -> blockValue
                    { systemsBlockOps = map (mutateSend witness) (systemsBlockOps blockValue)
                    })
                  (clientOutboundEntryBlock witness)
                  (systemsFunctionBlocks client)
              })
            (clientOutboundFunction witness)
            (systemsProgramFunctions program)
        }
      mutated = rebindArtifact artifact mutatedProgram
  in isLeft (verifyClientOutboundWitness mutated witness)
  where
    mutateSend witness operation = case operation of
      OpRuntimeCall name _ [] Nothing decision
        | name == clientOutboundSendHelloCall witness ->
            OpRuntimeCall name [clientOutboundTransport witness] [] Nothing decision
      other -> other

wrongBeginDigestRejects :: Bool
wrongBeginDigestRejects = withBundle $ \bundle ->
  let witness = clientOutboundWitness bundle
      artifact = clientOutboundArtifact bundle
      program = systemsArtifactProgram artifact
      mutatedProgram = program
        { systemsProgramFunctions = Map.adjust
            (\client -> client
              { systemsFunctionBlocks = Map.adjust
                  (\blockValue -> blockValue
                    { systemsBlockOps = map (mutateConstruct witness) (systemsBlockOps blockValue)
                    })
                  (clientOutboundVersionBlock witness)
                  (systemsFunctionBlocks client)
              })
            (clientOutboundFunction witness)
            (systemsProgramFunctions program)
        }
      mutated = rebindArtifact artifact mutatedProgram
  in isLeft (verifyClientOutboundWitness mutated witness)
  where
    mutateConstruct witness operation = case operation of
      OpRuntimeCall name inputs outputs site decision
        | name == clientOutboundConstructBeginCall witness ->
            OpRuntimeCall name
              [ clientOutboundPayloadLength witness
              , clientOutboundPayloadKind witness
              , clientOutboundSupportedVersions witness
              ]
              outputs site decision
      other -> other

predecessorWitnessesPreserved :: Bool
predecessorWitnessesPreserved = withBundle $ \bundle ->
  let artifact = clientOutboundArtifact bundle
  in verifyHelloPolicyValidationWitness artifact phase0HelloPolicyValidationWitness == Right ()
      && verifyBeginPolicySessionChoiceWitness artifact phase0BeginPolicySessionChoiceWitness == Right ()
      && verifyVersionChoiceOperandsWitness artifact phase0VersionChoiceOperandsWitness == Right ()

cert013DoesNotCoverSuccessor :: Bool
cert013DoesNotCoverSuccessor = withBundle $ \bundle ->
  case phase0ExactSendLLVMCertification of
    Left _ -> False
    Right certification ->
      let certifiedSource = llvmContractSourceDigest
            (llvmArtifactContract (exactSendCertificationLLVM certification))
          successorSource = systemsArtifactDigest (clientOutboundArtifact bundle)
      in certifiedSource /= successorSource

rebindArtifact :: SystemsArtifact -> SystemsProgram -> SystemsArtifact
rebindArtifact artifact program =
  let contract0 = systemsArtifactStageContract artifact
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

withBundle :: (ClientOutboundBundle -> Bool) -> Bool
withBundle action = case phase0ClientOutboundBundle of
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
