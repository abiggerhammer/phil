{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Assurance.Types (Digest)
import Phil.Systems.ClientOutbound
import Phil.Systems.IR
import Phil.Systems.RecognitionFailure
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "current RecognitionFailure successor verifies" currentSuccessorVerifies
    , test "current successor preserves ClientOutbound witness" currentSuccessorPreservesClientOutbound
    , test "current successor has exact Hello dataflow" exactHelloDataflow
    , test "current successor has exact Begin dataflow" exactBeginDataflow
    , test "current successor preserves no-copy payload borrow" exactBorrowNoCopy
    , test "ClientOutbound decisions are rebound to current successor" decisionsRebound
    ]
  if and results then pure () else exitFailure

currentSuccessorVerifies :: Bool
currentSuccessorVerifies = case phase0RecognitionFailureBundle of
  Left _ -> False
  Right bundle -> verifyRecognitionFailureBundle bundle == Right ()

currentSuccessorPreservesClientOutbound :: Bool
currentSuccessorPreservesClientOutbound = withCurrent $ \bundle ->
  verifyClientOutboundWitness
    (recognitionFailureArtifact bundle)
    phase0ClientOutboundWitness == Right ()

exactHelloDataflow :: Bool
exactHelloDataflow = withCurrent $ \bundle ->
  let witness = phase0ClientOutboundWitness
      program = systemsArtifactProgram (recognitionFailureArtifact bundle)
  in doBool $ do
      client <- Map.lookup (clientOutboundFunction witness) (systemsProgramFunctions program)
      blockValue <- Map.lookup
        (clientOutboundEntryBlock witness)
        (systemsFunctionBlocks client)
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
exactBeginDataflow = withCurrent $ \bundle ->
  let witness = phase0ClientOutboundWitness
      program = systemsArtifactProgram (recognitionFailureArtifact bundle)
  in doBool $ do
      client <- Map.lookup (clientOutboundFunction witness) (systemsProgramFunctions program)
      blockValue <- Map.lookup
        (clientOutboundVersionBlock witness)
        (systemsFunctionBlocks client)
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

exactBorrowNoCopy :: Bool
exactBorrowNoCopy = withCurrent $ \bundle ->
  let witness = phase0ClientOutboundWitness
      program = systemsArtifactProgram (recognitionFailureArtifact bundle)
  in doBool $ do
      client <- Map.lookup (clientOutboundFunction witness) (systemsProgramFunctions program)
      let operations =
            [ operation
            | blockValue <- Map.elems (systemsFunctionBlocks client)
            , operation <- systemsBlockOps blockValue
            ]
          borrows =
            [ ()
            | OpBorrowView view owner _ <- operations
            , view == clientOutboundPayloadView witness
            , owner == clientOutboundPayload witness
            ]
          copies =
            [ ()
            | OpCopy source _ _ <- operations
            , source == clientOutboundPayload witness
            ]
      pure (length borrows == 1 && null copies)

decisionsRebound :: Bool
decisionsRebound = withCurrent $ \bundle ->
  let witness = phase0ClientOutboundWitness
      artifact = recognitionFailureArtifact bundle
      targetDigest = systemsProgramDigest (systemsArtifactProgram artifact)
      decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      ids =
        [ clientOutboundRecordDecision witness
        , clientOutboundBorrowDecision witness
        , clientOutboundDigestDecision witness
        ]
  in all (decisionTargets targetDigest decisions) ids
      && case Map.lookup
          (clientOutboundBorrowInvariant witness)
          (stageInvariants (systemsArtifactStageContract artifact)) of
          Just StageInvariant
            { stageInvariantClaim = InvariantBorrowAliases functionName view owner
            } ->
              functionName == clientOutboundFunction witness
                && view == clientOutboundPayloadView witness
                && owner == clientOutboundPayload witness
          _ -> False

decisionTargets
  :: Digest
  -> Map.Map DecisionId LoweringDecision
  -> DecisionId
  -> Bool
decisionTargets targetDigest decisions decisionId =
  case Map.lookup decisionId decisions of
    Just decision -> loweringTargetArtifactDigest decision == targetDigest
    Nothing -> False

withCurrent :: (RecognitionFailureBundle -> Bool) -> Bool
withCurrent action = case phase0RecognitionFailureBundle of
  Left _ -> False
  Right bundle -> action bundle

doBool :: Maybe Bool -> Bool
doBool = maybe False id

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
