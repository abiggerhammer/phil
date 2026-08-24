{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.LLVM.IR
import Phil.LLVM.ServerFramedIngress
import Phil.Systems.IR
import Phil.Systems.RecognitionFailure
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "server framed-ingress translation verifies" currentCandidateVerifies
    , test "Hello ingress preserves exact receive/borrow/recognition identities" helloIngressExact
    , test "Begin ingress preserves exact receive/borrow/recognition identities" beginIngressExact
    , test "failure flows forward exact reasons then destroy exact pending/frame" failureFlowsExact
    , test "commit flows preserve exact transport and pending handles" commitFlowsExact
    , test "wrong Hello recognition reason identity is rejected" wrongHelloReasonRejects
    , test "failure cleanup/effect reordering is rejected" reorderedFailureRejects
    , test "ambient ingress state is rejected" ambientStateRejects
    , test "legacy nullary ingress residue is rejected" legacyResidueRejects
    ]
  if and results then pure () else exitFailure

currentCandidateVerifies :: Bool
currentCandidateVerifies = verifyPhase0ServerFramedIngressLLVM == Right ()

helloIngressExact :: Bool
helloIngressExact = withCandidate (ingressExactFor "Hello")

beginIngressExact :: Bool
beginIngressExact = withCandidate (ingressExactFor "Begin")

ingressExactFor :: Text -> RecognitionFailureBundle -> LLVMArtifact -> Bool
ingressExactFor grammar bundle artifact = doBool $ do
  witness <- unique
    [ candidate
    | candidate <- recognitionFailureWitnesses bundle
    , recognitionFailureGrammar candidate == grammar
    ]
  systemsFunction <- Map.lookup
    (recognitionFailureFunction witness)
    (systemsProgramFunctions (systemsArtifactProgram (recognitionFailureArtifact bundle)))
  systemsRecognition <- Map.lookup
    (recognitionFailureRecognitionBlock witness)
    (systemsFunctionBlocks systemsFunction)
  (pending, raw, site, success, failure) <- case systemsBlockTerminator systemsRecognition of
    TermRecognize p r s yes no -> Just (p, r, s, yes, no)
    _ -> Nothing
  (transport, frame) <- unique
    [ (receiveTransport operation, receiveFrameOwner operation)
    | operation@OpReceiveFrame {} <- systemsBlockOps systemsRecognition
    , receivePending operation == pending
    , receiveGrammar operation == grammar
    ]
  _ <- unique
    [ ()
    | OpBorrowView view owner _ <- systemsBlockOps systemsRecognition
    , view == raw
    , owner == frame
    ]
  systemsSuccess <- Map.lookup success (systemsFunctionBlocks systemsFunction)
  record <- unique
    [ output
    | OpRuntimeCall name [] [output] Nothing _ <- systemsBlockOps systemsSuccess
    , name == "materialize recognized " <> grammar
    ]
  llvmFunction <- Map.lookup
    (recognitionFailureFunction witness)
    (llvmFunctions (llvmArtifactModule artifact))
  llvmRecognition <- Map.lookup
    (LLVMBlockId (unBlockId (recognitionFailureRecognitionBlock witness)))
    (llvmFunctionBlocks llvmFunction)
  let expectedReceive = LLVMServerReceiveFrame
        grammar
        (unValueId pending)
        (unValueId frame)
        (unValueId transport)
      expectedBorrow = LLVMServerBorrowFrameView
        grammar
        (unValueId raw)
        (unValueId frame)
      expectedTerminator = LLVMRecognizeRecordDetailed
        site
        grammar
        (unValueId pending)
        (unValueId raw)
        (unValueId record)
        (unValueId (recognitionFailureReason witness))
        (LLVMBlockId (unBlockId success))
        (LLVMBlockId (unBlockId failure))
  pure $
    expectedReceive `elem` llvmBlockOps llvmRecognition
      && expectedBorrow `elem` llvmBlockOps llvmRecognition
      && llvmBlockTerminator llvmRecognition == expectedTerminator

failureFlowsExact :: Bool
failureFlowsExact = withCandidate $ \_ artifact -> doBool $ do
  server <- Map.lookup "UploadServer" (llvmFunctions (llvmArtifactModule artifact))
  helloFailure <- Map.lookup (LLVMBlockId "server.hello.recognition_failure") (llvmFunctionBlocks server)
  beginFailure <- Map.lookup (LLVMBlockId "server.begin.recognition_failure") (llvmFunctionBlocks server)
  pure $
    llvmBlockOps helloFailure ==
      [ LLVMServerFailRecognition "Hello" "server.pending.hello" "server.hello_recognition_reason"
      , LLVMServerDestroyPending "Hello" "server.pending.hello" "server.frame.hello"
      ]
    && llvmBlockOps beginFailure ==
      [ LLVMServerFailRecognition "Begin" "server.pending.begin" "server.begin_recognition_reason"
      , LLVMServerDestroyPending "Begin" "server.pending.begin" "server.frame.begin"
      ]

commitFlowsExact :: Bool
commitFlowsExact = withCandidate $ \bundle artifact ->
  commitExactFor "Hello" bundle artifact && commitExactFor "Begin" bundle artifact

commitExactFor :: Text -> RecognitionFailureBundle -> LLVMArtifact -> Bool
commitExactFor grammar bundle artifact = doBool $ do
  witness <- unique
    [ candidate
    | candidate <- recognitionFailureWitnesses bundle
    , recognitionFailureGrammar candidate == grammar
    ]
  systemsFunction <- Map.lookup
    (recognitionFailureFunction witness)
    (systemsProgramFunctions (systemsArtifactProgram (recognitionFailureArtifact bundle)))
  systemsRecognition <- Map.lookup
    (recognitionFailureRecognitionBlock witness)
    (systemsFunctionBlocks systemsFunction)
  (pending, success) <- case systemsBlockTerminator systemsRecognition of
    TermRecognize p _ _ yes _ -> Just (p, yes)
    _ -> Nothing
  transport <- unique
    [ receiveTransport operation
    | operation@OpReceiveFrame {} <- systemsBlockOps systemsRecognition
    , receivePending operation == pending
    , receiveGrammar operation == grammar
    ]
  llvmFunction <- Map.lookup
    (recognitionFailureFunction witness)
    (llvmFunctions (llvmArtifactModule artifact))
  llvmCommit <- Map.lookup
    (LLVMBlockId (unBlockId success))
    (llvmFunctionBlocks llvmFunction)
  pure $
    LLVMServerCommitIngress grammar (unValueId transport) (unValueId pending)
      `elem` llvmBlockOps llvmCommit

wrongHelloReasonRejects :: Bool
wrongHelloReasonRejects = withCandidate $ \bundle artifact ->
  let mutated = mutateServerBlock (LLVMBlockId "server.entry") mutateTerm artifact
      mutateTerm blockValue = blockValue
        { llvmBlockTerminator = case llvmBlockTerminator blockValue of
            LLVMRecognizeRecordDetailed site grammar pending raw record _reason yes no ->
              LLVMRecognizeRecordDetailed site grammar pending raw record "wrong.hello.reason" yes no
            other -> other
        }
  in isLeft (verifyServerFramedIngressLLVMWitnesses bundle mutated)

reorderedFailureRejects :: Bool
reorderedFailureRejects = withCandidate $ \bundle artifact ->
  let mutated = mutateServerBlock
        (LLVMBlockId "server.hello.recognition_failure")
        (\blockValue -> blockValue { llvmBlockOps = reverse (llvmBlockOps blockValue) })
        artifact
  in isLeft (verifyServerFramedIngressLLVMWitnesses bundle mutated)

ambientStateRejects :: Bool
ambientStateRejects = withCandidate $ \bundle artifact ->
  let mutated = artifact { llvmArtifactText = llvmArtifactText artifact <> "\ncurrent_pending\n" }
  in isLeft (verifyServerFramedIngressLLVMWitnesses bundle mutated)

legacyResidueRejects :: Bool
legacyResidueRejects = withCandidate $ \bundle artifact ->
  let mutated = artifact { llvmArtifactText = llvmArtifactText artifact <> "\n@phil_runtime_recognize_Hello()\n" }
  in isLeft (verifyServerFramedIngressLLVMWitnesses bundle mutated)

mutateServerBlock :: LLVMBlockId -> (LLVMBlock -> LLVMBlock) -> LLVMArtifact -> LLVMArtifact
mutateServerBlock blockId transform artifact =
  let moduleValue = llvmArtifactModule artifact
      functions' = Map.adjust
        (\function -> function
          { llvmFunctionBlocks = Map.adjust transform blockId (llvmFunctionBlocks function) })
        "UploadServer"
        (llvmFunctions moduleValue)
  in artifact { llvmArtifactModule = moduleValue { llvmFunctions = functions' } }

withCandidate :: (RecognitionFailureBundle -> LLVMArtifact -> Bool) -> Bool
withCandidate action = case phase0RecognitionFailureBundle of
  Left _ -> False
  Right bundle ->
    let artifact = lowerSystemsServerFramedIngress
          phase0ServerFramedIngressLLVMTarget
          (recognitionFailureArtifact bundle)
    in action bundle artifact

unique :: [a] -> Maybe a
unique values = case values of
  [value] -> Just value
  _ -> Nothing

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
