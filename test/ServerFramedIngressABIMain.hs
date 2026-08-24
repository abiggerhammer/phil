{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.LLVM
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "server framed-ingress translation verifies" candidateVerifies
    , test "Hello frame receive uses exact transport and explicit outputs" helloFrameExplicit
    , test "recognition binds exact record and failure reason" recognitionDetailExplicit
    , test "recognition failure forwards reason then destroys exact pending/frame" failureFlowExplicit
    , test "legacy nullary ingress primitives are absent" legacyIngressAbsent
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies = verifyPhase0ServerFramedIngressLLVM == Right ()

helloFrameExplicit :: Bool
helloFrameExplicit = withCandidate $ \artifact -> doBool $ do
  server <- Map.lookup "UploadServer" (llvmFunctions (llvmArtifactModule artifact))
  entry <- Map.lookup (LLVMBlockId "server.entry") (llvmFunctionBlocks server)
  pure $
    LLVMServerReceiveFrame
      "Hello"
      "server.pending.hello"
      "server.frame.hello"
      "server.transport" `elem` llvmBlockOps entry
    && LLVMServerBorrowFrameView
      "Hello"
      "server.raw.hello"
      "server.frame.hello" `elem` llvmBlockOps entry

recognitionDetailExplicit :: Bool
recognitionDetailExplicit = withCandidate $ \artifact -> doBool $ do
  server <- Map.lookup "UploadServer" (llvmFunctions (llvmArtifactModule artifact))
  entry <- Map.lookup (LLVMBlockId "server.entry") (llvmFunctionBlocks server)
  version <- Map.lookup (LLVMBlockId "server.version") (llvmFunctionBlocks server)
  pure $
    case (llvmBlockTerminator entry, llvmBlockTerminator version) of
      ( LLVMRecognizeRecordDetailed _ "Hello" pendingH rawH recordH reasonH _ _
        , LLVMRecognizeRecordDetailed _ "Begin" pendingB rawB recordB reasonB _ _
        ) ->
          pendingH == "server.pending.hello"
            && rawH == "server.raw.hello"
            && recordH == "server.hello"
            && reasonH == "server.hello_recognition_reason"
            && pendingB == "server.pending.begin"
            && rawB == "server.raw.begin"
            && recordB == "server.begin"
            && reasonB == "server.begin_recognition_reason"
      _ -> False

failureFlowExplicit :: Bool
failureFlowExplicit = withCandidate $ \artifact -> doBool $ do
  server <- Map.lookup "UploadServer" (llvmFunctions (llvmArtifactModule artifact))
  helloFailure <- Map.lookup
    (LLVMBlockId "server.hello.recognition_failure")
    (llvmFunctionBlocks server)
  beginFailure <- Map.lookup
    (LLVMBlockId "server.begin.recognition_failure")
    (llvmFunctionBlocks server)
  pure $
    llvmBlockOps helloFailure ==
      [ LLVMServerFailRecognition
          "Hello" "server.pending.hello" "server.hello_recognition_reason"
      , LLVMServerDestroyPending
          "Hello" "server.pending.hello" "server.frame.hello"
      ]
    && llvmBlockOps beginFailure ==
      [ LLVMServerFailRecognition
          "Begin" "server.pending.begin" "server.begin_recognition_reason"
      , LLVMServerDestroyPending
          "Begin" "server.pending.begin" "server.frame.begin"
      ]

legacyIngressAbsent :: Bool
legacyIngressAbsent = withCandidate $ \artifact ->
  let rendered = llvmArtifactText artifact
  in all (not . (`Text.isInfixOf` rendered))
      [ "@phil_call_receive_frame_Hello()"
      , "@phil_call_receive_frame_Begin()"
      , "@phil_runtime_recognize_Hello()"
      , "@phil_runtime_recognize_Begin()"
      , "@phil_call_materialize_recognition_failure_reason_Hello()"
      , "@phil_call_materialize_recognition_failure_reason_Begin()"
      , "@phil_call_fail_recognition_Hello()"
      , "@phil_call_fail_recognition_Begin()"
      ]

withCandidate :: (LLVMArtifact -> Bool) -> Bool
withCandidate action = case phase0ServerFramedIngressLLVMArtifact of
  Left _ -> False
  Right artifact -> action artifact

doBool :: Maybe Bool -> Bool
doBool = maybe False id

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
