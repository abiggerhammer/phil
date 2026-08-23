{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "exact-send Systems candidate verifies" systemsCandidateVerifies
    , test "exact-send LLVM translation verifies" translationVerifies
    , test "PHIL-LLVM-CERT-013 translation certification verifies" certificationVerifies
    , test "UploadClient ABI carries transport then payload owner" exactClientParameters
    , test "send_exact lowers source payload to exact owner handle" exactSendOperation
    , test "exact-send runtime declaration is physical" exactRenderedABI
    , test "canonical exact-send target has no generic residue" noExactSendResidue
    ]
  if and results then pure () else exitFailure

systemsCandidateVerifies :: Bool
systemsCandidateVerifies = case phase0HelloPolicyValidationBundle of
  Right bundle -> verifyHelloPolicyValidationBundle bundle == Right ()
  Left _ -> False

translationVerifies :: Bool
translationVerifies = withLLVM $ \bundle artifact ->
  verifyExactSendTranslation bundle artifact == Right ()

certificationVerifies :: Bool
certificationVerifies = verifyPhase0ExactSendLLVMCertification == Right ()

exactClientParameters :: Bool
exactClientParameters = withLLVM $ \_ artifact ->
  doBool $ do
    client <- Map.lookup "UploadClient" (llvmFunctions (llvmArtifactModule artifact))
    pure (llvmFunctionParameters client ==
      [ LLVMParameter "client.transport" LLVMPointerParameter
      , LLVMParameter "client.payload.owner" LLVMPointerParameter
      ])

exactSendOperation :: Bool
exactSendOperation = withLLVM $ \bundle artifact ->
  let program = systemsArtifactProgram (helloPolicyValidationArtifact bundle)
      moduleValue = llvmArtifactModule artifact
  in doBool $ do
      systemsClient <- Map.lookup "UploadClient" (systemsProgramFunctions program)
      sourceBlock <- Map.lookup (BlockId "client.payload") (systemsFunctionBlocks systemsClient)
      site <- case
        [ candidate
        | OpRuntimeCall "send_exact"
            [ValueId "client.transport", ValueId "client.payload"] [] (Just candidate) _ <-
            systemsBlockOps sourceBlock
        , runtimeSiteKind candidate == ExactSendBoundary
        ] of
          [candidate] -> Just candidate
          _ -> Nothing
      client <- Map.lookup "UploadClient" (llvmFunctions moduleValue)
      blockValue <- Map.lookup (LLVMBlockId "client.payload") (llvmFunctionBlocks client)
      pure (LLVMExactSend site "client.transport" "client.payload.owner" `elem` llvmBlockOps blockValue)

exactRenderedABI :: Bool
exactRenderedABI = withLLVM $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in all (`Text.isInfixOf` rendered)
      [ "declare void @phil_runtime_send_exact(ptr, ptr)"
      , "call void @phil_runtime_send_exact(ptr %client_transport, ptr %client_payload_owner)"
      ]

noExactSendResidue :: Bool
noExactSendResidue = withLLVM $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in all (not . (`Text.isInfixOf` rendered))
      [ "declare i1 @phil_runtime_send_exact()"
      , "@phil_call_send_exact"
      , "current_payload"
      , "current_transport"
      ]

withLLVM
  :: (HelloPolicyValidationBundle -> LLVMArtifact -> Bool)
  -> Bool
withLLVM action = case phase0HelloPolicyValidationBundle of
  Left _ -> False
  Right bundle -> action bundle (lowerSystemsExactSend
    phase0ExactSendLLVMTarget
    (helloPolicyValidationArtifact bundle))

doBool :: Maybe Bool -> Bool
doBool = maybe False id

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
