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
    [ test "HelloPolicy Systems candidate verifies" systemsCandidateVerifies
    , test "HelloPolicy LLVM translation verifies" translationVerifies
    , test "PHIL-LLVM-CERT-012 translation certification verifies" certificationVerifies
    , test "policyContext and recognized Hello remain explicit target operands" explicitSubjects
    , test "HelloPolicy validator has exact operands and opaque reason slot" exactValidator
    , test "rejected reason reaches exact fatal runtime effect" exactFailureEffect
    , test "HelloPolicy ABI declarations are exact" exactRenderedABI
    , test "HelloPolicy reason remains opaque and off-wire" reasonRemainsOpaque
    , test "canonical HelloPolicy target has no generic or poison residue" noHelloPolicyResidue
    , test "wrong fatal-effect transport is rejected" wrongFailureTransportRejects
    , test "wrong rejected reason binding is rejected" wrongReasonBindingRejects
    ]
  if and results then pure () else exitFailure

systemsCandidateVerifies :: Bool
systemsCandidateVerifies = case phase0HelloPolicyValidationBundle of
  Right bundle -> verifyHelloPolicyValidationBundle bundle == Right ()
  Left _ -> False

translationVerifies :: Bool
translationVerifies = withBundle $ \bundle ->
  let artifact = lowerSystemsHelloPolicyValidation
        phase0HelloPolicyValidationLLVMTarget
        (helloPolicyValidationArtifact bundle)
  in verifyHelloPolicyValidationTranslation bundle artifact == Right ()

certificationVerifies :: Bool
certificationVerifies =
  verifyPhase0HelloPolicyValidationLLVMCertification == Right ()

explicitSubjects :: Bool
explicitSubjects = withLLVM $ \bundle artifact ->
  let witness = helloPolicyValidationWitness bundle
      program = systemsArtifactProgram (helloPolicyValidationArtifact bundle)
      moduleValue = llvmArtifactModule artifact
  in doBool $ do
      systemsFunction <- Map.lookup
        (helloPolicyServerFunction witness)
        (systemsProgramFunctions program)
      policyValue <- Map.lookup
        (helloPolicyPolicyContext witness)
        (systemsFunctionValues systemsFunction)
      helloValue <- Map.lookup
        (helloPolicyHelloRecord witness)
        (systemsFunctionValues systemsFunction)
      llvmFunction <- Map.lookup
        (helloPolicyServerFunction witness)
        (llvmFunctions moduleValue)
      let policyParameter = LLVMParameter
            (unValueId (helloPolicyPolicyContext witness))
            LLVMPointerParameter
      pure
        ( systemsValueRole policyValue == RuntimeInput "PolicyContext"
        && systemsValueRole helloValue == RuntimeRecord "Hello"
        && policyParameter `elem` llvmFunctionParameters llvmFunction
        )

exactValidator :: Bool
exactValidator = withLLVM $ \bundle artifact ->
  let witness = helloPolicyValidationWitness bundle
      moduleValue = llvmArtifactModule artifact
      commitId = LLVMBlockId (unBlockId (helloPolicyCommitBlock witness))
  in doBool $ do
      server <- Map.lookup
        (helloPolicyServerFunction witness)
        (llvmFunctions moduleValue)
      commitBlock <- Map.lookup commitId (llvmFunctionBlocks server)
      pure $ case llvmBlockTerminator commitBlock of
        LLVMHelloPolicyValidate site policyContext helloRecord reason accepted rejected ->
          runtimeSiteKind site == ValidationBoundary "HelloPolicy"
            && policyContext == unValueId (helloPolicyPolicyContext witness)
            && helloRecord == unValueId (helloPolicyHelloRecord witness)
            && reason == unValueId (helloPolicyRejectReason witness)
            && accepted == LLVMBlockId (unBlockId (helloPolicyAcceptedTarget witness))
            && rejected == LLVMBlockId (unBlockId (helloPolicyRejectedTarget witness))
        _ -> False

exactFailureEffect :: Bool
exactFailureEffect = withLLVM $ \bundle artifact ->
  let witness = helloPolicyValidationWitness bundle
      moduleValue = llvmArtifactModule artifact
      failureId = LLVMBlockId (unBlockId (helloPolicyRejectedTarget witness))
      reason = unValueId (helloPolicyRejectReason witness)
      transport = unValueId (helloPolicyServerTransport witness)
  in doBool $ do
      server <- Map.lookup
        (helloPolicyServerFunction witness)
        (llvmFunctions moduleValue)
      failureBlock <- Map.lookup failureId (llvmFunctionBlocks server)
      pure
        ( llvmBlockOps failureBlock ==
            [ LLVMHelloPolicyValidationReasonBinding reason
            , LLVMHelloPolicyFailure transport reason
            ]
        && llvmBlockTerminator failureBlock ==
            LLVMReturn ("fatal:" <> helloPolicyFailureClass witness)
        )

exactRenderedABI :: Bool
exactRenderedABI = withLLVM $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in all (`Text.isInfixOf` rendered)
      [ "declare i1 @phil_runtime_validate_hello_policy(ptr, ptr, ptr)"
      , "declare void @phil_runtime_fail_hello_policy(ptr, ptr)"
      , "alloca ptr"
      , "call void @phil_runtime_fail_hello_policy(ptr %server_transport, ptr %server_hello_reject_reason)"
      ]

reasonRemainsOpaque :: Bool
reasonRemainsOpaque = withLLVM $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in Text.isInfixOf "load ptr, ptr %phil_hello_policy_validation_reason_slot_" rendered
      && all (not . (`Text.isInfixOf` rendered))
        [ "hello_policy_reason_code"
        , "reason-u8"
        , "wire-hello-policy"
        , "select_hello_policy_reject"
        ]

noHelloPolicyResidue :: Bool
noHelloPolicyResidue = withLLVM $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in all (not . (`Text.isInfixOf` rendered))
      [ "@phil_call_fail_validation_HelloPolicy"
      , "@phil_runtime_validate_HelloPolicy()"
      , "current_hello_policy_reason"
      , "last_hello_policy_reason"
      , "unreachable"
      ]

wrongFailureTransportRejects :: Bool
wrongFailureTransportRejects = withLLVM $ \bundle artifact ->
  let witness = helloPolicyValidationWitness bundle
      reason = unValueId (helloPolicyRejectReason witness)
      mutated = mutateFailureOps bundle artifact
        [ LLVMHelloPolicyValidationReasonBinding reason
        , LLVMHelloPolicyFailure "client.transport" reason
        ]
  in case verifyHelloPolicyValidationLLVMWitness bundle mutated of
      Left HelloPolicyValidationLLVMFailureMismatch {} -> True
      _ -> False

wrongReasonBindingRejects :: Bool
wrongReasonBindingRejects = withLLVM $ \bundle artifact ->
  let witness = helloPolicyValidationWitness bundle
      transport = unValueId (helloPolicyServerTransport witness)
      reason = unValueId (helloPolicyRejectReason witness)
      mutated = mutateFailureOps bundle artifact
        [ LLVMHelloPolicyValidationReasonBinding "wrong.reason"
        , LLVMHelloPolicyFailure transport reason
        ]
  in case verifyHelloPolicyValidationLLVMWitness bundle mutated of
      Left HelloPolicyValidationLLVMFailureMismatch {} -> True
      _ -> False

mutateFailureOps
  :: HelloPolicyValidationBundle
  -> LLVMArtifact
  -> [LLVMOp]
  -> LLVMArtifact
mutateFailureOps bundle artifact operations = artifact
  { llvmArtifactModule = moduleValue
  , llvmArtifactText = renderLLVMModule moduleValue
  }
  where
    witness = helloPolicyValidationWitness bundle
    failureId = LLVMBlockId (unBlockId (helloPolicyRejectedTarget witness))
    module0 = llvmArtifactModule artifact
    moduleValue = module0
      { llvmFunctions = Map.adjust
          (\functionValue -> functionValue
            { llvmFunctionBlocks = Map.adjust
                (\blockValue -> blockValue { llvmBlockOps = operations })
                failureId
                (llvmFunctionBlocks functionValue)
            })
          (helloPolicyServerFunction witness)
          (llvmFunctions module0)
      }

withBundle :: (HelloPolicyValidationBundle -> Bool) -> Bool
withBundle action = case phase0HelloPolicyValidationBundle of
  Left _ -> False
  Right bundle -> action bundle

withLLVM
  :: (HelloPolicyValidationBundle -> LLVMArtifact -> Bool)
  -> Bool
withLLVM action = case phase0HelloPolicyValidationBundle of
  Left _ -> False
  Right bundle -> action bundle (lowerSystemsHelloPolicyValidation
    phase0HelloPolicyValidationLLVMTarget
    (helloPolicyValidationArtifact bundle))

doBool :: Maybe Bool -> Bool
doBool = maybe False id

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
