{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.LLVM.HelloPolicyValidation
import Phil.LLVM.HelloPolicyValidationCertification
import Phil.LLVM.IR
import Phil.Systems.HelloPolicyValidation
import Phil.Systems.IR
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "Systems HelloPolicy candidate verifies" systemsCandidateVerifies
    , test "LLVM HelloPolicy translation verifies" llvmCandidateVerifies
    , test "translation-only CERT-012 base verifies" translationCertificationVerifies
    , test "Systems validator uses exact policyContext/Hello operands and retained site" exactSystemsValidator
    , test "Systems rejected reason flows exactly once into fatal validation effect" exactSystemsFailureFlow
    , test "extra HelloPolicy reason use is rejected" extraReasonUseRejects
    , test "produced policyContext is rejected" producedPolicyContextRejects
    , test "missing rejected payload binding is rejected" missingRejectedBindingRejects
    , test "LLVM validator and opaque reason/failure shape are exact" exactLLVMShape
    , test "LLVM failure reason identity drift is rejected" wrongLLVMFailureReasonRejects
    , test "LLVM ambient HelloPolicy state marker is rejected" ambientLLVMStateRejects
    ]
  if and results then pure () else exitFailure

systemsCandidateVerifies :: Bool
systemsCandidateVerifies = withBundle $ \bundle ->
  verifyHelloPolicyValidationBundle bundle == Right ()

llvmCandidateVerifies :: Bool
llvmCandidateVerifies = withLLVM $ \bundle artifact ->
  verifyHelloPolicyValidationTranslation bundle artifact == Right ()

translationCertificationVerifies :: Bool
translationCertificationVerifies =
  verifyPhase0HelloPolicyValidationLLVMCertification == Right ()

exactSystemsValidator :: Bool
exactSystemsValidator = withBundle $ \bundle ->
  let witness = helloPolicyValidationWitness bundle
  in case lookupSystemsBlock bundle
      (helloPolicyServerFunction witness)
      (helloPolicyCommitBlock witness) of
      Nothing -> False
      Just blockValue -> case systemsBlockTerminator blockValue of
        TermRuntimeChoice name inputs (Just site) arms ->
          name == helloPolicyRuntimeChoiceName witness
            && inputs == [helloPolicyPolicyContext witness, helloPolicyHelloRecord witness]
            && runtimeSiteKind site == ValidationBoundary "HelloPolicy"
            && Map.lookup (helloPolicyAcceptedArm witness) arms
                == Just (SystemsRuntimeChoiceArm Nothing (helloPolicyAcceptedTarget witness))
            && Map.lookup (helloPolicyRejectedArm witness) arms
                == Just (SystemsRuntimeChoiceArm
                    (Just (helloPolicyRejectReason witness))
                    (helloPolicyRejectedTarget witness))
            && Map.size arms == 2
        _ -> False

exactSystemsFailureFlow :: Bool
exactSystemsFailureFlow = withBundle $ \bundle ->
  let witness = helloPolicyValidationWitness bundle
  in case lookupSystemsBlock bundle
      (helloPolicyServerFunction witness)
      (helloPolicyRejectedTarget witness) of
      Nothing -> False
      Just blockValue ->
        systemsBlockOps blockValue ==
          [ OpRuntimeCall
              (helloPolicyFailureCall witness)
              [helloPolicyServerTransport witness, helloPolicyRejectReason witness]
              []
              Nothing
              (helloPolicyLoweringDecision witness)
          ]
          && systemsBlockTerminator blockValue
              == TermFatal (helloPolicyFailureClass witness)

extraReasonUseRejects :: Bool
extraReasonUseRejects = withBundle $ \bundle ->
  let witness = helloPolicyValidationWitness bundle
      mutated = mapSystemsBlock bundle
        (helloPolicyServerFunction witness)
        (helloPolicyAcceptedTarget witness) $ \blockValue ->
          blockValue
            { systemsBlockOps = systemsBlockOps blockValue <>
                [ OpRuntimeCall
                    "mutation-observe-hello-policy-reason"
                    [helloPolicyRejectReason witness]
                    []
                    Nothing
                    (helloPolicyLoweringDecision witness)
                ]
            }
  in case verifyHelloPolicyValidationWitness mutated witness of
      Left HelloPolicyReasonUseMismatch {} -> True
      _ -> False

producedPolicyContextRejects :: Bool
producedPolicyContextRejects = withBundle $ \bundle ->
  let witness = helloPolicyValidationWitness bundle
      mutated = mapSystemsBlock bundle
        (helloPolicyServerFunction witness)
        (helloPolicyCommitBlock witness) $ \blockValue ->
          blockValue
            { systemsBlockOps = OpRuntimeCall
                "mutation-policy-producer"
                []
                [helloPolicyPolicyContext witness]
                Nothing
                (helloPolicyLoweringDecision witness)
                : systemsBlockOps blockValue
            }
  in case verifyHelloPolicyValidationWitness mutated witness of
      Left HelloPolicyInputHasProducer {} -> True
      _ -> False

missingRejectedBindingRejects :: Bool
missingRejectedBindingRejects = withBundle $ \bundle ->
  let witness = helloPolicyValidationWitness bundle
      mutated = mapSystemsBlock bundle
        (helloPolicyServerFunction witness)
        (helloPolicyCommitBlock witness) $ \blockValue ->
          blockValue { systemsBlockTerminator = case systemsBlockTerminator blockValue of
            TermRuntimeChoice name inputs site arms ->
              TermRuntimeChoice name inputs site $
                Map.adjust
                  (\arm -> arm { runtimeChoiceArmPayloadBinding = Nothing })
                  (helloPolicyRejectedArm witness)
                  arms
            other -> other }
  in case verifyHelloPolicyValidationWitness mutated witness of
      Left _ -> True
      Right () -> False

exactLLVMShape :: Bool
exactLLVMShape = withLLVM $ \bundle artifact ->
  let witness = helloPolicyValidationWitness bundle
      moduleValue = llvmArtifactModule artifact
      serverName = helloPolicyServerFunction witness
      commitId = LLVMBlockId (unBlockId (helloPolicyCommitBlock witness))
      acceptedId = LLVMBlockId (unBlockId (helloPolicyAcceptedTarget witness))
      failureId = LLVMBlockId (unBlockId (helloPolicyRejectedTarget witness))
      policyContext = unValueId (helloPolicyPolicyContext witness)
      helloRecord = unValueId (helloPolicyHelloRecord witness)
      reason = unValueId (helloPolicyRejectReason witness)
      transport = unValueId (helloPolicyServerTransport witness)
  in case Map.lookup serverName (llvmFunctions moduleValue) of
      Nothing -> False
      Just server -> case
          ( Map.lookup commitId (llvmFunctionBlocks server)
          , Map.lookup failureId (llvmFunctionBlocks server)
          ) of
          (Just commitBlock, Just failureBlock) ->
            let validatorOk = case llvmBlockTerminator commitBlock of
                  LLVMHelloPolicyValidate site policy hello outReason accepted rejected ->
                    runtimeSiteKind site == ValidationBoundary "HelloPolicy"
                      && policy == policyContext
                      && hello == helloRecord
                      && outReason == reason
                      && accepted == acceptedId
                      && rejected == failureId
                  _ -> False
            in validatorOk
                && llvmBlockOps failureBlock ==
                    [ LLVMHelloPolicyValidationReasonBinding reason
                    , LLVMHelloPolicyFailure transport reason
                    ]
                && llvmBlockTerminator failureBlock
                    == LLVMReturn ("fatal:" <> helloPolicyFailureClass witness)
          _ -> False

wrongLLVMFailureReasonRejects :: Bool
wrongLLVMFailureReasonRejects = withLLVM $ \bundle artifact ->
  let witness = helloPolicyValidationWitness bundle
      serverName = helloPolicyServerFunction witness
      failureId = LLVMBlockId (unBlockId (helloPolicyRejectedTarget witness))
      transport = unValueId (helloPolicyServerTransport witness)
      reason = unValueId (helloPolicyRejectReason witness)
      mutated = mapLLVMBlock artifact serverName failureId $ \blockValue ->
        blockValue
          { llvmBlockOps =
              [ LLVMHelloPolicyValidationReasonBinding reason
              , LLVMHelloPolicyFailure transport "mutation.other_reason"
              ]
          }
  in case verifyHelloPolicyValidationLLVMWitness bundle mutated of
      Left HelloPolicyValidationLLVMFailureMismatch {} -> True
      _ -> False

ambientLLVMStateRejects :: Bool
ambientLLVMStateRejects = withLLVM $ \bundle artifact ->
  let mutated = artifact
        { llvmArtifactText = llvmArtifactText artifact <> "\n; current_hello\n" }
  in case verifyHelloPolicyValidationLLVMWitness bundle mutated of
      Left HelloPolicyValidationLLVMAmbientStateDetected {} -> True
      _ -> False

lookupSystemsBlock
  :: HelloPolicyValidationBundle
  -> Text.Text
  -> BlockId
  -> Maybe SystemsBlock
lookupSystemsBlock bundle functionName blockId = do
  function <- Map.lookup functionName $
    systemsProgramFunctions (systemsArtifactProgram (helloPolicyValidationArtifact bundle))
  Map.lookup blockId (systemsFunctionBlocks function)

mapSystemsBlock
  :: HelloPolicyValidationBundle
  -> Text.Text
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapSystemsBlock bundle functionName blockId transform =
  let artifact = helloPolicyValidationArtifact bundle
      program = systemsArtifactProgram artifact
      functions' = Map.adjust
        (\function -> function
          { systemsFunctionBlocks =
              Map.adjust transform blockId (systemsFunctionBlocks function)
          })
        functionName
        (systemsProgramFunctions program)
  in artifact
      { systemsArtifactProgram = program { systemsProgramFunctions = functions' } }

mapLLVMBlock
  :: LLVMArtifact
  -> Text.Text
  -> LLVMBlockId
  -> (LLVMBlock -> LLVMBlock)
  -> LLVMArtifact
mapLLVMBlock artifact functionName blockId transform =
  let moduleValue = llvmArtifactModule artifact
      functions' = Map.adjust
        (\function -> function
          { llvmFunctionBlocks =
              Map.adjust transform blockId (llvmFunctionBlocks function)
          })
        functionName
        (llvmFunctions moduleValue)
      module' = moduleValue { llvmFunctions = functions' }
  in artifact { llvmArtifactModule = module' }

withBundle :: (HelloPolicyValidationBundle -> Bool) -> Bool
withBundle action = case phase0HelloPolicyValidationBundle of
  Left _ -> False
  Right bundle -> action bundle

withLLVM :: (HelloPolicyValidationBundle -> LLVMArtifact -> Bool) -> Bool
withLLVM action = case phase0HelloPolicyValidationBundle of
  Left _ -> False
  Right bundle ->
    action bundle (lowerSystemsHelloPolicyValidation
      phase0HelloPolicyValidationLLVMTarget
      (helloPolicyValidationArtifact bundle))

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
