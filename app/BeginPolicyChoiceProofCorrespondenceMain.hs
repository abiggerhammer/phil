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
    [ test "Systems BeginPolicy candidate verifies" systemsCandidateVerifies
    , test "LLVM BeginPolicy translation verifies" llvmCandidateVerifies
    , test "translation-only CERT-011 base verifies" translationCertificationVerifies
    , test "Systems validator uses exact policyContext/Begin operands and retained site" exactSystemsValidator
    , test "Systems server select multiplicity and payloads are exact" exactSystemsServerSelects
    , test "Systems client offer is exact with distinct reject reason" exactSystemsClientOffer
    , test "LLVM validator/select/receiver shape is exact" exactLLVMShape
    , test "extra server reason use invalidates quotient" extraServerReasonUseRejects
    , test "client reason observation invalidates quotient" clientReasonUseRejects
    , test "produced policyContext is rejected" producedPolicyContextRejects
    , test "missing rejected payload binding is rejected" missingRejectedBindingRejects
    ]
  if and results then pure () else exitFailure

systemsCandidateVerifies :: Bool
systemsCandidateVerifies = withBundle $ \bundle ->
  verifyBeginPolicySessionChoiceBundle bundle == Right ()

llvmCandidateVerifies :: Bool
llvmCandidateVerifies = withLLVM $ \bundle artifact ->
  verifyBeginPolicyChoiceTranslation bundle artifact == Right ()

translationCertificationVerifies :: Bool
translationCertificationVerifies =
  verifyPhase0BeginPolicyChoiceLLVMCertification == Right ()

exactSystemsValidator :: Bool
exactSystemsValidator = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
  in case lookupSystemsBlock bundle (beginPolicyServerFunction witness) (beginPolicyCommitBlock witness) of
      Nothing -> False
      Just blockValue -> case systemsBlockTerminator blockValue of
        TermRuntimeChoice name inputs (Just site) arms ->
          name == beginPolicyRuntimeChoiceName witness
            && inputs == [beginPolicyPolicyContext witness, beginPolicyBeginRecord witness]
            && runtimeSiteKind site == ValidationBoundary "BeginPolicy"
            && Map.lookup (beginPolicyAcceptedArm witness) arms
                == Just (SystemsRuntimeChoiceArm Nothing (beginPolicyServerProceedBlock witness))
            && Map.lookup (beginPolicyRejectedArm witness) arms
                == Just (SystemsRuntimeChoiceArm
                    (Just (beginPolicyServerRejectReason witness))
                    (beginPolicyServerRejectBlock witness))
            && Map.size arms == 2
        _ -> False

exactSystemsServerSelects :: Bool
exactSystemsServerSelects = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
      rejectCount = countSystemsSelect bundle
        (beginPolicyServerRejectBlock witness)
        (beginPolicyServerTransport witness)
        (beginPolicyRejectLabel witness)
        (Just (beginPolicyServerRejectReason witness))
      proceedCount = countSystemsSelect bundle
        (beginPolicyServerProceedBlock witness)
        (beginPolicyServerTransport witness)
        (beginPolicyProceedLabel witness)
        Nothing
  in rejectCount == 1 && proceedCount == 1

exactSystemsClientOffer :: Bool
exactSystemsClientOffer = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
  in case lookupSystemsBlock bundle (beginPolicyClientFunction witness) (beginPolicyClientOfferBlock witness) of
      Nothing -> False
      Just blockValue -> case systemsBlockTerminator blockValue of
        TermSessionOffer transport arms ->
          transport == beginPolicyClientTransport witness
            && Map.lookup (beginPolicyRejectLabel witness) arms
                == Just (SystemsChoiceArm
                    (Just (beginPolicyClientRejectReason witness))
                    (beginPolicyClientRejectTarget witness))
            && Map.lookup (beginPolicyProceedLabel witness) arms
                == Just (SystemsChoiceArm Nothing (beginPolicyClientProceedTarget witness))
            && beginPolicyClientRejectReason witness /= beginPolicyServerRejectReason witness
            && Map.size arms == 2
        _ -> False

exactLLVMShape :: Bool
exactLLVMShape = withLLVM $ \bundle artifact ->
  let witness = beginPolicySessionChoiceWitness bundle
      moduleValue = llvmArtifactModule artifact
      serverName = beginPolicyServerFunction witness
      clientName = beginPolicyClientFunction witness
      commitId = LLVMBlockId (unBlockId (beginPolicyCommitBlock witness))
      rejectId = LLVMBlockId (unBlockId (beginPolicyServerRejectBlock witness))
      proceedId = LLVMBlockId (unBlockId (beginPolicyServerProceedBlock witness))
      offerId = LLVMBlockId (unBlockId (beginPolicyClientOfferBlock witness))
      clientRejectId = LLVMBlockId (unBlockId (beginPolicyClientRejectTarget witness))
      clientProceedId = LLVMBlockId (unBlockId (beginPolicyClientProceedTarget witness))
  in case (Map.lookup serverName (llvmFunctions moduleValue), Map.lookup clientName (llvmFunctions moduleValue)) of
      (Just server, Just client) ->
        case ( Map.lookup commitId (llvmFunctionBlocks server)
             , Map.lookup rejectId (llvmFunctionBlocks server)
             , Map.lookup proceedId (llvmFunctionBlocks server)
             , Map.lookup offerId (llvmFunctionBlocks client)
             , Map.lookup clientRejectId (llvmFunctionBlocks client)
             ) of
          (Just commitBlock, Just rejectBlock, Just proceedBlock, Just offerBlock, Just clientRejectBlock) ->
            let validatorOk = case llvmBlockTerminator commitBlock of
                  LLVMBeginPolicyValidate site policy beginRecord reason accepted rejected ->
                    runtimeSiteKind site == ValidationBoundary "BeginPolicy"
                      && policy == unValueId (beginPolicyPolicyContext witness)
                      && beginRecord == unValueId (beginPolicyBeginRecord witness)
                      && reason == unValueId (beginPolicyServerRejectReason witness)
                      && accepted == proceedId
                      && rejected == rejectId
                  _ -> False
                rejectOps = llvmBlockOps rejectBlock
                proceedOps = llvmBlockOps proceedBlock
                offerOk = llvmBlockTerminator offerBlock == LLVMBeginPolicyChoiceOffer
                  (unValueId (beginPolicyClientTransport witness))
                  (unValueId (beginPolicyClientRejectReason witness))
                  clientProceedId
                  clientRejectId
            in validatorOk
                && countEq (LLVMBeginPolicyValidationReasonBinding
                      (unValueId (beginPolicyServerRejectReason witness))) rejectOps == 1
                && countEq (LLVMBeginPolicyRejectSelect
                      (unValueId (beginPolicyServerTransport witness))
                      (unValueId (beginPolicyServerRejectReason witness))) rejectOps == 1
                && countEq (LLVMBeginPolicyProceedSelect
                      (unValueId (beginPolicyServerTransport witness))) proceedOps == 1
                && offerOk
                && countEq (LLVMBeginPolicyChoiceReasonBinding
                      (unValueId (beginPolicyClientRejectReason witness)))
                      (llvmBlockOps clientRejectBlock) == 1
          _ -> False
      _ -> False

extraServerReasonUseRejects :: Bool
extraServerReasonUseRejects = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
      mutated = addReasonUse bundle
        (beginPolicyServerFunction witness)
        (beginPolicyServerRejectBlock witness)
        (beginPolicyServerTransport witness)
        (beginPolicyServerRejectReason witness)
  in case verifyBeginPolicyReasonUseShape mutated of
      Left BeginPolicyChoiceLLVMReasonUseMismatch {} -> True
      _ -> False

clientReasonUseRejects :: Bool
clientReasonUseRejects = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
      mutated = addReasonUse bundle
        (beginPolicyClientFunction witness)
        (beginPolicyClientRejectTarget witness)
        (beginPolicyClientTransport witness)
        (beginPolicyClientRejectReason witness)
  in case verifyBeginPolicyReasonUseShape mutated of
      Left BeginPolicyChoiceLLVMReasonUseMismatch {} -> True
      _ -> False

producedPolicyContextRejects :: Bool
producedPolicyContextRejects = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
      mutated = mapSystemsBlock bundle
        (beginPolicyServerFunction witness)
        (beginPolicyCommitBlock witness) $ \blockValue ->
          blockValue
            { systemsBlockOps = OpRuntimeCall
                { runtimeCallName = "mutation-policy-producer"
                , runtimeCallInputs = []
                , runtimeCallOutputs = [beginPolicyPolicyContext witness]
                , runtimeCallSite = Nothing
                , runtimeCallDecision = beginPolicyLoweringDecision witness
                } : systemsBlockOps blockValue
            }
  in case verifyBeginPolicySessionChoiceWitness mutated witness of
      Left BeginPolicyInputHasProducer {} -> True
      _ -> False

missingRejectedBindingRejects :: Bool
missingRejectedBindingRejects = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
      mutated = mapSystemsBlock bundle
        (beginPolicyServerFunction witness)
        (beginPolicyCommitBlock witness) $ \blockValue ->
          blockValue { systemsBlockTerminator = case systemsBlockTerminator blockValue of
            TermRuntimeChoice name inputs site arms ->
              TermRuntimeChoice name inputs site $
                Map.adjust
                  (\arm -> arm { runtimeChoiceArmPayloadBinding = Nothing })
                  (beginPolicyRejectedArm witness)
                  arms
            other -> other }
  in case verifyBeginPolicySessionChoiceWitness mutated witness of
      Left _ -> True
      Right () -> False

countSystemsSelect
  :: BeginPolicySessionChoiceBundle
  -> BlockId
  -> ValueId
  -> Text.Text
  -> Maybe ValueId
  -> Int
countSystemsSelect bundle blockId transport label payload =
  case lookupSystemsBlock bundle "UploadServer" blockId of
    Nothing -> 0
    Just blockValue -> length (filter matches (systemsBlockOps blockValue))
  where
    witness = beginPolicySessionChoiceWitness bundle
    matches operation = case operation of
      OpSessionSelect actualTransport actualLabel actualPayload decision ->
        actualTransport == transport
          && actualLabel == label
          && actualPayload == payload
          && decision == beginPolicyLoweringDecision witness
      _ -> False

lookupSystemsBlock
  :: BeginPolicySessionChoiceBundle
  -> Text.Text
  -> BlockId
  -> Maybe SystemsBlock
lookupSystemsBlock bundle functionName blockId = do
  function <- Map.lookup functionName $
    systemsProgramFunctions (systemsArtifactProgram (beginPolicySessionChoiceArtifact bundle))
  Map.lookup blockId (systemsFunctionBlocks function)

mapSystemsBlock
  :: BeginPolicySessionChoiceBundle
  -> Text.Text
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapSystemsBlock bundle functionName blockId transform =
  let artifact = beginPolicySessionChoiceArtifact bundle
      program = systemsArtifactProgram artifact
      functions' = Map.adjust
        (\function -> function
          { systemsFunctionBlocks = Map.adjust transform blockId (systemsFunctionBlocks function) })
        functionName
        (systemsProgramFunctions program)
  in artifact
      { systemsArtifactProgram = program { systemsProgramFunctions = functions' } }

addReasonUse
  :: BeginPolicySessionChoiceBundle
  -> Text.Text
  -> BlockId
  -> ValueId
  -> ValueId
  -> BeginPolicySessionChoiceBundle
addReasonUse bundle functionName blockId transport reason =
  bundle { beginPolicySessionChoiceArtifact = artifact' }
  where
    witness = beginPolicySessionChoiceWitness bundle
    artifact' = mapSystemsBlock bundle functionName blockId $ \blockValue ->
      blockValue
        { systemsBlockOps = systemsBlockOps blockValue <>
            [ OpSessionSelect transport "mutation-observe-reason" (Just reason)
                (beginPolicyLoweringDecision witness) ]
        }

countEq :: Eq a => a -> [a] -> Int
countEq value = length . filter (== value)

withBundle :: (BeginPolicySessionChoiceBundle -> Bool) -> Bool
withBundle action = case phase0BeginPolicySessionChoiceBundle of
  Left _ -> False
  Right bundle -> action bundle

withLLVM :: (BeginPolicySessionChoiceBundle -> LLVMArtifact -> Bool) -> Bool
withLLVM action = case phase0BeginPolicySessionChoiceBundle of
  Left _ -> False
  Right bundle ->
    action bundle (lowerSystemsBeginPolicyChoice
      phase0BeginPolicyChoiceLLVMTarget
      (beginPolicySessionChoiceArtifact bundle))

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
