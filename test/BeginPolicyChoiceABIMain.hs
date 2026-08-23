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
    [ test "BeginPolicy Systems candidate verifies" systemsCandidateVerifies
    , test "BeginPolicy LLVM translation verifies" translationVerifies
    , test "PHIL-LLVM-CERT-011 translation certification verifies" certificationVerifies
    , test "policyContext is explicit runtime input and target parameter" explicitPolicyContext
    , test "BeginPolicy validator has exact operands and reason slot" exactValidator
    , test "server reject/proceed selectors are exact" exactServerSelectors
    , test "client physical offer binds rejection reason only on reject" exactClientOffer
    , test "wire ABI declarations are exact" exactRenderedABI
    , test "canonical BeginPolicy target has no generic or poison residue" noBeginPolicyResidue
    ]
  if and results then pure () else exitFailure

systemsCandidateVerifies :: Bool
systemsCandidateVerifies = case phase0BeginPolicySessionChoiceBundle of
  Right bundle -> verifyBeginPolicySessionChoiceBundle bundle == Right ()
  Left _ -> False

translationVerifies :: Bool
translationVerifies = withBundle $ \bundle ->
  let artifact = lowerSystemsBeginPolicyChoice
        phase0BeginPolicyChoiceLLVMTarget
        (beginPolicySessionChoiceArtifact bundle)
  in verifyBeginPolicyChoiceTranslation bundle artifact == Right ()

certificationVerifies :: Bool
certificationVerifies =
  verifyPhase0BeginPolicyChoiceLLVMCertification == Right ()

explicitPolicyContext :: Bool
explicitPolicyContext = withLLVM $ \bundle artifact ->
  let witness = beginPolicySessionChoiceWitness bundle
      program = systemsArtifactProgram (beginPolicySessionChoiceArtifact bundle)
      moduleValue = llvmArtifactModule artifact
  in doBool $ do
      systemsFunction <- Map.lookup
        (beginPolicyServerFunction witness)
        (systemsProgramFunctions program)
      value <- Map.lookup
        (beginPolicyPolicyContext witness)
        (systemsFunctionValues systemsFunction)
      llvmFunction <- Map.lookup
        (beginPolicyServerFunction witness)
        (llvmFunctions moduleValue)
      let parameter = LLVMParameter
            (unValueId (beginPolicyPolicyContext witness))
            LLVMPointerParameter
      pure (systemsValueRole value == RuntimeInput "PolicyContext"
        && parameter `elem` llvmFunctionParameters llvmFunction)

exactValidator :: Bool
exactValidator = withLLVM $ \bundle artifact ->
  let witness = beginPolicySessionChoiceWitness bundle
      moduleValue = llvmArtifactModule artifact
      commitId = LLVMBlockId (unBlockId (beginPolicyCommitBlock witness))
  in doBool $ do
      server <- Map.lookup
        (beginPolicyServerFunction witness)
        (llvmFunctions moduleValue)
      commitBlock <- Map.lookup commitId (llvmFunctionBlocks server)
      pure $ case llvmBlockTerminator commitBlock of
        LLVMBeginPolicyValidate site policyContext beginRecord reason accepted rejected ->
          runtimeSiteKind site == ValidationBoundary "BeginPolicy"
            && policyContext == unValueId (beginPolicyPolicyContext witness)
            && beginRecord == unValueId (beginPolicyBeginRecord witness)
            && reason == unValueId (beginPolicyServerRejectReason witness)
            && accepted == LLVMBlockId (unBlockId (beginPolicyServerProceedBlock witness))
            && rejected == LLVMBlockId (unBlockId (beginPolicyServerRejectBlock witness))
        _ -> False

exactServerSelectors :: Bool
exactServerSelectors = withLLVM $ \bundle artifact ->
  let witness = beginPolicySessionChoiceWitness bundle
      moduleValue = llvmArtifactModule artifact
      rejectId = LLVMBlockId (unBlockId (beginPolicyServerRejectBlock witness))
      proceedId = LLVMBlockId (unBlockId (beginPolicyServerProceedBlock witness))
      transport = unValueId (beginPolicyServerTransport witness)
      reason = unValueId (beginPolicyServerRejectReason witness)
  in doBool $ do
      server <- Map.lookup
        (beginPolicyServerFunction witness)
        (llvmFunctions moduleValue)
      rejectBlock <- Map.lookup rejectId (llvmFunctionBlocks server)
      proceedBlock <- Map.lookup proceedId (llvmFunctionBlocks server)
      pure
        ( LLVMBeginPolicyValidationReasonBinding reason `elem` llvmBlockOps rejectBlock
        && LLVMBeginPolicyRejectSelect transport reason `elem` llvmBlockOps rejectBlock
        && LLVMBeginPolicyProceedSelect transport `elem` llvmBlockOps proceedBlock
        )

exactClientOffer :: Bool
exactClientOffer = withLLVM $ \bundle artifact ->
  let witness = beginPolicySessionChoiceWitness bundle
      moduleValue = llvmArtifactModule artifact
      offerId = LLVMBlockId (unBlockId (beginPolicyClientOfferBlock witness))
      rejectId = LLVMBlockId (unBlockId (beginPolicyClientRejectTarget witness))
      proceedId = LLVMBlockId (unBlockId (beginPolicyClientProceedTarget witness))
      transport = unValueId (beginPolicyClientTransport witness)
      reason = unValueId (beginPolicyClientRejectReason witness)
  in doBool $ do
      client <- Map.lookup
        (beginPolicyClientFunction witness)
        (llvmFunctions moduleValue)
      offerBlock <- Map.lookup offerId (llvmFunctionBlocks client)
      rejectBlock <- Map.lookup rejectId (llvmFunctionBlocks client)
      let expectedOffer = LLVMBeginPolicyChoiceOffer
            transport reason proceedId rejectId
      pure (llvmBlockTerminator offerBlock == expectedOffer
        && LLVMBeginPolicyChoiceReasonBinding reason `elem` llvmBlockOps rejectBlock)

exactRenderedABI :: Bool
exactRenderedABI = withLLVM $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in all (`Text.isInfixOf` rendered)
      [ "declare i1 @phil_runtime_validate_begin_policy(ptr, ptr, ptr)"
      , "declare void @phil_runtime_select_begin_policy_reject(ptr, i8)"
      , "declare void @phil_runtime_select_begin_policy_proceed(ptr)"
      , "declare i1 @phil_runtime_receive_begin_policy_choice(ptr, ptr)"
      ]

noBeginPolicyResidue :: Bool
noBeginPolicyResidue = withLLVM $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in all (not . (`Text.isInfixOf` rendered))
      [ "unlowered-session-select:reject"
      , "unlowered-session-select:proceed"
      , "@phil_runtime_validate_BeginPolicy()"
      , "current_begin_policy_reason"
      , "last_begin_policy_reason"
      ]

withBundle :: (BeginPolicySessionChoiceBundle -> Bool) -> Bool
withBundle action = case phase0BeginPolicySessionChoiceBundle of
  Left _ -> False
  Right bundle -> action bundle

withLLVM
  :: (BeginPolicySessionChoiceBundle -> LLVMArtifact -> Bool)
  -> Bool
withLLVM action = case phase0BeginPolicySessionChoiceBundle of
  Left _ -> False
  Right bundle -> action bundle (lowerSystemsBeginPolicyChoice
    phase0BeginPolicyChoiceLLVMTarget
    (beginPolicySessionChoiceArtifact bundle))

doBool :: Maybe Bool -> Bool
doBool = maybe False id

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
