{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.HelloPolicyValidation
  ( HelloPolicyValidationLLVMError (..)
  , helloPolicyValidationABIDescriptor
  , phase0HelloPolicyValidationLLVMTarget
  , phase0HelloPolicyValidationLLVMArtifact
  , phase0HelloPolicyValidationLLVMVerificationContext
  , lowerSystemsHelloPolicyValidation
  , verifyHelloPolicyValidationLLVMWitness
  , verifyHelloPolicyValidationTranslation
  , verifyPhase0HelloPolicyValidationLLVM
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest)
import Phil.LLVM.BeginPolicyChoice
  ( beginPolicyChoiceABIDescriptor
  , lowerSystemsBeginPolicyChoice
  , phase0BeginPolicyChoiceLLVMTarget
  , verifyBeginPolicyChoiceLLVMWitness
  )
import Phil.LLVM.IR
import Phil.LLVM.Verify
import Phil.Systems.HelloPolicyValidation
import Phil.Systems.IR

data HelloPolicyValidationLLVMError
  = HelloPolicyValidationLLVMSystemsError HelloPolicyValidationError
  | HelloPolicyValidationLLVMVerificationError LLVMVerificationError
  | HelloPolicyValidationLLVMFunctionMissing Text
  | HelloPolicyValidationLLVMBlockMissing Text LLVMBlockId
  | HelloPolicyValidationLLVMParameterMismatch Text [LLVMParameter]
  | HelloPolicyValidationLLVMValidationMismatch Text LLVMBlockId LLVMTerminator
  | HelloPolicyValidationLLVMFailureMismatch Text LLVMBlockId [LLVMOp] LLVMTerminator
  | HelloPolicyValidationLLVMBeginPolicyRegression Text
  | HelloPolicyValidationLLVMRenderedCallMissing Text
  | HelloPolicyValidationLLVMGenericCallDetected Text
  | HelloPolicyValidationLLVMAmbientStateDetected Text
  | HelloPolicyValidationLLVMPoisonDetected Text
  | HelloPolicyValidationLLVMUnresolvedControlDetected Text LLVMBlockId
  deriving (Eq, Show)

helloPolicyValidationABIDescriptor :: Text
helloPolicyValidationABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/hello-policy-validation-v1"
  , "base-begin-policy-abi-digest=" <> unDigest (digestText beginPolicyChoiceABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0BeginPolicyChoiceLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0BeginPolicyChoiceLLVMTarget
  , "policy-context=explicit-UploadServer-ptr-parameter"
  , "policy-context-ambient-lookup=forbidden"
  , "hello-record=exact-recognized-Hello-ptr"
  , "validate=phil_runtime_validate_hello_policy(ptr,ptr,ptr)->i1"
  , "validate-arg0=exact-policy-context"
  , "validate-arg1=exact-recognized-Hello"
  , "validate-out=pointer-to-ptr-rejection-reason-slot"
  , "validate-true=accepted;reason-slot-not-observed"
  , "validate-false=rejected;reason-slot-initialized-to-nonnull-opaque-handle"
  , "validate-provider-obligation=return-true-iff-HelloPolicy-accepts;on-false-write-exact-provider-reason-handle"
  , "reason-physical-representation=opaque-provider-ptr"
  , "reason-identity=preserved-through-fatal-effect"
  , "reason-lifetime=provider-owned-and-valid-through-fail-call"
  , "reason-wire-encoding=none"
  , "fail=phil_runtime_fail_hello_policy(ptr,ptr)->void"
  , "fail-arg0=exact-server-transport"
  , "fail-arg1=exact-validator-reason-handle"
  , "fail-provider-obligation=perform-local-HelloPolicy-validation-failure-effect;component-terminates-immediately-after-call"
  , "peer-protocol-effect=none-defined-by-this-profile"
  , "outer-framing=not-defined-by-this-profile"
  , "ambient-policy-state=forbidden"
  , "ambient-hello-state=forbidden"
  , "ambient-rejection-state=forbidden"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "pointer-strengthening=none-by-default"
  ]

phase0HelloPolicyValidationLLVMTarget :: LLVMTargetProfile
phase0HelloPolicyValidationLLVMTarget = phase0BeginPolicyChoiceLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText helloPolicyValidationABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/hello-policy-validation-v1"
  }

phase0HelloPolicyValidationLLVMArtifact
  :: Either HelloPolicyValidationError LLVMArtifact
phase0HelloPolicyValidationLLVMArtifact = do
  bundle <- phase0HelloPolicyValidationBundle
  pure (lowerSystemsHelloPolicyValidation
    phase0HelloPolicyValidationLLVMTarget
    (helloPolicyValidationArtifact bundle))

lowerSystemsHelloPolicyValidation :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsHelloPolicyValidation target systemsArtifact = artifact
  where
    base = lowerSystemsBeginPolicyChoice target systemsArtifact
    witness = phase0HelloPolicyValidationWitness
    module0 = llvmArtifactModule base
    module1 = module0
      { llvmFunctions = Map.adjust rewriteServer
          (helloPolicyServerFunction witness)
          (llvmFunctions module0)
      }

    rewriteServer function = function
      { llvmFunctionBlocks = Map.adjust rewriteCommit commitBlockId $
          Map.adjust rewriteFailure failureBlockId (llvmFunctionBlocks function)
      }

    rewriteCommit blockValue =
      case helloPolicyRuntimeSite systemsArtifact witness of
        Nothing -> blockValue
        Just site -> blockValue
          { llvmBlockTerminator = LLVMHelloPolicyValidate
              site
              policyContext
              helloRecord
              reason
              acceptedBlockId
              failureBlockId
          }

    rewriteFailure blockValue = blockValue
      { llvmBlockOps =
          [ LLVMHelloPolicyValidationReasonBinding reason
          , LLVMHelloPolicyFailure serverTransport reason
          ] <> filter (not . isGenericFailure) (llvmBlockOps blockValue)
      }

    isGenericFailure operation = case operation of
      LLVMCall name -> name == helloPolicyFailureCall witness
      _ -> False

    commitBlockId = LLVMBlockId (unBlockId (helloPolicyCommitBlock witness))
    acceptedBlockId = LLVMBlockId (unBlockId (helloPolicyAcceptedTarget witness))
    failureBlockId = LLVMBlockId (unBlockId (helloPolicyRejectedTarget witness))
    policyContext = unValueId (helloPolicyPolicyContext witness)
    helloRecord = unValueId (helloPolicyHelloRecord witness)
    reason = unValueId (helloPolicyRejectReason witness)
    serverTransport = unValueId (helloPolicyServerTransport witness)

    contract0 = llvmArtifactContract base
    contract1 = contract0 { llvmContractTargetDigest = llvmModuleDigest module1 }
    artifact = base
      { llvmArtifactModule = module1
      , llvmArtifactText = renderLLVMModule module1
      , llvmArtifactContract = contract1
      }

phase0HelloPolicyValidationLLVMVerificationContext
  :: HelloPolicyValidationBundle
  -> LLVMVerificationContext
phase0HelloPolicyValidationLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = helloPolicyValidationContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0HelloPolicyValidationLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0HelloPolicyValidationLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0HelloPolicyValidationLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0HelloPolicyValidationLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0HelloPolicyValidationLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0HelloPolicyValidationLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyHelloPolicyValidationTranslation
  :: HelloPolicyValidationBundle
  -> LLVMArtifact
  -> Either HelloPolicyValidationLLVMError ()
verifyHelloPolicyValidationTranslation bundle llvmArtifact = do
  mapLeft HelloPolicyValidationLLVMSystemsError $
    verifyHelloPolicyValidationBundle bundle
  let systemsArtifact = helloPolicyValidationArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      moduleValue = llvmArtifactModule llvmArtifact
      context = phase0HelloPolicyValidationLLVMVerificationContext bundle
  forM_ (Map.toAscList (systemsProgramFunctions systemsProgram)) $
    \(functionName, systemsFunction) -> do
      llvmFunction <- lookupLLVMFunction moduleValue functionName
      let expectedParameters =
            [ LLVMParameter (unValueId valueId) LLVMPointerParameter
            | (valueId, SystemsValue { systemsValueRole = role }) <-
                Map.toAscList (systemsFunctionValues systemsFunction)
            , role == TransportHandle || isRuntimeInput role
            ]
      unless (llvmFunctionParameters llvmFunction == expectedParameters) $
        Left (HelloPolicyValidationLLVMParameterMismatch
          functionName (llvmFunctionParameters llvmFunction))
  verifyHelloPolicyValidationLLVMWitness bundle llvmArtifact
  mapLeft HelloPolicyValidationLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsHelloPolicyValidation
      context
      systemsArtifact
      llvmArtifact
  where
    isRuntimeInput role = case role of
      RuntimeInput _ -> True
      _ -> False

verifyHelloPolicyValidationLLVMWitness
  :: HelloPolicyValidationBundle
  -> LLVMArtifact
  -> Either HelloPolicyValidationLLVMError ()
verifyHelloPolicyValidationLLVMWitness bundle llvmArtifact = do
  let witness = helloPolicyValidationWitness bundle
      systemsArtifact = helloPolicyValidationArtifact bundle
      moduleValue = llvmArtifactModule llvmArtifact
      serverName = helloPolicyServerFunction witness
      commitId = LLVMBlockId (unBlockId (helloPolicyCommitBlock witness))
      acceptedId = LLVMBlockId (unBlockId (helloPolicyAcceptedTarget witness))
      failureId = LLVMBlockId (unBlockId (helloPolicyRejectedTarget witness))
      serverTransport = unValueId (helloPolicyServerTransport witness)
      policyContext = unValueId (helloPolicyPolicyContext witness)
      helloRecord = unValueId (helloPolicyHelloRecord witness)
      reason = unValueId (helloPolicyRejectReason witness)

  site <- case helloPolicyRuntimeSite systemsArtifact witness of
    Nothing -> Left (HelloPolicyValidationLLVMValidationMismatch
      serverName commitId (LLVMUnreachable Nothing))
    Just value -> Right value

  server <- lookupLLVMFunction moduleValue serverName
  commitBlock <- lookupLLVMBlock serverName server commitId
  unless (llvmBlockTerminator commitBlock == LLVMHelloPolicyValidate
      site policyContext helloRecord reason acceptedId failureId) $
    Left (HelloPolicyValidationLLVMValidationMismatch
      serverName commitId (llvmBlockTerminator commitBlock))

  failureBlock <- lookupLLVMBlock serverName server failureId
  unless
    ( llvmBlockOps failureBlock ==
        [ LLVMHelloPolicyValidationReasonBinding reason
        , LLVMHelloPolicyFailure serverTransport reason
        ]
    && llvmBlockTerminator failureBlock ==
        LLVMReturn ("fatal:" <> helloPolicyFailureClass witness)
    ) $
    Left (HelloPolicyValidationLLVMFailureMismatch
      serverName failureId (llvmBlockOps failureBlock) (llvmBlockTerminator failureBlock))

  case verifyBeginPolicyChoiceLLVMWitness
      (helloPolicyValidationPredecessor bundle) llvmArtifact of
    Right () -> pure ()
    Left err -> Left (HelloPolicyValidationLLVMBeginPolicyRegression (Text.pack (show err)))

  let rendered = llvmArtifactText llvmArtifact
      requiredCalls =
        [ "declare i1 @phil_runtime_validate_hello_policy(ptr, ptr, ptr)"
        , "declare void @phil_runtime_fail_hello_policy(ptr, ptr)"
        ]
  forM_ requiredCalls $ \needle ->
    unless (Text.isInfixOf needle rendered) $
      Left (HelloPolicyValidationLLVMRenderedCallMissing needle)

  forM_
    [ "@phil_call_fail_validation_HelloPolicy"
    , "@phil_runtime_validate_HelloPolicy()"
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (HelloPolicyValidationLLVMGenericCallDetected needle)

  forM_
    [ "current_policy"
    , "current_hello"
    , "current_hello_policy_reason"
    , "last_hello_policy_reason"
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (HelloPolicyValidationLLVMAmbientStateDetected needle)

  forM_ (Map.toAscList (llvmFunctions moduleValue)) $ \(functionName, functionValue) ->
    forM_ (Map.toAscList (llvmFunctionBlocks functionValue)) $ \(blockId, blockValue) -> do
      forM_ (llvmBlockOps blockValue) $ \operation ->
        case operation of
          LLVMPoison description ->
            Left (HelloPolicyValidationLLVMPoisonDetected description)
          _ -> pure ()
      case llvmBlockTerminator blockValue of
        LLVMUnreachable Nothing ->
          Left (HelloPolicyValidationLLVMUnresolvedControlDetected functionName blockId)
        _ -> pure ()

verifyPhase0HelloPolicyValidationLLVM :: Either HelloPolicyValidationLLVMError ()
verifyPhase0HelloPolicyValidationLLVM = do
  bundle <- mapLeft HelloPolicyValidationLLVMSystemsError phase0HelloPolicyValidationBundle
  let artifact = lowerSystemsHelloPolicyValidation
        phase0HelloPolicyValidationLLVMTarget
        (helloPolicyValidationArtifact bundle)
  verifyHelloPolicyValidationTranslation bundle artifact

helloPolicyRuntimeSite
  :: SystemsArtifact
  -> HelloPolicyValidationWitness
  -> Maybe RuntimeSiteRef
helloPolicyRuntimeSite artifact witness = do
  functionValue <- Map.lookup
    (helloPolicyServerFunction witness)
    (systemsProgramFunctions (systemsArtifactProgram artifact))
  blockValue <- Map.lookup
    (helloPolicyCommitBlock witness)
    (systemsFunctionBlocks functionValue)
  case systemsBlockTerminator blockValue of
    TermRuntimeChoice name inputs (Just site) _
      | name == helloPolicyRuntimeChoiceName witness
          && inputs == [helloPolicyPolicyContext witness, helloPolicyHelloRecord witness]
          && runtimeSiteKind site == ValidationBoundary "HelloPolicy" -> Just site
    _ -> Nothing

lookupLLVMFunction
  :: LLVMModule
  -> Text
  -> Either HelloPolicyValidationLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName =
  case Map.lookup functionName (llvmFunctions moduleValue) of
    Nothing -> Left (HelloPolicyValidationLLVMFunctionMissing functionName)
    Just functionValue -> Right functionValue

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either HelloPolicyValidationLLVMError LLVMBlock
lookupLLVMBlock functionName functionValue blockId =
  case Map.lookup blockId (llvmFunctionBlocks functionValue) of
    Nothing -> Left (HelloPolicyValidationLLVMBlockMissing functionName blockId)
    Just blockValue -> Right blockValue

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
