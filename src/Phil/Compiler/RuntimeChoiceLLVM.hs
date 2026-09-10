{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.RuntimeChoiceLLVM
  ( RuntimeChoiceLLVMArtifact (..)
  , RuntimeChoiceLLVMError (..)
  , runtimeChoiceProviderABIDescriptor
  , phase1RuntimeChoiceLLVMTarget
  , lowerRuntimeChoiceABIToLLVM
  ) where

import Control.Monad (forM_, unless)
import Data.Char (isAlphaNum)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest, digestText, unDigest)
import Phil.Compiler.RuntimeChoiceABI
import Phil.Compiler.RuntimeChoicePayload (RuntimeChoiceSite (..))
import Phil.LLVM.IR (LLVMTargetProfile (..))
import Phil.LLVM.Phase0 (phase0LLVMTarget)
import Phil.Systems.IR
import Phil.Systems.Phase1Stage

-- | The first executable Phase-1 qualified-provider ABI. Values cross this
-- boundary as opaque semantic handles. Borrowed slices pass their owner handle;
-- result payloads are written through out-slots and loaded only in the selected
-- successor. The runtime returns the certified canonical arm tag as i32.
runtimeChoiceProviderABIDescriptor :: Text
runtimeChoiceProviderABIDescriptor = Text.unlines
  [ "phil-runtime/phase1/runtime-choice-provider-v1"
  , "target=x86_64-unknown-linux-gnu"
  , "choice-return=i32 canonical-arm-tag"
  , "choice-symbol=site-qualified(function,block,qualified-provider-name)"
  , "input-carrier=ptr opaque-semantic-handle"
  , "borrowed-slice-input=owner-handle"
  , "payload-result=ptr out-slot"
  , "payload-load=selected-successor-only"
  , "arm-tag-order=canonical-ascending-label"
  , "invalid-tag=llvm.trap"
  , "ambient-provider-state=forbidden"
  , "success-outcome=0"
  , "other-outcomes=positive canonical-ascending-per-function"
  ]

phase1RuntimeChoiceLLVMTarget :: LLVMTargetProfile
phase1RuntimeChoiceLLVMTarget = phase0LLVMTarget
  { llvmTargetRuntimeABIDigest = digestText runtimeChoiceProviderABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase1/runtime-choice-provider-v1"
  }

data RuntimeChoiceLLVMArtifact = RuntimeChoiceLLVMArtifact
  { runtimeChoiceLLVMSourceSystemsDigest :: Digest
  , runtimeChoiceLLVMABIDigest :: Digest
  , runtimeChoiceLLVMTarget :: LLVMTargetProfile
  , runtimeChoiceLLVMTextDigest :: Digest
  , runtimeChoiceLLVMText :: Text
  }
  deriving (Eq, Show)

data RuntimeChoiceLLVMError
  = RuntimeChoiceLLVMStageRejected Phase1StageVerificationError
  | RuntimeChoiceLLVMSiteDomainMismatch (Set RuntimeChoiceSite) (Set RuntimeChoiceSite)
  | RuntimeChoiceLLVMFunctionMissing RuntimeChoiceSite
  | RuntimeChoiceLLVMBlockMissing RuntimeChoiceSite
  | RuntimeChoiceLLVMNotRuntimeChoice RuntimeChoiceSite
  | RuntimeChoiceLLVMNameMismatch RuntimeChoiceSite Text Text
  | RuntimeChoiceLLVMInputMismatch RuntimeChoiceSite [ValueId] [ValueId]
  | RuntimeChoiceLLVMInputCarrierMismatch RuntimeChoiceSite ValueId RuntimeChoiceABICarrier RuntimeChoiceABICarrier
  | RuntimeChoiceLLVMArmDomainMismatch RuntimeChoiceSite (Set Text) (Set Text)
  | RuntimeChoiceLLVMArmTagMismatch RuntimeChoiceSite Text Int Int
  | RuntimeChoiceLLVMArmTargetMismatch RuntimeChoiceSite Text BlockId BlockId
  | RuntimeChoiceLLVMArmPayloadMismatch RuntimeChoiceSite Text (Maybe ValueId) (Maybe ValueId)
  | RuntimeChoiceLLVMPayloadCarrierMismatch RuntimeChoiceSite Text ValueId RuntimeChoiceABICarrier RuntimeChoiceABICarrier
  | RuntimeChoiceLLVMValueMissing RuntimeChoiceSite ValueId
  | RuntimeChoiceLLVMPayloadTargetAmbiguous Text BlockId
  | RuntimeChoiceLLVMUnsupportedOperation Text BlockId SystemsOp
  | RuntimeChoiceLLVMUnsupportedTerminator Text BlockId SystemsTerminator
  deriving (Eq, Show)

lowerRuntimeChoiceABIToLLVM
  :: LLVMTargetProfile
  -> RuntimeChoiceABIPlan
  -> Phase1StageBundle
  -> Either RuntimeChoiceLLVMError RuntimeChoiceLLVMArtifact
lowerRuntimeChoiceABIToLLVM target abiPlan stage = do
  mapLeft RuntimeChoiceLLVMStageRejected (verifyPhase1StageBundle stage)
  validateABI program abiPlan
  renderedFunctions <- mapM (renderFunction abiPlan)
    (Map.toAscList (systemsProgramFunctions program))
  let text = Text.unlines
        ( renderHeader target systemsDigest abiDigest
        <> renderDeclarations abiPlan program
        <> concat renderedFunctions
        )
  pure RuntimeChoiceLLVMArtifact
    { runtimeChoiceLLVMSourceSystemsDigest = systemsDigest
    , runtimeChoiceLLVMABIDigest = abiDigest
    , runtimeChoiceLLVMTarget = target
    , runtimeChoiceLLVMTextDigest = digestText text
    , runtimeChoiceLLVMText = text
    }
  where
    systemsArtifact = phase1StageSystemsArtifact stage
    systemsDigest = systemsArtifactDigest systemsArtifact
    program = systemsArtifactProgram systemsArtifact
    abiDigest = runtimeChoiceABIPlanDigest abiPlan

validateABI
  :: SystemsProgram
  -> RuntimeChoiceABIPlan
  -> Either RuntimeChoiceLLVMError ()
validateABI program abiPlan = do
  let actualSites = collectRuntimeChoiceSites program
      plannedSites = runtimeChoiceABISites abiPlan
      actualDomain = Map.keysSet actualSites
      plannedDomain = Map.keysSet plannedSites
  unless (actualDomain == plannedDomain) $
    Left (RuntimeChoiceLLVMSiteDomainMismatch actualDomain plannedDomain)
  forM_ (Map.toAscList plannedSites) $ \(site, planned) ->
    validateSite program site planned

validateSite
  :: SystemsProgram
  -> RuntimeChoiceSite
  -> RuntimeChoiceABISite
  -> Either RuntimeChoiceLLVMError ()
validateSite program site planned = do
  function <- maybe
    (Left (RuntimeChoiceLLVMFunctionMissing site))
    Right
    (Map.lookup (runtimeChoiceSiteFunction site) (systemsProgramFunctions program))
  blockValue <- maybe
    (Left (RuntimeChoiceLLVMBlockMissing site))
    Right
    (Map.lookup (BlockId (runtimeChoiceSiteBlock site)) (systemsFunctionBlocks function))
  (name, inputs, arms) <- case systemsBlockTerminator blockValue of
    TermRuntimeChoice choiceName choiceInputs _ choiceArms ->
      Right (choiceName, choiceInputs, choiceArms)
    _ -> Left (RuntimeChoiceLLVMNotRuntimeChoice site)
  unless (name == runtimeChoiceABIName planned) $
    Left (RuntimeChoiceLLVMNameMismatch site name (runtimeChoiceABIName planned))
  let plannedInputs = map runtimeChoiceABIInputValue (runtimeChoiceABIInputs planned)
  unless (inputs == plannedInputs) $
    Left (RuntimeChoiceLLVMInputMismatch site inputs plannedInputs)
  forM_ (runtimeChoiceABIInputs planned) $ \plannedInput -> do
    value <- needValue site function (runtimeChoiceABIInputValue plannedInput)
    let actualCarrier = carrierForRole (systemsValueRole value)
        plannedCarrier = runtimeChoiceABIInputCarrier plannedInput
    unless (actualCarrier == plannedCarrier) $
      Left (RuntimeChoiceLLVMInputCarrierMismatch
        site (runtimeChoiceABIInputValue plannedInput) actualCarrier plannedCarrier)
  let plannedArms = runtimeChoiceABIArms planned
      actualDomain = Map.keysSet arms
      plannedDomain = Map.keysSet plannedArms
  unless (actualDomain == plannedDomain) $
    Left (RuntimeChoiceLLVMArmDomainMismatch site actualDomain plannedDomain)
  forM_ (zip [0 ..] (Map.toAscList plannedArms)) $ \(expectedTag, (label, plannedArm)) -> do
    let actualArm = arms Map.! label
    unless (runtimeChoiceABIArmTag plannedArm == expectedTag) $
      Left (RuntimeChoiceLLVMArmTagMismatch
        site label expectedTag (runtimeChoiceABIArmTag plannedArm))
    unless (runtimeChoiceArmTarget actualArm == runtimeChoiceABIArmTarget plannedArm) $
      Left (RuntimeChoiceLLVMArmTargetMismatch
        site label (runtimeChoiceArmTarget actualArm) (runtimeChoiceABIArmTarget plannedArm))
    let actualPayload = runtimeChoiceArmPayloadBinding actualArm
        plannedPayload = fst <$> runtimeChoiceABIArmPayload plannedArm
    unless (actualPayload == plannedPayload) $
      Left (RuntimeChoiceLLVMArmPayloadMismatch site label actualPayload plannedPayload)
    case runtimeChoiceABIArmPayload plannedArm of
      Nothing -> pure ()
      Just (valueId, plannedCarrier) -> do
        value <- needValue site function valueId
        let actualCarrier = carrierForRole (systemsValueRole value)
        unless (actualCarrier == plannedCarrier) $
          Left (RuntimeChoiceLLVMPayloadCarrierMismatch
            site label valueId actualCarrier plannedCarrier)

needValue
  :: RuntimeChoiceSite
  -> SystemsFunction
  -> ValueId
  -> Either RuntimeChoiceLLVMError SystemsValue
needValue site function valueId = maybe
  (Left (RuntimeChoiceLLVMValueMissing site valueId))
  Right
  (Map.lookup valueId (systemsFunctionValues function))

collectRuntimeChoiceSites
  :: SystemsProgram
  -> Map RuntimeChoiceSite SystemsTerminator
collectRuntimeChoiceSites program = Map.fromList
  [ (RuntimeChoiceSite functionName (unBlockId blockId), terminator)
  | (functionName, functionValue) <- Map.toAscList (systemsProgramFunctions program)
  , (blockId, blockValue) <- Map.toAscList (systemsFunctionBlocks functionValue)
  , let terminator = systemsBlockTerminator blockValue
  , TermRuntimeChoice {} <- [terminator]
  ]

renderHeader :: LLVMTargetProfile -> Digest -> Digest -> [Text]
renderHeader target systemsDigest abiDigest =
  [ "; Phil Phase-1 runtime-choice provider LLVM"
  , "; systems-digest=" <> unDigest systemsDigest
  , "; runtime-choice-abi-digest=" <> unDigest abiDigest
  , "; runtime-abi-profile=" <> llvmTargetRuntimeABIProfile target
  , "; runtime-abi-digest=" <> unDigest (llvmTargetRuntimeABIDigest target)
  , "source_filename = \"phil-phase1-runtime-choice\""
  , "target datalayout = \"" <> llvmTargetDataLayout target <> "\""
  , "target triple = \"" <> llvmTargetTripleName target <> "\""
  , ""
  ]

renderDeclarations :: RuntimeChoiceABIPlan -> SystemsProgram -> [Text]
renderDeclarations abiPlan program =
  choiceDeclarations
  <> releaseDeclaration
  <> trapDeclaration
  <> [""]
  where
    choiceDeclarations =
      [ "declare i32 @" <> runtimeSymbol site abiSite
          <> "(" <> Text.intercalate ", " (replicate argumentCount "ptr") <> ")"
      | (site, abiSite) <- Map.toAscList (runtimeChoiceABISites abiPlan)
      , let argumentCount =
              length (runtimeChoiceABIInputs abiSite)
                + length (payloadValues abiSite)
      ]
    releaseDeclaration =
      ["declare void @phil_runtime_release(ptr)" | programHasRelease program]
    trapDeclaration =
      ["declare void @llvm.trap()" | not (Map.null (runtimeChoiceABISites abiPlan))]

renderFunction
  :: RuntimeChoiceABIPlan
  -> (Text, SystemsFunction)
  -> Either RuntimeChoiceLLVMError [Text]
renderFunction abiPlan (functionName, functionValue) = do
  incoming <- incomingPayloads functionName abiPlan
  renderedBlocks <- mapM (renderBlock functionName functionValue abiPlan incoming outcomeCodes)
    (orderedBlocks functionValue)
  pure $
    [ "define i32 @" <> symbol functionName
        <> "(" <> Text.intercalate ", "
          [ "ptr %" <> symbol (unValueId valueId)
          | valueId <- externalInputs functionName abiPlan
          ]
        <> ") {"
    ]
    <> concat renderedBlocks
    <> ["}", ""]
  where
    outcomeCodes = functionOutcomeCodes functionValue

orderedBlocks :: SystemsFunction -> [(BlockId, SystemsBlock)]
orderedBlocks functionValue =
  case Map.lookup (systemsFunctionEntry functionValue) (systemsFunctionBlocks functionValue) of
    Nothing -> Map.toAscList (systemsFunctionBlocks functionValue)
    Just entryBlock ->
      (systemsFunctionEntry functionValue, entryBlock)
        : filter ((/= systemsFunctionEntry functionValue) . fst)
            (Map.toAscList (systemsFunctionBlocks functionValue))

renderBlock
  :: Text
  -> SystemsFunction
  -> RuntimeChoiceABIPlan
  -> Map BlockId (RuntimeChoiceSite, ValueId)
  -> Map Text Int
  -> (BlockId, SystemsBlock)
  -> Either RuntimeChoiceLLVMError [Text]
renderBlock functionName functionValue abiPlan incoming outcomeCodes (blockId, blockValue) = do
  opLines <- fmap concat $ mapM (renderOperation functionName blockId)
    (systemsBlockOps blockValue)
  terminatorLines <- renderTerminator
    functionName functionValue abiPlan outcomeCodes blockId (systemsBlockTerminator blockValue)
  pure $
    [symbol (unBlockId blockId) <> ":"]
    <> maybe [] (renderPayloadLoad blockId) (Map.lookup blockId incoming)
    <> map ("  " <>) opLines
    <> map ("  " <>) terminatorLines

renderPayloadLoad :: BlockId -> (RuntimeChoiceSite, ValueId) -> [Text]
renderPayloadLoad _ (sourceSite, valueId) =
  [ "  %" <> symbol (unValueId valueId)
      <> " = load ptr, ptr %" <> payloadSlotName sourceSite valueId
  ]

renderOperation
  :: Text
  -> BlockId
  -> SystemsOp
  -> Either RuntimeChoiceLLVMError [Text]
renderOperation _ _ (OpReleaseOwner owner _) =
  Right ["call void @phil_runtime_release(ptr %" <> symbol (unValueId owner) <> ")"]
renderOperation _ _ (OpTraceEvent eventName) =
  Right ["; !phil trace " <> oneLine eventName]
renderOperation functionName blockId operation =
  Left (RuntimeChoiceLLVMUnsupportedOperation functionName blockId operation)

renderTerminator
  :: Text
  -> SystemsFunction
  -> RuntimeChoiceABIPlan
  -> Map Text Int
  -> BlockId
  -> SystemsTerminator
  -> Either RuntimeChoiceLLVMError [Text]
renderTerminator functionName _functionValue abiPlan _outcomes blockId TermRuntimeChoice {} = do
  let site = RuntimeChoiceSite functionName (unBlockId blockId)
  abiSite <- maybe
    (Left (RuntimeChoiceLLVMNotRuntimeChoice site))
    Right
    (Map.lookup site (runtimeChoiceABISites abiPlan))
  pure (renderRuntimeChoice site abiSite)
renderTerminator _ _ _ outcomes _ (TermEnd outcome) =
  Right ["ret i32 " <> Text.pack (show (Map.findWithDefault 1 outcome outcomes))]
renderTerminator _ _ _ outcomes _ (TermFatal reason) =
  Right ["ret i32 " <> Text.pack (show (Map.findWithDefault 1 ("fatal:" <> reason) outcomes))]
renderTerminator functionName _ _ _ blockId terminator =
  Left (RuntimeChoiceLLVMUnsupportedTerminator functionName blockId terminator)

renderRuntimeChoice :: RuntimeChoiceSite -> RuntimeChoiceABISite -> [Text]
renderRuntimeChoice site abiSite =
  slotLines
  <> [ tagName <> " = call i32 @" <> runtimeSymbol site abiSite
        <> "(" <> Text.intercalate ", " (inputArgs <> outputArgs) <> ")"
     , "switch i32 " <> tagName <> ", label %" <> invalidLabel <> " ["
     ]
  <> [ "  i32 " <> Text.pack (show (runtimeChoiceABIArmTag armValue))
        <> ", label %" <> symbol (unBlockId (runtimeChoiceABIArmTarget armValue))
     | (_, armValue) <- Map.toAscList (runtimeChoiceABIArms abiSite)
     ]
  <> [ "]"
     , invalidLabel <> ":"
     , "  call void @llvm.trap()"
     , "  unreachable"
     ]
  where
    payloads = payloadValues abiSite
    slotLines =
      [ "%" <> payloadSlotName site valueId <> " = alloca ptr"
      | valueId <- payloads
      ]
    inputArgs = map ("ptr %" <>)
      [ symbol (unValueId (runtimeInputRoot input))
      | input <- runtimeChoiceABIInputs abiSite
      ]
    outputArgs =
      [ "ptr %" <> payloadSlotName site valueId
      | valueId <- payloads
      ]
    tagName = "%phil_runtime_choice_tag_"
      <> symbol (runtimeChoiceSiteFunction site <> "_" <> runtimeChoiceSiteBlock site)
    invalidLabel = symbol
      ("phil_runtime_choice_invalid_"
        <> runtimeChoiceSiteFunction site <> "_" <> runtimeChoiceSiteBlock site)

incomingPayloads
  :: Text
  -> RuntimeChoiceABIPlan
  -> Either RuntimeChoiceLLVMError (Map BlockId (RuntimeChoiceSite, ValueId))
incomingPayloads functionName abiPlan =
  foldl insertIncoming (Right Map.empty) candidates
  where
    candidates =
      [ (runtimeChoiceABIArmTarget armValue, site, valueId)
      | (site, abiSite) <- Map.toAscList (runtimeChoiceABISites abiPlan)
      , runtimeChoiceSiteFunction site == functionName
      , (_, armValue) <- Map.toAscList (runtimeChoiceABIArms abiSite)
      , Just (valueId, _) <- [runtimeChoiceABIArmPayload armValue]
      ]
    insertIncoming acc (target, site, valueId) = do
      result <- acc
      case Map.lookup target result of
        Nothing -> Right (Map.insert target (site, valueId) result)
        Just existing
          | existing == (site, valueId) -> Right result
          | otherwise -> Left (RuntimeChoiceLLVMPayloadTargetAmbiguous functionName target)

externalInputs :: Text -> RuntimeChoiceABIPlan -> [ValueId]
externalInputs functionName abiPlan =
  sortValues . Set.toList $ required `Set.difference` produced
  where
    functionSites =
      [ abiSite
      | (site, abiSite) <- Map.toAscList (runtimeChoiceABISites abiPlan)
      , runtimeChoiceSiteFunction site == functionName
      ]
    required = Set.fromList
      [ runtimeInputRoot input
      | abiSite <- functionSites
      , input <- runtimeChoiceABIInputs abiSite
      ]
    produced = Set.fromList
      [ valueId
      | abiSite <- functionSites
      , (_, armValue) <- Map.toAscList (runtimeChoiceABIArms abiSite)
      , Just (valueId, _) <- [runtimeChoiceABIArmPayload armValue]
      ]

runtimeInputRoot :: RuntimeChoiceABIInput -> ValueId
runtimeInputRoot input = case runtimeChoiceABIInputCarrier input of
  ABIBorrowedSlice owner -> owner
  _ -> runtimeChoiceABIInputValue input

payloadValues :: RuntimeChoiceABISite -> [ValueId]
payloadValues abiSite = sortValues . Set.toList . Set.fromList $
  [ valueId
  | (_, armValue) <- Map.toAscList (runtimeChoiceABIArms abiSite)
  , Just (valueId, _) <- [runtimeChoiceABIArmPayload armValue]
  ]

sortValues :: [ValueId] -> [ValueId]
sortValues = map snd . sort . map (\valueId -> (unValueId valueId, valueId))

runtimeSymbol :: RuntimeChoiceSite -> RuntimeChoiceABISite -> Text
runtimeSymbol site abiSite = symbol $ Text.intercalate "_"
  [ "phil_runtime_choice"
  , runtimeChoiceSiteFunction site
  , runtimeChoiceSiteBlock site
  , runtimeChoiceABIName abiSite
  ]

payloadSlotName :: RuntimeChoiceSite -> ValueId -> Text
payloadSlotName site valueId = symbol $ Text.intercalate "_"
  [ "phil_runtime_choice_payload_slot"
  , runtimeChoiceSiteFunction site
  , runtimeChoiceSiteBlock site
  , unValueId valueId
  ]

functionOutcomeCodes :: SystemsFunction -> Map Text Int
functionOutcomeCodes functionValue =
  Map.fromList (successEntry <> zip nonSuccess [1 ..])
  where
    outcomes = Set.toAscList . Set.fromList $
      [ outcomeKey (systemsBlockTerminator blockValue)
      | blockValue <- Map.elems (systemsFunctionBlocks functionValue)
      , isOutcome (systemsBlockTerminator blockValue)
      ]
    successEntry = [("success", 0) | "success" `elem` outcomes]
    nonSuccess = filter (/= "success") outcomes
    outcomeKey terminator = case terminator of
      TermEnd outcome -> outcome
      TermFatal reason -> "fatal:" <> reason
      _ -> ""
    isOutcome terminator = case terminator of
      TermEnd {} -> True
      TermFatal {} -> True
      _ -> False

programHasRelease :: SystemsProgram -> Bool
programHasRelease program = any blockHasRelease
  [ blockValue
  | functionValue <- Map.elems (systemsProgramFunctions program)
  , blockValue <- Map.elems (systemsFunctionBlocks functionValue)
  ]
  where
    blockHasRelease blockValue = any isRelease (systemsBlockOps blockValue)
    isRelease OpReleaseOwner {} = True
    isRelease _ = False

carrierForRole :: SystemsValueRole -> RuntimeChoiceABICarrier
carrierForRole role = case role of
  TransportHandle -> ABITransportHandle
  PendingIngress grammar -> ABIPendingIngress grammar
  FrameOwner grammar -> ABIFrameOwner grammar
  OwnedBuffer semanticType -> ABIOwnedBuffer semanticType
  BorrowedSlice owner -> ABIBorrowedSlice owner
  RuntimeScalar scalarType -> ABIRuntimeScalar scalarType
  RuntimeInput inputType -> ABIRuntimeInput inputType
  RuntimeOpaque opaqueType -> ABIRuntimeOpaque opaqueType
  TypedScalar scalarType -> ABITypedScalar scalarType
  RuntimeRecord recordType -> ABIRuntimeRecord recordType
  DiagnosticState stateType -> ABIDiagnosticState stateType

symbol :: Text -> Text
symbol = Text.map (\character -> if isAlphaNum character then character else '_')

oneLine :: Text -> Text
oneLine = Text.replace "\n" " " . Text.replace "\r" " "

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
