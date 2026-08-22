{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.Lower
  ( lowerSystemsConservative
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.LLVM.IR
import Phil.Systems.IR

lowerSystemsConservative :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsConservative target systemsArtifact = artifact
  where
    program = systemsArtifactProgram systemsArtifact
    sourceContract = systemsArtifactStageContract systemsArtifact
    moduleValue = LLVMModule
      { llvmModuleName = systemsProgramName program <> "-preopt"
      , llvmLanguageVersion = llvmTargetLanguageVersion target
      , llvmToolVersion = llvmTargetToolVersion target
      , llvmTargetTriple = llvmTargetTripleName target
      , llvmDataLayout = llvmTargetDataLayout target
      , llvmRuntimeABIDigest = llvmTargetRuntimeABIDigest target
      , llvmRuntimeABIProfile = llvmTargetRuntimeABIProfile target
      , llvmCompilationProfile = systemsProgramProfile program
      , llvmFunctions = Map.fromList
          [ (functionKey, lowerFunction target functionValue)
          | (functionKey, functionValue) <- Map.toAscList (systemsProgramFunctions program)
          ]
      , llvmStrengthenings = Map.empty
      }
    contract = LLVMEmissionContract
      { llvmContractSourceDigest = systemsArtifactDigest systemsArtifact
      , llvmContractTargetDigest = llvmModuleDigest moduleValue
      , llvmContractEdgeWitnesses = allEdgeWitnesses program
      , llvmContractTraceRelation = stageTraceRelation sourceContract
      , llvmContractResourceFailureRelation = stageResourceFailureRelation sourceContract
      }
    artifact = LLVMArtifact
      { llvmArtifactModule = moduleValue
      , llvmArtifactText = renderLLVMModule moduleValue
      , llvmArtifactContract = contract
      }

lowerFunction :: LLVMTargetProfile -> SystemsFunction -> LLVMFunction
lowerFunction target functionValue = LLVMFunction
  { llvmFunctionName = systemsFunctionName functionValue
  , llvmFunctionEntry = lowerBlockId (systemsFunctionEntry functionValue)
  , llvmFunctionBlocks = Map.fromList
      [ (lowerBlockId blockKey, lowerBlock target functionValue blockValue)
      | (blockKey, blockValue) <- Map.toAscList (systemsFunctionBlocks functionValue)
      ]
  }

lowerBlock :: LLVMTargetProfile -> SystemsFunction -> SystemsBlock -> LLVMBlock
lowerBlock target functionValue blockValue = LLVMBlock
  { llvmBlockId = lowerBlockId (systemsBlockId blockValue)
  , llvmBlockOps = concatMap (lowerOp target functionValue) (systemsBlockOps blockValue)
  , llvmBlockTerminator = lowerTerminator target functionValue (systemsBlockTerminator blockValue)
  }

lowerOp :: LLVMTargetProfile -> SystemsFunction -> SystemsOp -> [LLVMOp]
lowerOp target functionValue operation = case operation of
  OpReceiveFrame { receiveGrammar = grammar } ->
    [LLVMCall ("receive_frame." <> grammar)]
  OpBorrowView {} -> [LLVMPlain "borrowed view; no representation copy"]
  OpCommitIngress {} -> [LLVMPlain "commit recognized ingress into CFG typestate"]
  OpDestroyPending {} -> [LLVMCleanup "destroy pending ingress/frame"]
  OpReleaseOwner {} -> [LLVMCleanup "release owner"]
  OpCleanupPartial {} -> [LLVMCleanup "cleanup partial owner"]
  OpRuntimeCall
    { runtimeCallName = name
    , runtimeCallInputs = inputs
    , runtimeCallOutputs = outputs
    , runtimeCallSite = maybeSite
    } ->
      case maybeSite of
        Just site -> [LLVMRuntime site name]
        Nothing -> case abiV1FieldProjection target functionValue name inputs outputs of
          Just encoded -> [LLVMCall encoded]
          Nothing -> [LLVMCall name]
  OpCopy {} -> [LLVMCall "copy"]
  OpEraseFact {} -> [LLVMMetadata "proof/typestate fact erased before LLVM"]
  OpDiagnostic { diagnosticName = name } -> [LLVMMetadata ("diagnostic " <> name)]
  OpScalarLiteral { scalarLiteralOutput = output, scalarLiteralValue = literal } ->
    [LLVMScalarLiteral (unValueId output) literal]
  OpTraceEvent name -> [LLVMMetadata ("trace " <> name)]

lowerTerminator :: LLVMTargetProfile -> SystemsFunction -> SystemsTerminator -> LLVMTerminator
lowerTerminator target functionValue terminator = case terminator of
  TermJump targetBlock -> LLVMJump (lowerBlockId targetBlock)
  TermBranch _ yes no -> LLVMBranch (lowerBlockId yes) (lowerBlockId no)
  TermRecognize
    { recognizePending = pending
    , recognizeSite = site
    , recognizeSuccess = yes
    , recognizeFailure = no
    } ->
      if isRecognizedRecordV1 target
        then LLVMRuntimeBranch
          site
          (recognitionRuntimeName functionValue pending site)
          (lowerBlockId yes)
          (lowerBlockId no)
        else runtimeBranch site yes no
  TermRuntimeCheck { checkSite = site, checkSuccess = yes, checkFailure = no } ->
    runtimeBranch site yes no
  TermReceiveExact
    { exactLength = lengthValue
    , exactSite = site
    , exactSuccess = yes
    , exactFailure = no
    } ->
      if isRecognizedRecordV1 target && isU64Value functionValue lengthValue
        then LLVMRuntimeBranch
          site
          ("abi-v1:receive-exact-u64:" <> unValueId lengthValue)
          (lowerBlockId yes)
          (lowerBlockId no)
        else runtimeBranch site yes no
  TermSendExact { sendExactSite = site, sendExactSuccess = yes, sendExactFailure = no } ->
    runtimeBranch site yes no
  TermStore { storeSite = site, storeSuccess = yes, storeFailure = no } ->
    runtimeBranch site yes no
  TermReturnScalar valueId ->
    case Map.lookup valueId (systemsFunctionValues functionValue) of
      Just SystemsValue { systemsValueRole = TypedScalar scalarType } ->
        LLVMReturnScalar (unValueId valueId) scalarType
      _ -> LLVMReturn ("invalid-scalar-return:" <> unValueId valueId)
  TermEnd outcome -> LLVMReturn outcome
  TermFatal failure -> LLVMReturn ("fatal:" <> failure)

abiV1FieldProjection
  :: LLVMTargetProfile
  -> SystemsFunction
  -> Text
  -> [ValueId]
  -> [ValueId]
  -> Maybe Text
abiV1FieldProjection target functionValue name inputs outputs
  | not (isRecognizedRecordV1 target) = Nothing
  | otherwise = do
      semanticField <- Text.stripPrefix "project recognized " name
      (grammar, fieldName) <- splitSemanticField semanticField
      recordValue <- case inputs of
        [single] -> Just single
        _ -> Nothing
      outputValue <- case outputs of
        [single] -> Just single
        _ -> Nothing
      recordRole <- systemsValueRole <$> Map.lookup recordValue (systemsFunctionValues functionValue)
      scalarRole <- systemsValueRole <$> Map.lookup outputValue (systemsFunctionValues functionValue)
      case (recordRole, scalarRole) of
        (RuntimeRecord recordGrammar, TypedScalar (ScalarUInt width))
          | recordGrammar == grammar -> Just $ Text.intercalate ":"
              [ "abi-v1"
              , "field"
              , grammar
              , fieldName
              , unValueId recordValue
              , unValueId outputValue
              , Text.pack (show width)
              ]
        _ -> Nothing

splitSemanticField :: Text -> Maybe (Text, Text)
splitSemanticField value = case Text.splitOn "." value of
  [grammar, fieldName]
    | not (Text.null grammar) && not (Text.null fieldName) -> Just (grammar, fieldName)
  _ -> Nothing

recognitionRuntimeName :: SystemsFunction -> ValueId -> RuntimeSiteRef -> Text
recognitionRuntimeName functionValue pending site = case runtimeSiteKind site of
  RecognitionBoundary grammar -> Text.intercalate ":"
    [ "abi-v1"
    , "recognize"
    , grammar
    , unValueId (recordValueForGrammar functionValue grammar pending)
    ]
  _ -> siteName site

recordValueForGrammar :: SystemsFunction -> Text -> ValueId -> ValueId
recordValueForGrammar functionValue grammar pending =
  case
    [ valueId
    | (valueId, SystemsValue { systemsValueRole = RuntimeRecord candidate }) <-
        Map.toAscList (systemsFunctionValues functionValue)
    , candidate == grammar
    ] of
      [valueId] -> valueId
      _ -> ValueId ("phil.recognized." <> grammar <> "." <> unValueId pending)

isU64Value :: SystemsFunction -> ValueId -> Bool
isU64Value functionValue valueId =
  case Map.lookup valueId (systemsFunctionValues functionValue) of
    Just SystemsValue { systemsValueRole = TypedScalar (ScalarUInt 64) } -> True
    _ -> False

isRecognizedRecordV1 :: LLVMTargetProfile -> Bool
isRecognizedRecordV1 target =
  llvmTargetRuntimeABIProfile target == "phil-runtime/phase0/recognized-record-v1"

runtimeBranch :: RuntimeSiteRef -> BlockId -> BlockId -> LLVMTerminator
runtimeBranch site yes no =
  LLVMRuntimeBranch site (siteName site) (lowerBlockId yes) (lowerBlockId no)

siteName :: RuntimeSiteRef -> Text
siteName site = Text.pack (show (runtimeSiteKind site))

allEdgeWitnesses :: SystemsProgram -> [LLVMEdgeWitness]
allEdgeWitnesses program =
  [ LLVMEdgeWitness
      { llvmEdgeSourceFunction = systemsFunctionName functionValue
      , llvmEdgeSourceFrom = systemsBlockId blockValue
      , llvmEdgeSourceTo = target
      , llvmEdgeTargetFunction = systemsFunctionName functionValue
      , llvmEdgeTargetPath = [lowerBlockId (systemsBlockId blockValue), lowerBlockId target]
      }
  | functionValue <- Map.elems (systemsProgramFunctions program)
  , blockValue <- Map.elems (systemsFunctionBlocks functionValue)
  , target <- blockSuccessors blockValue
  ]

lowerBlockId :: BlockId -> LLVMBlockId
lowerBlockId = LLVMBlockId . unBlockId
