{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.Lower
  ( lowerSystemsConservative
  , lowerSystemsRecognizedRecord
  , lowerSystemsExactReceive
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.LLVM.IR
import Phil.Systems.IR

data LoweringMode
  = ConservativeMode
  | RecognizedRecordMode
  | ExactReceiveMode
  deriving (Eq, Show)

lowerSystemsConservative :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsConservative = lowerSystemsWith ConservativeMode

lowerSystemsRecognizedRecord :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsRecognizedRecord = lowerSystemsWith RecognizedRecordMode

lowerSystemsExactReceive :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsExactReceive = lowerSystemsWith ExactReceiveMode

lowerSystemsWith
  :: LoweringMode
  -> LLVMTargetProfile
  -> SystemsArtifact
  -> LLVMArtifact
lowerSystemsWith mode target systemsArtifact = artifact
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
          [ (functionKey, lowerFunction mode functionValue)
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

lowerFunction :: LoweringMode -> SystemsFunction -> LLVMFunction
lowerFunction mode functionValue = LLVMFunction
  { llvmFunctionName = systemsFunctionName functionValue
  , llvmFunctionParameters = lowerParameters mode functionValue
  , llvmFunctionEntry = lowerBlockId (systemsFunctionEntry functionValue)
  , llvmFunctionBlocks = Map.fromList
      [ (lowerBlockId blockKey, lowerBlock mode functionValue blockValue)
      | (blockKey, blockValue) <- Map.toAscList (systemsFunctionBlocks functionValue)
      ]
  }

lowerParameters :: LoweringMode -> SystemsFunction -> [LLVMParameter]
lowerParameters mode functionValue = case mode of
  ExactReceiveMode ->
    [ LLVMParameter (unValueId valueId) LLVMPointerParameter
    | (valueId, SystemsValue { systemsValueRole = TransportHandle }) <-
        Map.toAscList (systemsFunctionValues functionValue)
    ]
  _ -> []

lowerBlock :: LoweringMode -> SystemsFunction -> SystemsBlock -> LLVMBlock
lowerBlock mode functionValue blockValue = LLVMBlock
  { llvmBlockId = lowerBlockId (systemsBlockId blockValue)
  , llvmBlockOps = concatMap (lowerOp mode functionValue) (systemsBlockOps blockValue)
  , llvmBlockTerminator = lowerTerminator mode functionValue (systemsBlockTerminator blockValue)
  }

lowerOp :: LoweringMode -> SystemsFunction -> SystemsOp -> [LLVMOp]
lowerOp mode functionValue operation = case operation of
  OpReceiveFrame { receiveGrammar = grammar } ->
    [LLVMCall ("receive_frame." <> grammar)]
  OpBorrowView {} -> [LLVMPlain "borrowed view; no representation copy"]
  OpCommitIngress {} -> [LLVMPlain "commit recognized ingress into CFG typestate"]
  OpDestroyPending {} -> [LLVMCleanup "destroy pending ingress/frame"]
  OpReleaseOwner { releaseOwner = owner }
    | mode == ExactReceiveMode && isExactReceivePayload functionValue owner ->
        [LLVMBufferRelease (payloadSSAName owner)]
    | otherwise -> [LLVMCleanup "release owner"]
  OpCleanupPartial { cleanupOwner = owner }
    | mode == ExactReceiveMode && isExactReceivePayload functionValue owner ->
        [LLVMBufferRelease (payloadSSAName owner)]
    | otherwise -> [LLVMCleanup "cleanup partial owner"]
  OpRuntimeCall
    { runtimeCallName = name
    , runtimeCallInputs = inputs
    , runtimeCallOutputs = outputs
    , runtimeCallSite = maybeSite
    } ->
      case maybeSite of
        Just site -> [LLVMRuntime site name]
        Nothing
          | mode /= ConservativeMode
          , isRecordMaterialization functionValue name inputs outputs -> []
          | mode /= ConservativeMode
          , Just projection <- recordProjection functionValue name inputs outputs ->
              [projection]
          | otherwise -> [LLVMCall name]
  OpCopy {} -> [LLVMCall "copy"]
  OpEraseFact {} -> [LLVMMetadata "proof/typestate fact erased before LLVM"]
  OpDiagnostic { diagnosticName = name } -> [LLVMMetadata ("diagnostic " <> name)]
  OpScalarLiteral { scalarLiteralOutput = output, scalarLiteralValue = literal } ->
    [LLVMScalarLiteral (unValueId output) literal]
  OpTraceEvent name -> [LLVMMetadata ("trace " <> name)]

lowerTerminator :: LoweringMode -> SystemsFunction -> SystemsTerminator -> LLVMTerminator
lowerTerminator mode functionValue terminator = case terminator of
  TermJump target -> LLVMJump (lowerBlockId target)
  TermBranch _ yes no -> LLVMBranch (lowerBlockId yes) (lowerBlockId no)
  TermRecognize
    { recognizePending = pending
    , recognizeSite = site
    , recognizeSuccess = yes
    , recognizeFailure = no
    } ->
      case mode of
        ConservativeMode -> runtimeBranch site yes no
        _ ->
          case recognizedRecordForSuccess functionValue pending yes of
            Just (grammar, recordValue) ->
              LLVMRecognizeRecord
                site
                grammar
                (unValueId recordValue)
                (lowerBlockId yes)
                (lowerBlockId no)
            Nothing -> runtimeBranch site yes no
  TermRuntimeCheck { checkSite = site, checkSuccess = yes, checkFailure = no } ->
    runtimeBranch site yes no
  TermReceiveExact
    { exactTransport = transportValue
    , exactLength = lengthValue
    , exactPayloadOwner = payloadValue
    , exactSite = site
    , exactSuccess = yes
    , exactFailure = no
    } ->
      case mode of
        ExactReceiveMode ->
          case
            ( transportRoleOf functionValue transportValue
            , scalarTypeOf functionValue lengthValue
            , payloadRoleOf functionValue payloadValue
            ) of
            (True, Just scalarType, True) -> LLVMExactReceive
              site
              ("receive_exact_" <> scalarSuffix scalarType)
              (unValueId transportValue)
              (unValueId lengthValue)
              scalarType
              (payloadSSAName payloadValue)
              (lowerBlockId yes)
              (lowerBlockId no)
            _ -> runtimeBranch site yes no
        RecognizedRecordMode ->
          case scalarTypeOf functionValue lengthValue of
            Just scalarType -> LLVMRuntimeScalarBranch
              site
              ("receive_exact_" <> scalarSuffix scalarType)
              (unValueId lengthValue)
              scalarType
              (lowerBlockId yes)
              (lowerBlockId no)
            Nothing -> runtimeBranch site yes no
        ConservativeMode -> runtimeBranch site yes no
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

runtimeBranch :: RuntimeSiteRef -> BlockId -> BlockId -> LLVMTerminator
runtimeBranch site yes no =
  LLVMRuntimeBranch site (siteName site) (lowerBlockId yes) (lowerBlockId no)

recognizedRecordForSuccess
  :: SystemsFunction
  -> ValueId
  -> BlockId
  -> Maybe (Text, ValueId)
recognizedRecordForSuccess functionValue _pending successBlock = do
  blockValue <- Map.lookup successBlock (systemsFunctionBlocks functionValue)
  firstRecognizedRecord functionValue (systemsBlockOps blockValue)

firstRecognizedRecord :: SystemsFunction -> [SystemsOp] -> Maybe (Text, ValueId)
firstRecognizedRecord _ [] = Nothing
firstRecognizedRecord functionValue (operation : rest) =
  case operation of
    OpRuntimeCall
      { runtimeCallName = name
      , runtimeCallInputs = []
      , runtimeCallOutputs = [output]
      , runtimeCallSite = Nothing
      } ->
        case Map.lookup output (systemsFunctionValues functionValue) of
          Just SystemsValue { systemsValueRole = RuntimeRecord grammar }
            | name == "materialize recognized " <> grammar -> Just (grammar, output)
          _ -> firstRecognizedRecord functionValue rest
    _ -> firstRecognizedRecord functionValue rest

isRecordMaterialization
  :: SystemsFunction
  -> Text
  -> [ValueId]
  -> [ValueId]
  -> Bool
isRecordMaterialization functionValue name inputs outputs =
  case (inputs, outputs) of
    ([], [output]) ->
      case Map.lookup output (systemsFunctionValues functionValue) of
        Just SystemsValue { systemsValueRole = RuntimeRecord grammar } ->
          name == "materialize recognized " <> grammar
        _ -> False
    _ -> False

recordProjection
  :: SystemsFunction
  -> Text
  -> [ValueId]
  -> [ValueId]
  -> Maybe LLVMOp
recordProjection functionValue name inputs outputs =
  case (inputs, outputs) of
    ([recordValue], [outputValue]) -> do
      SystemsValue { systemsValueRole = RuntimeRecord grammar } <-
        Map.lookup recordValue (systemsFunctionValues functionValue)
      SystemsValue { systemsValueRole = TypedScalar scalarType } <-
        Map.lookup outputValue (systemsFunctionValues functionValue)
      fieldName <- Text.stripPrefix ("project recognized " <> grammar <> ".") name
      pure (LLVMFieldProjection
        (unValueId outputValue)
        (unValueId recordValue)
        grammar
        fieldName
        scalarType)
    _ -> Nothing

transportRoleOf :: SystemsFunction -> ValueId -> Bool
transportRoleOf functionValue valueId =
  case Map.lookup valueId (systemsFunctionValues functionValue) of
    Just SystemsValue { systemsValueRole = TransportHandle } -> True
    _ -> False

payloadRoleOf :: SystemsFunction -> ValueId -> Bool
payloadRoleOf functionValue valueId =
  case Map.lookup valueId (systemsFunctionValues functionValue) of
    Just SystemsValue { systemsValueRole = OwnedBuffer _ } -> True
    _ -> False

isExactReceivePayload :: SystemsFunction -> ValueId -> Bool
isExactReceivePayload functionValue owner = any blockOwnsPayload
  (Map.elems (systemsFunctionBlocks functionValue))
  where
    blockOwnsPayload blockValue = case systemsBlockTerminator blockValue of
      TermReceiveExact { exactPayloadOwner = payload } -> payload == owner
      _ -> False

payloadSSAName :: ValueId -> Text
payloadSSAName valueId = unValueId valueId <> ".owner"

scalarTypeOf :: SystemsFunction -> ValueId -> Maybe ScalarType
scalarTypeOf functionValue valueId = do
  SystemsValue { systemsValueRole = TypedScalar scalarType } <-
    Map.lookup valueId (systemsFunctionValues functionValue)
  pure scalarType

scalarSuffix :: ScalarType -> Text
scalarSuffix scalarType = case scalarType of
  ScalarBool -> "bool"
  ScalarUInt width -> "u" <> Text.pack (show width)

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
