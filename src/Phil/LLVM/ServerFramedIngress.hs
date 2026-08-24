{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ServerFramedIngress
  ( ServerFramedIngressLLVMError (..)
  , serverFramedIngressABIDescriptor
  , phase0ServerFramedIngressLLVMTarget
  , phase0ServerFramedIngressLLVMArtifact
  , phase0ServerFramedIngressLLVMVerificationContext
  , lowerSystemsServerFramedIngress
  , verifyServerFramedIngressLLVMWitnesses
  , verifyServerFramedIngressTranslation
  , verifyPhase0ServerFramedIngressLLVM
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest)
import Phil.LLVM.IR
import Phil.LLVM.ClientControlSend
  ( ClientControlSendLLVMError
  , clientControlSendABIDescriptor
  , lowerSystemsClientControlSend
  , phase0ClientControlSendLLVMTarget
  , verifyClientControlSendLLVMWitness
  )
import Phil.LLVM.Verify
import Phil.Systems.IR
import Phil.Systems.RecognitionFailure

data ServerFramedIngressLLVMError
  = ServerFramedIngressSystemsError RecognitionFailureError
  | ServerFramedIngressClientRegression ClientControlSendLLVMError
  | ServerFramedIngressLLVMVerificationError LLVMVerificationError
  | ServerFramedIngressSystemsFunctionMissing Text
  | ServerFramedIngressSystemsBlockMissing Text BlockId
  | ServerFramedIngressLLVMFunctionMissing Text
  | ServerFramedIngressLLVMBlockMissing Text LLVMBlockId
  | ServerFramedIngressIngressShapeMismatch Text BlockId
  | ServerFramedIngressRecordMaterializationMismatch Text BlockId
  | ServerFramedIngressParameterMismatch [LLVMParameter]
  | ServerFramedIngressRecognitionOpsMismatch Text LLVMBlockId [LLVMOp]
  | ServerFramedIngressRecognitionTerminatorMismatch Text LLVMBlockId LLVMTerminator
  | ServerFramedIngressCommitMismatch Text LLVMBlockId [LLVMOp]
  | ServerFramedIngressFailureMismatch Text LLVMBlockId [LLVMOp] LLVMTerminator
  | ServerFramedIngressRenderedPrimitiveMissing Text
  | ServerFramedIngressLegacyPrimitivePresent Text
  | ServerFramedIngressAmbientStatePresent Text
  deriving (Eq, Show)

serverFunctionName :: Text
serverFunctionName = "UploadServer"

serverFramedIngressABIDescriptor :: Text
serverFramedIngressABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/server-framed-ingress-v1"
  , "base-client-control-send-abi-digest=" <> unDigest (digestText clientControlSendABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0ClientControlSendLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0ClientControlSendLLVMTarget
  , "source-authority=recognition-failure-detail-v1"
  , "receive-frame=phil_runtime_receive_frame_<grammar>(ptr,ptr,ptr)->void"
  , "receive-frame-arg0=exact-server-transport"
  , "receive-frame-arg1=pending-output-slot"
  , "receive-frame-arg2=frame-output-slot"
  , "receive-frame-semantics=one-complete-frame-or-do-not-return-normally"
  , "pending-handle=opaque-runtime-owned"
  , "frame-handle=opaque-runtime-owned"
  , "frame-view=phil_runtime_frame_borrow_view_<grammar>(ptr)->ptr"
  , "frame-view-semantics=borrow-no-copy-valid-through-recognition"
  , "recognize=phil_runtime_recognize_<grammar>(ptr,ptr,ptr,ptr)->i8"
  , "recognize-arg0=exact-pending-handle"
  , "recognize-arg1=exact-borrowed-raw-view"
  , "recognize-arg2=record-output-slot"
  , "recognize-arg3=reason-output-slot"
  , "recognize-status=1-success,other-failure"
  , "recognize-success=record-valid-and-reason-null"
  , "recognize-failure=record-null-and-grammar-specific-reason-valid"
  , "commit=phil_runtime_commit_ingress_<grammar>(ptr,ptr)->void"
  , "commit-arg0=exact-server-transport"
  , "commit-arg1=exact-pending-handle"
  , "failure-effect=phil_runtime_fail_recognition_<grammar>(ptr,ptr)->void"
  , "failure-effect-arg0=exact-pending-handle"
  , "failure-effect-arg1=exact-recognition-reason"
  , "destroy=phil_runtime_destroy_pending_<grammar>(ptr,ptr)->void"
  , "destroy-arg0=exact-pending-handle"
  , "destroy-arg1=exact-frame-handle"
  , "ambient-transport=forbidden"
  , "ambient-pending=forbidden"
  , "ambient-frame=forbidden"
  , "ambient-raw-view=forbidden"
  , "ambient-recognition-reason=forbidden"
  , "storage-failure-detail=outside-this-profile"
  ]

phase0ServerFramedIngressLLVMTarget :: LLVMTargetProfile
phase0ServerFramedIngressLLVMTarget = phase0ClientControlSendLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText serverFramedIngressABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/server-framed-ingress-v1"
  }

phase0ServerFramedIngressLLVMArtifact
  :: Either RecognitionFailureError LLVMArtifact
phase0ServerFramedIngressLLVMArtifact = do
  bundle <- phase0RecognitionFailureBundle
  pure (lowerSystemsServerFramedIngress
    phase0ServerFramedIngressLLVMTarget
    (recognitionFailureArtifact bundle))

phase0ServerFramedIngressLLVMVerificationContext
  :: RecognitionFailureBundle
  -> LLVMVerificationContext
phase0ServerFramedIngressLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = recognitionFailureContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0ServerFramedIngressLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0ServerFramedIngressLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0ServerFramedIngressLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0ServerFramedIngressLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0ServerFramedIngressLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0ServerFramedIngressLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

lowerSystemsServerFramedIngress :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsServerFramedIngress target systemsArtifact = artifact
  where
    base = lowerSystemsClientControlSend target systemsArtifact
    module0 = llvmArtifactModule base
    module1 = case Map.lookup serverFunctionName (systemsProgramFunctions (systemsArtifactProgram systemsArtifact)) of
      Nothing -> module0
      Just systemsServer -> module0
        { llvmFunctions = Map.adjust
            (rewriteServer systemsServer)
            serverFunctionName
            (llvmFunctions module0)
        }
    rewriteServer systemsServer llvmServer =
      foldl (rewriteWitness systemsServer) llvmServer phase0RecognitionFailureWitnesses

    contract0 = llvmArtifactContract base
    contract1 = contract0 { llvmContractTargetDigest = llvmModuleDigest module1 }
    artifact = base
      { llvmArtifactModule = module1
      , llvmArtifactText = renderLLVMModule module1
      , llvmArtifactContract = contract1
      }

rewriteWitness
  :: SystemsFunction
  -> LLVMFunction
  -> RecognitionFailureWitness
  -> LLVMFunction
rewriteWitness systemsServer llvmServer witness =
  case ingressShape systemsServer witness of
    Nothing -> llvmServer
    Just shape -> llvmServer
      { llvmFunctionBlocks =
          Map.adjust (rewriteRecognitionBlock shape)
            (LLVMBlockId (unBlockId (recognitionFailureRecognitionBlock witness))) $
          Map.adjust (rewriteCommitBlock shape)
            (LLVMBlockId (unBlockId (ingressSuccess shape))) $
          Map.adjust (rewriteFailureBlock shape)
            (LLVMBlockId (unBlockId (recognitionFailureFailureBlock witness)))
            (llvmFunctionBlocks llvmServer)
      }

rewriteRecognitionBlock :: IngressShape -> LLVMBlock -> LLVMBlock
rewriteRecognitionBlock shape blockValue = blockValue
  { llvmBlockOps = concatMap rewriteOp (llvmBlockOps blockValue)
  , llvmBlockTerminator = case llvmBlockTerminator blockValue of
      LLVMRecognizeRecord site grammar record yes no
        | grammar == ingressGrammar shape ->
            LLVMRecognizeRecordDetailed
              site
              grammar
              (unValueId (ingressPending shape))
              (unValueId (ingressRaw shape))
              record
              (unValueId (ingressReason shape))
              yes
              no
      other -> other
  }
  where
    rewriteOp operation = case operation of
      LLVMCall name
        | name == "receive_frame." <> ingressGrammar shape ->
            [ LLVMServerReceiveFrame
                (ingressGrammar shape)
                (unValueId (ingressPending shape))
                (unValueId (ingressFrame shape))
                (unValueId (ingressTransport shape))
            ]
      LLVMPlain description
        | description == "borrowed view; no representation copy" ->
            [ LLVMServerBorrowFrameView
                (ingressGrammar shape)
                (unValueId (ingressRaw shape))
                (unValueId (ingressFrame shape))
            ]
      _ -> [operation]

rewriteCommitBlock :: IngressShape -> LLVMBlock -> LLVMBlock
rewriteCommitBlock shape blockValue = blockValue
  { llvmBlockOps = map rewriteOp (llvmBlockOps blockValue) }
  where
    rewriteOp operation = case operation of
      LLVMPlain description
        | description == "commit recognized ingress into CFG typestate" ->
            LLVMServerCommitIngress
              (ingressGrammar shape)
              (unValueId (ingressTransport shape))
              (unValueId (ingressPending shape))
      _ -> operation

rewriteFailureBlock :: IngressShape -> LLVMBlock -> LLVMBlock
rewriteFailureBlock shape blockValue = blockValue
  { llvmBlockOps = concatMap rewriteOp (llvmBlockOps blockValue) }
  where
    rewriteOp operation = case operation of
      LLVMCall name
        | name == recognitionFailureMaterializeCall (ingressFailureWitness shape) -> []
        | name == recognitionFailureEffectCall (ingressFailureWitness shape) ->
            [ LLVMServerFailRecognition
                (ingressGrammar shape)
                (unValueId (ingressPending shape))
                (unValueId (ingressReason shape))
            ]
      LLVMCleanup description
        | description == "destroy pending ingress/frame" ->
            [ LLVMServerDestroyPending
                (ingressGrammar shape)
                (unValueId (ingressPending shape))
                (unValueId (ingressFrame shape))
            ]
      _ -> [operation]

data IngressShape = IngressShape
  { ingressGrammar :: Text
  , ingressTransport :: ValueId
  , ingressPending :: ValueId
  , ingressFrame :: ValueId
  , ingressRaw :: ValueId
  , ingressRecord :: ValueId
  , ingressReason :: ValueId
  , ingressSuccess :: BlockId
  , ingressFailure :: BlockId
  , ingressSite :: RuntimeSiteRef
  , ingressFailureWitness :: RecognitionFailureWitness
  }

ingressShape
  :: SystemsFunction
  -> RecognitionFailureWitness
  -> Maybe IngressShape
ingressShape function witness = do
  recognitionBlock <- Map.lookup
    (recognitionFailureRecognitionBlock witness)
    (systemsFunctionBlocks function)
  (pending, raw, site, success, failure) <- case systemsBlockTerminator recognitionBlock of
    TermRecognize p r s yes no -> Just (p, r, s, yes, no)
    _ -> Nothing
  (transport, frame) <- case
    [ (receiveTransport operation, receiveFrameOwner operation)
    | operation@OpReceiveFrame {} <- systemsBlockOps recognitionBlock
    , receivePending operation == pending
    , receiveGrammar operation == recognitionFailureGrammar witness
    ] of
      [entry] -> Just entry
      _ -> Nothing
  case
    [ ()
    | OpBorrowView view owner _ <- systemsBlockOps recognitionBlock
    , view == raw
    , owner == frame
    ] of
      [()] -> pure ()
      _ -> Nothing
  successBlock <- Map.lookup success (systemsFunctionBlocks function)
  record <- case
    [ output
    | OpRuntimeCall name [] [output] Nothing _ <- systemsBlockOps successBlock
    , name == "materialize recognized " <> recognitionFailureGrammar witness
    , Just SystemsValue { systemsValueRole = RuntimeRecord grammar } <-
        [Map.lookup output (systemsFunctionValues function)]
    , grammar == recognitionFailureGrammar witness
    ] of
      [value] -> Just value
      _ -> Nothing
  pure IngressShape
    { ingressGrammar = recognitionFailureGrammar witness
    , ingressTransport = transport
    , ingressPending = pending
    , ingressFrame = frame
    , ingressRaw = raw
    , ingressRecord = record
    , ingressReason = recognitionFailureReason witness
    , ingressSuccess = success
    , ingressFailure = failure
    , ingressSite = site
    , ingressFailureWitness = witness
    }

verifyServerFramedIngressTranslation
  :: RecognitionFailureBundle
  -> LLVMArtifact
  -> Either ServerFramedIngressLLVMError ()
verifyServerFramedIngressTranslation bundle llvmArtifact = do
  mapLeft ServerFramedIngressSystemsError (verifyRecognitionFailureBundle bundle)
  verifyServerFramedIngressLLVMWitnesses bundle llvmArtifact
  mapLeft ServerFramedIngressLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsServerFramedIngress
      (phase0ServerFramedIngressLLVMVerificationContext bundle)
      (recognitionFailureArtifact bundle)
      llvmArtifact

verifyServerFramedIngressLLVMWitnesses
  :: RecognitionFailureBundle
  -> LLVMArtifact
  -> Either ServerFramedIngressLLVMError ()
verifyServerFramedIngressLLVMWitnesses bundle llvmArtifact = do
  let systemsArtifact = recognitionFailureArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
  systemsServer <- lookupSystemsFunction systemsProgram serverFunctionName
  llvmServer <- lookupLLVMFunction llvmModule serverFunctionName
  let transportParameters =
        [ LLVMParameter (unValueId valueId) LLVMPointerParameter
        | (valueId, SystemsValue { systemsValueRole = TransportHandle }) <-
            Map.toAscList (systemsFunctionValues systemsServer)
        ]
  unless (all (`elem` llvmFunctionParameters llvmServer) transportParameters) $
    Left (ServerFramedIngressParameterMismatch (llvmFunctionParameters llvmServer))
  mapLeft ServerFramedIngressClientRegression $
    verifyClientControlSendLLVMWitness
      (recognitionFailurePredecessor bundle)
      llvmArtifact
  forM_ (recognitionFailureWitnesses bundle) $ \witness -> do
    shape <- case ingressShape systemsServer witness of
      Nothing -> Left (ServerFramedIngressIngressShapeMismatch
        serverFunctionName (recognitionFailureRecognitionBlock witness))
      Just value -> Right value
    verifyShape llvmServer shape
  verifyRendered (llvmArtifactText llvmArtifact) (recognitionFailureWitnesses bundle)

verifyShape
  :: LLVMFunction
  -> IngressShape
  -> Either ServerFramedIngressLLVMError ()
verifyShape llvmServer shape = do
  let recognitionId = LLVMBlockId
        (unBlockId (recognitionFailureRecognitionBlock (ingressFailureWitness shape)))
      commitId = LLVMBlockId (unBlockId (ingressSuccess shape))
      failureId = LLVMBlockId
        (unBlockId (recognitionFailureFailureBlock (ingressFailureWitness shape)))
  recognitionBlock <- lookupLLVMBlock serverFunctionName llvmServer recognitionId
  let expectedReceive = LLVMServerReceiveFrame
        (ingressGrammar shape)
        (unValueId (ingressPending shape))
        (unValueId (ingressFrame shape))
        (unValueId (ingressTransport shape))
      expectedBorrow = LLVMServerBorrowFrameView
        (ingressGrammar shape)
        (unValueId (ingressRaw shape))
        (unValueId (ingressFrame shape))
  unless
    (expectedReceive `elem` llvmBlockOps recognitionBlock
      && expectedBorrow `elem` llvmBlockOps recognitionBlock) $
    Left (ServerFramedIngressRecognitionOpsMismatch
      (ingressGrammar shape) recognitionId (llvmBlockOps recognitionBlock))
  let expectedTerminator = LLVMRecognizeRecordDetailed
        (ingressSite shape)
        (ingressGrammar shape)
        (unValueId (ingressPending shape))
        (unValueId (ingressRaw shape))
        (unValueId (ingressRecord shape))
        (unValueId (ingressReason shape))
        (LLVMBlockId (unBlockId (ingressSuccess shape)))
        (LLVMBlockId (unBlockId (ingressFailure shape)))
  unless (llvmBlockTerminator recognitionBlock == expectedTerminator) $
    Left (ServerFramedIngressRecognitionTerminatorMismatch
      (ingressGrammar shape) recognitionId (llvmBlockTerminator recognitionBlock))

  commitBlock <- lookupLLVMBlock serverFunctionName llvmServer commitId
  let expectedCommit = LLVMServerCommitIngress
        (ingressGrammar shape)
        (unValueId (ingressTransport shape))
        (unValueId (ingressPending shape))
  unless (expectedCommit `elem` llvmBlockOps commitBlock) $
    Left (ServerFramedIngressCommitMismatch
      (ingressGrammar shape) commitId (llvmBlockOps commitBlock))

  failureBlock <- lookupLLVMBlock serverFunctionName llvmServer failureId
  let expectedFailureOps =
        [ LLVMServerFailRecognition
            (ingressGrammar shape)
            (unValueId (ingressPending shape))
            (unValueId (ingressReason shape))
        , LLVMServerDestroyPending
            (ingressGrammar shape)
            (unValueId (ingressPending shape))
            (unValueId (ingressFrame shape))
        ]
      expectedFailureTerminator = LLVMReturn
        ("fatal:" <> recognitionFailureFatalClass (ingressFailureWitness shape))
  unless
    ( llvmBlockOps failureBlock == expectedFailureOps
      && llvmBlockTerminator failureBlock == expectedFailureTerminator
    ) $
    Left (ServerFramedIngressFailureMismatch
      (ingressGrammar shape)
      failureId
      (llvmBlockOps failureBlock)
      (llvmBlockTerminator failureBlock))

verifyRendered
  :: Text
  -> [RecognitionFailureWitness]
  -> Either ServerFramedIngressLLVMError ()
verifyRendered rendered witnesses = do
  forM_ witnesses $ \witness -> do
    let grammar = recognitionFailureGrammar witness
        suffix = symbolish grammar
        required =
          [ "declare void @phil_runtime_receive_frame_" <> suffix <> "(ptr, ptr, ptr)"
          , "declare ptr @phil_runtime_frame_borrow_view_" <> suffix <> "(ptr)"
          , "declare i8 @phil_runtime_recognize_" <> suffix <> "(ptr, ptr, ptr, ptr)"
          , "declare void @phil_runtime_commit_ingress_" <> suffix <> "(ptr, ptr)"
          , "declare void @phil_runtime_fail_recognition_" <> suffix <> "(ptr, ptr)"
          , "declare void @phil_runtime_destroy_pending_" <> suffix <> "(ptr, ptr)"
          ]
        forbidden =
          [ "@phil_call_receive_frame_" <> suffix <> "()"
          , "@phil_runtime_recognize_" <> suffix <> "()"
          , "@phil_call_materialize_recognition_failure_reason_" <> suffix <> "()"
          , "@phil_call_fail_recognition_" <> suffix <> "()"
          ]
    forM_ required $ \needle -> unless (Text.isInfixOf needle rendered) $
      Left (ServerFramedIngressRenderedPrimitiveMissing needle)
    forM_ forbidden $ \needle -> unless (not (Text.isInfixOf needle rendered)) $
      Left (ServerFramedIngressLegacyPrimitivePresent needle)
  forM_
    [ "current_transport"
    , "current_pending"
    , "current_frame"
    , "current_raw"
    , "current_reason"
    , "last_pending"
    , "last_frame"
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (ServerFramedIngressAmbientStatePresent needle)

verifyPhase0ServerFramedIngressLLVM
  :: Either ServerFramedIngressLLVMError ()
verifyPhase0ServerFramedIngressLLVM = do
  bundle <- mapLeft ServerFramedIngressSystemsError phase0RecognitionFailureBundle
  let artifact = lowerSystemsServerFramedIngress
        phase0ServerFramedIngressLLVMTarget
        (recognitionFailureArtifact bundle)
  verifyServerFramedIngressTranslation bundle artifact

lookupSystemsFunction
  :: SystemsProgram
  -> Text
  -> Either ServerFramedIngressLLVMError SystemsFunction
lookupSystemsFunction program functionName = case Map.lookup functionName (systemsProgramFunctions program) of
  Nothing -> Left (ServerFramedIngressSystemsFunctionMissing functionName)
  Just value -> Right value

lookupLLVMFunction
  :: LLVMModule
  -> Text
  -> Either ServerFramedIngressLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName = case Map.lookup functionName (llvmFunctions moduleValue) of
  Nothing -> Left (ServerFramedIngressLLVMFunctionMissing functionName)
  Just value -> Right value

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either ServerFramedIngressLLVMError LLVMBlock
lookupLLVMBlock functionName function blockId = case Map.lookup blockId (llvmFunctionBlocks function) of
  Nothing -> Left (ServerFramedIngressLLVMBlockMissing functionName blockId)
  Just value -> Right value

symbolish :: Text -> Text
symbolish = Text.map (\character ->
  if ('a' <= character && character <= 'z')
      || ('A' <= character && character <= 'Z')
      || ('0' <= character && character <= '9')
    then character
    else '_')

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
