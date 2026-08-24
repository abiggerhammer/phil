{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.StorageFailure
  ( StorageFailureWitness (..)
  , StorageFailureBundle (..)
  , StorageFailureError (..)
  , phase0StorageFailureWitness
  , phase0StorageFailureBundle
  , verifyStorageFailureBundle
  , verifyStorageFailureWitness
  ) where

import Control.Monad (unless, when)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.ClientOutbound
import Phil.Systems.Dataflow
import Phil.Systems.DigestValidation
import Phil.Systems.IR
import Phil.Systems.Storage
import Phil.Systems.Verify

data StorageFailureWitness = StorageFailureWitness
  { storageFailureFunction :: Text
  , storageFailureStoreBlock :: BlockId
  , storageFailureFailureBlock :: BlockId
  , storageFailureTransport :: ValueId
  , storageFailureOwner :: ValueId
  , storageFailureSuccessResult :: ValueId
  , storageFailureErrorValue :: ValueId
  , storageFailureMaterializeCall :: Text
  , storageFailureEffectCall :: Text
  , storageFailureFatalClass :: Text
  , storageFailureDecision :: DecisionId
  }
  deriving (Eq, Show)

data StorageFailureBundle = StorageFailureBundle
  { storageFailureArtifact :: SystemsArtifact
  , storageFailureContext :: SystemsVerificationContext
  , storageFailurePredecessor :: ClientOutboundBundle
  , storageFailureWitness :: StorageFailureWitness
  }
  deriving (Eq, Show)

data StorageFailureError
  = StorageFailurePredecessorError ClientOutboundError
  | StorageFailureStorageRegression StorageError
  | StorageFailureSystemsError SystemsVerificationError
  | StorageFailureDataflowError ScalarDataflowError
  | StorageFailureClientOutboundRegression ClientOutboundError
  | StorageFailureFunctionMissing Text
  | StorageFailureBlockMissing Text BlockId
  | StorageFailureValueMissing Text ValueId
  | StorageFailureValueRoleMismatch Text ValueId SystemsValueRole
  | StorageFailureUnexpectedValuePresent Text ValueId
  | StorageFailureStoreMismatch Text BlockId SystemsTerminator
  | StorageFailureLegacyBlockMismatch Text BlockId [SystemsOp] SystemsTerminator
  | StorageFailureFlowMismatch Text BlockId [SystemsOp] SystemsTerminator
  | StorageFailureErrorUseMismatch ValueId [(BlockId, Text)]
  | StorageFailurePayloadObservedAfterTransfer ValueId [(BlockId, Text)]
  | StorageFailureDecisionAlreadyPresent DecisionId
  | StorageFailureDecisionMissing DecisionId
  | StorageFailureDecisionMismatch DecisionId
  deriving (Eq, Show)

phase0StorageFailureWitness :: StorageFailureWitness
phase0StorageFailureWitness = StorageFailureWitness
  { storageFailureFunction = "UploadServer"
  , storageFailureStoreBlock = BlockId "server.store"
  , storageFailureFailureBlock = BlockId "server.storage_failure"
  , storageFailureTransport = ValueId "server.transport"
  , storageFailureOwner = ValueId "server.payload"
  , storageFailureSuccessResult = ValueId "server.upload_id"
  , storageFailureErrorValue = ValueId "server.storage_error"
  , storageFailureMaterializeCall = "materialize storage failure error"
  , storageFailureEffectCall = "fail internal storage"
  , storageFailureFatalClass = "StorageFailure"
  , storageFailureDecision = DecisionId "lower.storage.failure_detail"
  }

phase0StorageFailureBundle
  :: Either StorageFailureError StorageFailureBundle
phase0StorageFailureBundle = do
  predecessor <- mapLeft StorageFailurePredecessorError phase0ClientOutboundBundle
  let baseArtifact = clientOutboundArtifact predecessor
      baseContext = clientOutboundContext predecessor
      witness = phase0StorageFailureWitness
      predecessorDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
  mapLeft StorageFailureStorageRegression $
    verifyStorageWitness baseArtifact phase0DigestValidationWitness phase0StorageWitness
  when (Map.member (storageFailureDecision witness) predecessorDecisions) $
    Left (StorageFailureDecisionAlreadyPresent (storageFailureDecision witness))
  program <- materializeStorageFailure witness (systemsArtifactProgram baseArtifact)
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "store(payload) failure(err) -> dedicated storage-failure edge -> explicit server.storage_error -> exact fail internal storage effect"
            , "store consumes the payload on all outcomes; the failure detail is materialized without observing or releasing the transferred payload"
            ]
        , stageResourceFailureRelation = stageResourceFailureRelation baseContract <>
            [ "storage failure preserves the exact source error identity through the terminal internal-failure effect after payload ownership transfer"
            ]
        }
      sourceDigest = stageSourceArtifactDigest contract
      rebound = Map.map (rebindDecisionTarget targetDigest) predecessorDecisions
      decision = deriveStorageFailureDecision sourceDigest targetDigest witness
      decisions = Map.insert (storageFailureDecision witness) decision rebound
      loweringRoot = deriveLoweringLedgerRoot decisions
      artifact = SystemsArtifact program contract (LoweringLedger decisions loweringRoot)
      assuranceLedger = systemsAssuranceLedger baseContext
      baseManifest = systemsAssuranceManifest baseContext
      provisionalManifest = baseManifest
        { manifestImplementationDigest = systemsArtifactDigest artifact
        , manifestLoweringLedgerRoot = loweringRoot
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId assuranceLedger provisionalManifest }
      baseVerification = systemsAssuranceVerificationContext baseContext
      verification = baseVerification
        { verificationImplementationDigest = systemsArtifactDigest artifact
        , verificationLoweringLedgerRoot = loweringRoot
        }
      context = baseContext
        { systemsAssuranceManifest = manifest
        , systemsAssuranceVerificationContext = verification
        }
      bundle = StorageFailureBundle artifact context predecessor witness
  verifyStorageFailureBundle bundle
  pure bundle

verifyStorageFailureBundle
  :: StorageFailureBundle
  -> Either StorageFailureError ()
verifyStorageFailureBundle bundle = do
  mapLeft StorageFailurePredecessorError $
    verifyClientOutboundBundle (storageFailurePredecessor bundle)
  mapLeft StorageFailureSystemsError $
    verifySystemsArtifact
      (storageFailureContext bundle)
      (storageFailureArtifact bundle)
  mapLeft StorageFailureDataflowError $
    verifyScalarDataflow (storageFailureArtifact bundle)
  mapLeft StorageFailureClientOutboundRegression $
    verifyClientOutboundWitness
      (storageFailureArtifact bundle)
      phase0ClientOutboundWitness
  mapLeft StorageFailureStorageRegression $
    verifyStorageWitness
      (storageFailureArtifact bundle)
      phase0DigestValidationWitness
      phase0StorageWitness
  verifyStorageFailureWitness
    (storageFailureArtifact bundle)
    (storageFailureWitness bundle)
  let artifact = storageFailureArtifact bundle
      witness = storageFailureWitness bundle
      program = systemsArtifactProgram artifact
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest program
      decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      expected = deriveStorageFailureDecision sourceDigest targetDigest witness
  case Map.lookup (storageFailureDecision witness) decisions of
    Nothing -> Left (StorageFailureDecisionMissing (storageFailureDecision witness))
    Just actual -> unless (actual == expected) $
      Left (StorageFailureDecisionMismatch (storageFailureDecision witness))

verifyStorageFailureWitness
  :: SystemsArtifact
  -> StorageFailureWitness
  -> Either StorageFailureError ()
verifyStorageFailureWitness artifact witness = do
  let program = systemsArtifactProgram artifact
      functionName = storageFailureFunction witness
  function <- lookupFunction functionName program
  verifyRole functionName function
    (storageFailureTransport witness)
    TransportHandle
  verifyRole functionName function
    (storageFailureOwner witness)
    (OwnedBuffer "Bytes[begin.length]")
  verifyRole functionName function
    (storageFailureSuccessResult witness)
    (RuntimeScalar "UploadId")
  verifyRole functionName function
    (storageFailureErrorValue witness)
    (RuntimeOpaque "StorageError")

  storeBlock <- lookupBlock functionName function (storageFailureStoreBlock witness)
  case systemsBlockTerminator storeBlock of
    TermStore owner result site _success failure
      | owner == storageFailureOwner witness
          && result == storageFailureSuccessResult witness
          && runtimeSiteKind site == StorageBoundary
          && failure == storageFailureFailureBlock witness -> pure ()
    other -> Left (StorageFailureStoreMismatch
      functionName
      (storageFailureStoreBlock witness)
      other)

  failureBlock <- lookupBlock functionName function (storageFailureFailureBlock witness)
  unless
    ( systemsBlockOps failureBlock == expectedFailureOps witness
    && systemsBlockTerminator failureBlock == TermFatal (storageFailureFatalClass witness)
    ) $
    Left (StorageFailureFlowMismatch
      functionName
      (storageFailureFailureBlock witness)
      (systemsBlockOps failureBlock)
      (systemsBlockTerminator failureBlock))

  let errorUses = semanticUses (storageFailureErrorValue witness) function
      expectedErrorUses =
        [ (storageFailureFailureBlock witness,
            "runtime-call:" <> storageFailureEffectCall witness)
        ]
  unless (errorUses == expectedErrorUses) $
    Left (StorageFailureErrorUseMismatch
      (storageFailureErrorValue witness)
      errorUses)

  let payloadUses = semanticUsesInBlock
        (storageFailureOwner witness)
        (storageFailureFailureBlock witness)
        function
  unless (null payloadUses) $
    Left (StorageFailurePayloadObservedAfterTransfer
      (storageFailureOwner witness)
      payloadUses)

materializeStorageFailure
  :: StorageFailureWitness
  -> SystemsProgram
  -> Either StorageFailureError SystemsProgram
materializeStorageFailure witness program = do
  let functionName = storageFailureFunction witness
  function <- lookupFunction functionName program
  verifyRole functionName function
    (storageFailureTransport witness)
    TransportHandle
  verifyRole functionName function
    (storageFailureOwner witness)
    (OwnedBuffer "Bytes[begin.length]")
  verifyRole functionName function
    (storageFailureSuccessResult witness)
    (RuntimeScalar "UploadId")
  requireAbsent functionName function (storageFailureErrorValue witness)

  storeBlock <- lookupBlock functionName function (storageFailureStoreBlock witness)
  case systemsBlockTerminator storeBlock of
    TermStore owner result site _success failure
      | owner == storageFailureOwner witness
          && result == storageFailureSuccessResult witness
          && runtimeSiteKind site == StorageBoundary
          && failure == storageFailureFailureBlock witness -> pure ()
    other -> Left (StorageFailureStoreMismatch
      functionName
      (storageFailureStoreBlock witness)
      other)

  failureBlock <- lookupBlock functionName function (storageFailureFailureBlock witness)
  unless
    ( null (systemsBlockOps failureBlock)
    && systemsBlockTerminator failureBlock == TermFatal (storageFailureFatalClass witness)
    ) $
    Left (StorageFailureLegacyBlockMismatch
      functionName
      (storageFailureFailureBlock witness)
      (systemsBlockOps failureBlock)
      (systemsBlockTerminator failureBlock))

  let errorValue = SystemsValue
        (storageFailureErrorValue witness)
        (RuntimeOpaque "StorageError")
        Nothing
      failureBlock' = failureBlock
        { systemsBlockOps = expectedFailureOps witness }
      function' = function
        { systemsFunctionValues = Map.insert
            (storageFailureErrorValue witness)
            errorValue
            (systemsFunctionValues function)
        , systemsFunctionBlocks = Map.insert
            (storageFailureFailureBlock witness)
            failureBlock'
            (systemsFunctionBlocks function)
        }
  pure program
    { systemsProgramFunctions = Map.insert
        functionName function' (systemsProgramFunctions program)
    }

expectedFailureOps :: StorageFailureWitness -> [SystemsOp]
expectedFailureOps witness =
  [ OpRuntimeCall
      (storageFailureMaterializeCall witness)
      []
      [storageFailureErrorValue witness]
      Nothing
      (storageFailureDecision witness)
  , OpRuntimeCall
      (storageFailureEffectCall witness)
      [ storageFailureTransport witness
      , storageFailureErrorValue witness
      ]
      []
      Nothing
      (storageFailureDecision witness)
  ]

semanticUses :: ValueId -> SystemsFunction -> [(BlockId, Text)]
semanticUses valueId function = concatMap usesInBlock (Map.elems (systemsFunctionBlocks function))
  where
    usesInBlock blockValue =
      [ (systemsBlockId blockValue, "runtime-call:" <> name)
      | OpRuntimeCall name inputs _outputs _site _decision <- systemsBlockOps blockValue
      , valueId `elem` inputs
      ]

semanticUsesInBlock
  :: ValueId
  -> BlockId
  -> SystemsFunction
  -> [(BlockId, Text)]
semanticUsesInBlock valueId blockId function =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> []
    Just blockValue ->
      [ (blockId, describe operation)
      | operation <- systemsBlockOps blockValue
      , valueId `elem` operationInputs operation
      ]
  where
    describe operation = case operation of
      OpRuntimeCall { runtimeCallName = name } -> "runtime-call:" <> name
      OpSessionSelect { sessionSelectLabel = label } -> "session-select:" <> label
      OpReleaseOwner {} -> "release-owner"
      OpCleanupPartial {} -> "cleanup-partial"
      OpCopy {} -> "copy"
      OpBorrowView {} -> "borrow"
      _ -> "operation"

operationInputs :: SystemsOp -> [ValueId]
operationInputs operation = case operation of
  OpReceiveFrame pending frame transport _grammar _decision -> [pending, frame, transport]
  OpBorrowView _view owner _decision -> [owner]
  OpCommitIngress pending transport _decision -> [pending, transport]
  OpDestroyPending pending frame _decision -> [pending, frame]
  OpReleaseOwner owner _decision -> [owner]
  OpCleanupPartial owner _decision -> [owner]
  OpRuntimeCall _name inputs _outputs _site _decision -> inputs
  OpSessionSelect transport _label payload _decision -> transport : maybe [] pure payload
  OpCopy source _target _decision -> [source]
  OpEraseFact {} -> []
  OpDiagnostic {} -> []
  OpScalarLiteral {} -> []
  OpTraceEvent _ -> []

lookupFunction
  :: Text
  -> SystemsProgram
  -> Either StorageFailureError SystemsFunction
lookupFunction functionName program =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (StorageFailureFunctionMissing functionName)
    Just value -> Right value

lookupBlock
  :: Text
  -> SystemsFunction
  -> BlockId
  -> Either StorageFailureError SystemsBlock
lookupBlock functionName function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (StorageFailureBlockMissing functionName blockId)
    Just value -> Right value

verifyRole
  :: Text
  -> SystemsFunction
  -> ValueId
  -> SystemsValueRole
  -> Either StorageFailureError ()
verifyRole functionName function valueId expected =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (StorageFailureValueMissing functionName valueId)
    Just value -> unless (systemsValueRole value == expected) $
      Left (StorageFailureValueRoleMismatch
        functionName valueId (systemsValueRole value))

requireAbsent
  :: Text
  -> SystemsFunction
  -> ValueId
  -> Either StorageFailureError ()
requireAbsent functionName function valueId =
  when (Map.member valueId (systemsFunctionValues function)) $
    Left (StorageFailureUnexpectedValuePresent functionName valueId)

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = lowering { loweringTargetArtifactDigest = targetDigest }

deriveStorageFailureDecision
  :: Digest
  -> Digest
  -> StorageFailureWitness
  -> LoweringDecision
deriveStorageFailureDecision sourceDigest targetDigest witness = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = LoweringDecision
      { loweringDecisionId = storageFailureDecision witness
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation =
          "store(payload) failure(err) source arm followed by fail internal(err) on session5"
      , loweringTargetRepresentation =
          "dedicated storage-failure edge with explicit opaque StorageError and exact terminal internal-failure forwarding effect"
      , loweringSemanticEntities =
          [ "function:" <> storageFailureFunction witness
          , "store-block:" <> unBlockId (storageFailureStoreBlock witness)
          , "failure-block:" <> unBlockId (storageFailureFailureBlock witness)
          , "error:" <> unValueId (storageFailureErrorValue witness)
          , "transport:" <> unValueId (storageFailureTransport witness)
          ]
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = Materialize
      , loweringRepresentationBefore =
          "storage failure represented only by the TermStore failure edge and StorageFailure fatal class"
      , loweringRepresentationAfter =
          "storage failure edge binds opaque error identity, forwards it once into the exact internal-failure effect, and does not regain payload ownership"
      , loweringInvariantsPreserved =
          [ "digest success remains the only predecessor of store"
          , "store consumes payload ownership on all outcomes"
          , "accepted remains reachable only from store success"
          , "storage failure remains terminal"
          , "transferred payload is not observed or released on the failure edge"
          ]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue =
          [ "physical storage target must surface the exact failure error identity on failure"
          , "concrete StorageError representation and lifetime remain target/runtime choices"
          , "fatal internal-error reporting ABI remains unselected"
          ]
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costCodeSize = Just "one failure-only semantic error binding and forwarding effect"
          , costFrequency = Just "once per storage failure"
          }
      , loweringTargetPreconditions =
          [ "error materialization occurs only on the unique TermStore failure edge"
          , "payload ownership has already transferred to store before the failure arm executes"
          ]
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "verify the storage failure edge binds exactly server.storage_error"
          , "verify server.storage_error is forwarded exactly once to fail internal storage"
          , "verify no failure-edge operation observes, releases, or copies server.payload"
          , "verify the TermStore site, owner, success result, and success/failure targets are unchanged"
          ]
      }

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
