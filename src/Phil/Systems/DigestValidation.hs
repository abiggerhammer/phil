{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.DigestValidation
  ( DigestValidationWitness (..)
  , DigestValidationBundle (..)
  , DigestValidationError (..)
  , phase0DigestValidationWitness
  , phase0DigestValidationBundle
  , verifyDigestValidationBundle
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.IR
import Phil.Systems.RecognizedRecord
import Phil.Systems.Verify

data DigestValidationWitness = DigestValidationWitness
  { digestValidationFunction :: Text
  , digestValidationBlock :: BlockId
  , digestValidationRecord :: ValueId
  , digestValidationRecordGrammar :: Text
  , digestValidationPayloadOwner :: ValueId
  , digestValidationPayloadView :: ValueId
  }
  deriving (Eq, Show)

data DigestValidationBundle = DigestValidationBundle
  { digestValidationArtifact :: SystemsArtifact
  , digestValidationContext :: SystemsVerificationContext
  , digestValidationRecognizedRecordBundle :: RecognizedRecordBundle
  , digestValidationWitness :: DigestValidationWitness
  }
  deriving (Eq, Show)

data DigestValidationError
  = DigestValidationRecognizedRecordError RecognizedRecordError
  | DigestValidationSystemsError SystemsVerificationError
  | DigestValidationFunctionMissing Text
  | DigestValidationBlockMissing Text BlockId
  | DigestValidationRecordMissing Text ValueId
  | DigestValidationRecordRoleMismatch Text ValueId SystemsValueRole
  | DigestValidationPayloadMissing Text ValueId
  | DigestValidationPayloadRoleMismatch Text ValueId SystemsValueRole
  | DigestValidationViewMissing Text ValueId
  | DigestValidationViewRoleMismatch Text ValueId ValueId SystemsValueRole
  | DigestValidationBorrowMismatch Text BlockId [SystemsOp]
  | DigestValidationCheckMismatch Text BlockId SystemsTerminator
  deriving (Eq, Show)

phase0DigestValidationWitness :: DigestValidationWitness
phase0DigestValidationWitness = DigestValidationWitness
  { digestValidationFunction = "UploadServer"
  , digestValidationBlock = BlockId "server.digest"
  , digestValidationRecord = ValueId "server.begin"
  , digestValidationRecordGrammar = "Begin"
  , digestValidationPayloadOwner = ValueId "server.payload"
  , digestValidationPayloadView = ValueId "server.payload_view"
  }

phase0DigestValidationBundle :: Either DigestValidationError DigestValidationBundle
phase0DigestValidationBundle = do
  recognizedBundle <- mapLeft
    DigestValidationRecognizedRecordError
    phase0RecognizedRecordBundle
  let baseArtifact = recognizedRecordArtifact recognizedBundle
      baseContext = recognizedRecordContext recognizedBundle
      witness = phase0DigestValidationWitness
  program <- materializeDigestSubjects witness (systemsArtifactProgram baseArtifact)
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "DigestMatches(begin, payloadView) -> explicit server.begin + server.payload_view runtime-check subjects"
            ]
        }
      baseDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
      decisions = Map.map (rebindDecisionTarget targetDigest) baseDecisions
      loweringRoot = deriveLoweringLedgerRoot decisions
      loweringLedger = LoweringLedger
        { loweringLedgerDecisions = decisions
        , loweringLedgerRoot = loweringRoot
        }
      artifact = SystemsArtifact
        { systemsArtifactProgram = program
        , systemsArtifactStageContract = contract
        , systemsArtifactLoweringLedger = loweringLedger
        }
      assuranceLedger = systemsAssuranceLedger baseContext
      baseManifest = systemsAssuranceManifest baseContext
      provisionalManifest = baseManifest
        { manifestImplementationDigest = systemsArtifactDigest artifact
        , manifestLoweringLedgerRoot = loweringRoot
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId assuranceLedger provisionalManifest }
      baseAssuranceContext = systemsAssuranceVerificationContext baseContext
      assuranceContext = baseAssuranceContext
        { verificationImplementationDigest = systemsArtifactDigest artifact
        , verificationLoweringLedgerRoot = loweringRoot
        }
      systemsContext = baseContext
        { systemsAssuranceManifest = manifest
        , systemsAssuranceVerificationContext = assuranceContext
        }
      reboundRecognizedBundle = recognizedBundle
        { recognizedRecordArtifact = artifact
        , recognizedRecordContext = systemsContext
        }
      bundle = DigestValidationBundle
        { digestValidationArtifact = artifact
        , digestValidationContext = systemsContext
        , digestValidationRecognizedRecordBundle = reboundRecognizedBundle
        , digestValidationWitness = witness
        }
  verifyDigestValidationBundle bundle
  Right bundle

verifyDigestValidationBundle
  :: DigestValidationBundle
  -> Either DigestValidationError ()
verifyDigestValidationBundle bundle = do
  mapLeft DigestValidationSystemsError $
    verifySystemsArtifact
      (digestValidationContext bundle)
      (digestValidationArtifact bundle)
  mapLeft DigestValidationRecognizedRecordError $
    verifyRecognizedRecordBundle (digestValidationRecognizedRecordBundle bundle)
  verifyWitness
    (digestValidationArtifact bundle)
    (digestValidationWitness bundle)

verifyWitness
  :: SystemsArtifact
  -> DigestValidationWitness
  -> Either DigestValidationError ()
verifyWitness artifact witness = do
  let program = systemsArtifactProgram artifact
      functionName = digestValidationFunction witness
  function <- case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (DigestValidationFunctionMissing functionName)
    Just value -> Right value

  record <- lookupValue functionName function (digestValidationRecord witness)
    DigestValidationRecordMissing
  case systemsValueRole record of
    RuntimeRecord grammar
      | grammar == digestValidationRecordGrammar witness -> pure ()
    other -> Left (DigestValidationRecordRoleMismatch
      functionName
      (digestValidationRecord witness)
      other)

  payload <- lookupValue functionName function (digestValidationPayloadOwner witness)
    DigestValidationPayloadMissing
  case systemsValueRole payload of
    OwnedBuffer _ -> pure ()
    other -> Left (DigestValidationPayloadRoleMismatch
      functionName
      (digestValidationPayloadOwner witness)
      other)

  payloadView <- lookupValue functionName function (digestValidationPayloadView witness)
    DigestValidationViewMissing
  case systemsValueRole payloadView of
    BorrowedSlice owner
      | owner == digestValidationPayloadOwner witness -> pure ()
    other -> Left (DigestValidationViewRoleMismatch
      functionName
      (digestValidationPayloadView witness)
      (digestValidationPayloadOwner witness)
      other)

  blockValue <- case Map.lookup
      (digestValidationBlock witness)
      (systemsFunctionBlocks function) of
    Nothing -> Left (DigestValidationBlockMissing
      functionName
      (digestValidationBlock witness))
    Just value -> Right value

  let matchingBorrows =
        [ operation
        | operation@OpBorrowView
            { borrowView = view
            , borrowOwner = owner
            } <- systemsBlockOps blockValue
        , view == digestValidationPayloadView witness
        , owner == digestValidationPayloadOwner witness
        ]
  unless (length matchingBorrows == 1) $
    Left (DigestValidationBorrowMismatch
      functionName
      (digestValidationBlock witness)
      (systemsBlockOps blockValue))

  case systemsBlockTerminator blockValue of
    TermRuntimeCheck
      { checkInputs = inputs
      , checkSite = site
      }
      | inputs ==
          [ digestValidationRecord witness
          , digestValidationPayloadView witness
          ]
          && runtimeSiteKind site == DigestBoundary -> pure ()
    terminator -> Left (DigestValidationCheckMismatch
      functionName
      (digestValidationBlock witness)
      terminator)

lookupValue
  :: Text
  -> SystemsFunction
  -> ValueId
  -> (Text -> ValueId -> DigestValidationError)
  -> Either DigestValidationError SystemsValue
lookupValue functionName function valueId missing =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (missing functionName valueId)
    Just value -> Right value

materializeDigestSubjects
  :: DigestValidationWitness
  -> SystemsProgram
  -> Either DigestValidationError SystemsProgram
materializeDigestSubjects witness program = do
  let functionName = digestValidationFunction witness
  function <- case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (DigestValidationFunctionMissing functionName)
    Just value -> Right value
  blockValue <- case Map.lookup
      (digestValidationBlock witness)
      (systemsFunctionBlocks function) of
    Nothing -> Left (DigestValidationBlockMissing
      functionName
      (digestValidationBlock witness))
    Just value -> Right value
  terminator <- case systemsBlockTerminator blockValue of
    value@TermRuntimeCheck { checkSite = site }
      | runtimeSiteKind site == DigestBoundary -> Right value
    other -> Left (DigestValidationCheckMismatch
      functionName
      (digestValidationBlock witness)
      other)
  let blockValue' = blockValue
        { systemsBlockTerminator = terminator
            { checkInputs =
                [ digestValidationRecord witness
                , digestValidationPayloadView witness
                ]
            }
        }
      function' = function
        { systemsFunctionBlocks = Map.insert
            (digestValidationBlock witness)
            blockValue'
            (systemsFunctionBlocks function)
        }
  Right program
    { systemsProgramFunctions = Map.insert
        functionName
        function'
        (systemsProgramFunctions program)
    }

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = lowering { loweringTargetArtifactDigest = targetDigest }

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
