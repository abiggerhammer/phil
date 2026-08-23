{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.HelloPolicyValidation
  ( HelloPolicyValidationWitness (..)
  , HelloPolicyValidationBundle (..)
  , HelloPolicyValidationError (..)
  , phase0HelloPolicyValidationWitness
  , phase0HelloPolicyValidationBundle
  , verifyHelloPolicyValidationBundle
  , verifyHelloPolicyValidationWitness
  ) where

import Control.Monad (unless, when)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.BeginPolicySessionChoice
import Phil.Systems.Dataflow
import Phil.Systems.IR
import Phil.Systems.Verify
import Phil.Systems.VersionChoiceOperands

data HelloPolicyValidationWitness = HelloPolicyValidationWitness
  { helloPolicyServerFunction :: Text
  , helloPolicyServerTransport :: ValueId
  , helloPolicyCommitBlock :: BlockId
  , helloPolicyHelloRecord :: ValueId
  , helloPolicyPolicyContext :: ValueId
  , helloPolicyRejectReason :: ValueId
  , helloPolicyRuntimeChoiceName :: Text
  , helloPolicyAcceptedArm :: Text
  , helloPolicyRejectedArm :: Text
  , helloPolicyAcceptedTarget :: BlockId
  , helloPolicyRejectedTarget :: BlockId
  , helloPolicyFailureCall :: Text
  , helloPolicyFailureClass :: Text
  , helloPolicyLoweringDecision :: DecisionId
  }
  deriving (Eq, Show)

data HelloPolicyValidationBundle = HelloPolicyValidationBundle
  { helloPolicyValidationArtifact :: SystemsArtifact
  , helloPolicyValidationContext :: SystemsVerificationContext
  , helloPolicyValidationPredecessor :: BeginPolicySessionChoiceBundle
  , helloPolicyValidationWitness :: HelloPolicyValidationWitness
  }
  deriving (Eq, Show)

data HelloPolicyValidationError
  = HelloPolicyPredecessorError BeginPolicySessionChoiceError
  | HelloPolicySystemsError SystemsVerificationError
  | HelloPolicyDataflowError ScalarDataflowError
  | HelloPolicyBeginPolicyRegression BeginPolicySessionChoiceError
  | HelloPolicyVersionOperandsRegression VersionChoiceOperandsError
  | HelloPolicyFunctionMissing Text
  | HelloPolicyBlockMissing Text BlockId
  | HelloPolicyValueMissing Text ValueId
  | HelloPolicyValueRoleMismatch Text ValueId SystemsValueRole
  | HelloPolicyUnexpectedValuePresent Text ValueId
  | HelloPolicyInputHasProducer Text ValueId
  | HelloPolicyRuntimeChoiceMismatch Text BlockId SystemsTerminator
  | HelloPolicyRuntimeSiteChanged RuntimeSiteRef RuntimeSiteRef
  | HelloPolicyFailureMismatch Text BlockId [SystemsOp] SystemsTerminator
  | HelloPolicyReasonUseMismatch ValueId [(BlockId, Text)]
  | HelloPolicyDecisionAlreadyPresent DecisionId
  | HelloPolicyDecisionMissing DecisionId
  | HelloPolicyDecisionMismatch DecisionId
  deriving (Eq, Show)

phase0HelloPolicyValidationWitness :: HelloPolicyValidationWitness
phase0HelloPolicyValidationWitness = HelloPolicyValidationWitness
  { helloPolicyServerFunction = "UploadServer"
  , helloPolicyServerTransport = ValueId "server.transport"
  , helloPolicyCommitBlock = BlockId "server.hello.commit"
  , helloPolicyHelloRecord = ValueId "server.hello"
  , helloPolicyPolicyContext = ValueId "server.policy_context"
  , helloPolicyRejectReason = ValueId "server.hello_reject_reason"
  , helloPolicyRuntimeChoiceName = "validate HelloPolicy"
  , helloPolicyAcceptedArm = "accepted"
  , helloPolicyRejectedArm = "rejected"
  , helloPolicyAcceptedTarget = BlockId "server.version.choose"
  , helloPolicyRejectedTarget = BlockId "server.hello.policy_failure"
  , helloPolicyFailureCall = "fail validation HelloPolicy"
  , helloPolicyFailureClass = "ValidationFailure[HelloPolicy]"
  , helloPolicyLoweringDecision = DecisionId "lower.runtime.hello_policy_validation"
  }

phase0HelloPolicyValidationBundle
  :: Either HelloPolicyValidationError HelloPolicyValidationBundle
phase0HelloPolicyValidationBundle = do
  predecessor <- mapLeft HelloPolicyPredecessorError phase0BeginPolicySessionChoiceBundle
  let baseArtifact = beginPolicySessionChoiceArtifact predecessor
      baseContext = beginPolicySessionChoiceContext predecessor
      witness = phase0HelloPolicyValidationWitness
      predecessorDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
  when (Map.member (helloPolicyLoweringDecision witness) predecessorDecisions) $
    Left (HelloPolicyDecisionAlreadyPresent (helloPolicyLoweringDecision witness))
  predecessorSite <- extractPredecessorRuntimeSite baseArtifact witness
  program <- materializeHelloPolicyValidation witness (systemsArtifactProgram baseArtifact)
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "HelloPolicy validation preserves its exact runtime site while exposing accepted/rejected(reason) as a local semantic choice"
            , "the rejected HelloPolicy reason is carried into the exact terminal validation-failure effect without selecting physical reason representation"
            ]
        }
      sourceDigest = stageSourceArtifactDigest contract
      rebound = Map.map (rebindDecisionTarget targetDigest) predecessorDecisions
      decision = deriveHelloPolicyDecision sourceDigest targetDigest predecessorSite witness
      decisions = Map.insert (helloPolicyLoweringDecision witness) decision rebound
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
      bundle = HelloPolicyValidationBundle artifact context predecessor witness
  verifyHelloPolicyValidationBundle bundle
  pure bundle

verifyHelloPolicyValidationBundle
  :: HelloPolicyValidationBundle
  -> Either HelloPolicyValidationError ()
verifyHelloPolicyValidationBundle bundle = do
  mapLeft HelloPolicyPredecessorError $
    verifyBeginPolicySessionChoiceBundle (helloPolicyValidationPredecessor bundle)
  mapLeft HelloPolicySystemsError $
    verifySystemsArtifact
      (helloPolicyValidationContext bundle)
      (helloPolicyValidationArtifact bundle)
  mapLeft HelloPolicyDataflowError $
    verifyScalarDataflow (helloPolicyValidationArtifact bundle)
  mapLeft HelloPolicyBeginPolicyRegression $
    verifyBeginPolicySessionChoiceWitness
      (helloPolicyValidationArtifact bundle)
      phase0BeginPolicySessionChoiceWitness
  mapLeft HelloPolicyVersionOperandsRegression $
    verifyVersionChoiceOperandsWitness
      (helloPolicyValidationArtifact bundle)
      phase0VersionChoiceOperandsWitness
  let witness = helloPolicyValidationWitness bundle
  predecessorSite <- extractPredecessorRuntimeSite
    (beginPolicySessionChoiceArtifact (helloPolicyValidationPredecessor bundle))
    witness
  successorSite <- extractSuccessorRuntimeSite
    (helloPolicyValidationArtifact bundle)
    witness
  unless (predecessorSite == successorSite) $
    Left (HelloPolicyRuntimeSiteChanged predecessorSite successorSite)
  verifyHelloPolicyValidationWitness
    (helloPolicyValidationArtifact bundle)
    witness

verifyHelloPolicyValidationWitness
  :: SystemsArtifact
  -> HelloPolicyValidationWitness
  -> Either HelloPolicyValidationError ()
verifyHelloPolicyValidationWitness artifact witness = do
  let program = systemsArtifactProgram artifact
  server <- lookupFunction (helloPolicyServerFunction witness) program
  verifyRole server witness (helloPolicyServerTransport witness) TransportHandle
  verifyRole server witness (helloPolicyHelloRecord witness) (RuntimeRecord "Hello")
  verifyRole server witness (helloPolicyPolicyContext witness) (RuntimeInput "PolicyContext")
  verifyRole server witness (helloPolicyRejectReason witness)
    (RuntimeOpaque "ValidationReason[HelloPolicy]")

  when (valueHasProducer server (helloPolicyPolicyContext witness)) $
    Left (HelloPolicyInputHasProducer
      (helloPolicyServerFunction witness)
      (helloPolicyPolicyContext witness))

  commitBlock <- lookupBlock server witness (helloPolicyCommitBlock witness)
  case systemsBlockTerminator commitBlock of
    TermRuntimeChoice name inputs (Just site) arms
      | name == helloPolicyRuntimeChoiceName witness
          && inputs == [helloPolicyPolicyContext witness, helloPolicyHelloRecord witness]
          && runtimeSiteKind site == ValidationBoundary "HelloPolicy"
          && arms == expectedRuntimeArms witness -> pure ()
    other -> Left (HelloPolicyRuntimeChoiceMismatch
      (helloPolicyServerFunction witness)
      (helloPolicyCommitBlock witness)
      other)

  failureBlock <- lookupBlock server witness (helloPolicyRejectedTarget witness)
  let expectedFailureOp = OpRuntimeCall
        (helloPolicyFailureCall witness)
        [helloPolicyServerTransport witness, helloPolicyRejectReason witness]
        []
        Nothing
        (helloPolicyLoweringDecision witness)
  unless
    ( systemsBlockOps failureBlock == [expectedFailureOp]
    && systemsBlockTerminator failureBlock == TermFatal (helloPolicyFailureClass witness)
    ) $
    Left (HelloPolicyFailureMismatch
      (helloPolicyServerFunction witness)
      (helloPolicyRejectedTarget witness)
      (systemsBlockOps failureBlock)
      (systemsBlockTerminator failureBlock))

  let uses = semanticUsesOf (helloPolicyRejectReason witness) server
      expectedUses =
        [ (helloPolicyRejectedTarget witness, "runtime-call:" <> helloPolicyFailureCall witness) ]
  unless (uses == expectedUses) $
    Left (HelloPolicyReasonUseMismatch (helloPolicyRejectReason witness) uses)

  let decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest program
  site <- extractSuccessorRuntimeSite artifact witness
  let expectedDecision = deriveHelloPolicyDecision sourceDigest targetDigest site witness
  case Map.lookup (helloPolicyLoweringDecision witness) decisions of
    Nothing -> Left (HelloPolicyDecisionMissing (helloPolicyLoweringDecision witness))
    Just actual -> unless (actual == expectedDecision) $
      Left (HelloPolicyDecisionMismatch (helloPolicyLoweringDecision witness))

materializeHelloPolicyValidation
  :: HelloPolicyValidationWitness
  -> SystemsProgram
  -> Either HelloPolicyValidationError SystemsProgram
materializeHelloPolicyValidation witness program = do
  server <- lookupFunction (helloPolicyServerFunction witness) program
  commitBlock <- lookupBlock server witness (helloPolicyCommitBlock witness)
  failureBlock <- lookupBlock server witness (helloPolicyRejectedTarget witness)

  verifyRole server witness (helloPolicyServerTransport witness) TransportHandle
  verifyRole server witness (helloPolicyHelloRecord witness) (RuntimeRecord "Hello")
  verifyRole server witness (helloPolicyPolicyContext witness) (RuntimeInput "PolicyContext")
  requireAbsent server witness (helloPolicyRejectReason witness)

  site <- case systemsBlockTerminator commitBlock of
    TermRuntimeCheck [] runtimeSite yes no
      | runtimeSiteKind runtimeSite == ValidationBoundary "HelloPolicy"
          && yes == helloPolicyAcceptedTarget witness
          && no == helloPolicyRejectedTarget witness -> Right runtimeSite
    other -> Left (HelloPolicyRuntimeChoiceMismatch
      (helloPolicyServerFunction witness)
      (helloPolicyCommitBlock witness)
      other)

  unless
    ( null (systemsBlockOps failureBlock)
    && systemsBlockTerminator failureBlock == TermFatal (helloPolicyFailureClass witness)
    ) $
    Left (HelloPolicyFailureMismatch
      (helloPolicyServerFunction witness)
      (helloPolicyRejectedTarget witness)
      (systemsBlockOps failureBlock)
      (systemsBlockTerminator failureBlock))

  let commitBlock' = commitBlock
        { systemsBlockTerminator = TermRuntimeChoice
            (helloPolicyRuntimeChoiceName witness)
            [helloPolicyPolicyContext witness, helloPolicyHelloRecord witness]
            (Just site)
            (expectedRuntimeArms witness)
        }
      failureBlock' = failureBlock
        { systemsBlockOps =
            [ OpRuntimeCall
                (helloPolicyFailureCall witness)
                [helloPolicyServerTransport witness, helloPolicyRejectReason witness]
                []
                Nothing
                (helloPolicyLoweringDecision witness)
            ]
        }
      serverValues = Map.insert
        (helloPolicyRejectReason witness)
        (SystemsValue
          (helloPolicyRejectReason witness)
          (RuntimeOpaque "ValidationReason[HelloPolicy]")
          Nothing)
        (systemsFunctionValues server)
      server' = server
        { systemsFunctionValues = serverValues
        , systemsFunctionBlocks = Map.insert
            (helloPolicyRejectedTarget witness) failureBlock' $
            Map.insert
              (helloPolicyCommitBlock witness) commitBlock'
              (systemsFunctionBlocks server)
        }
      functions' = Map.insert
        (helloPolicyServerFunction witness)
        server'
        (systemsProgramFunctions program)
  pure program { systemsProgramFunctions = functions' }

expectedRuntimeArms
  :: HelloPolicyValidationWitness
  -> Map.Map Text SystemsRuntimeChoiceArm
expectedRuntimeArms witness = Map.fromList
  [ ( helloPolicyAcceptedArm witness
    , SystemsRuntimeChoiceArm Nothing (helloPolicyAcceptedTarget witness)
    )
  , ( helloPolicyRejectedArm witness
    , SystemsRuntimeChoiceArm
        (Just (helloPolicyRejectReason witness))
        (helloPolicyRejectedTarget witness)
    )
  ]

extractPredecessorRuntimeSite
  :: SystemsArtifact
  -> HelloPolicyValidationWitness
  -> Either HelloPolicyValidationError RuntimeSiteRef
extractPredecessorRuntimeSite artifact witness = do
  server <- lookupFunction
    (helloPolicyServerFunction witness)
    (systemsArtifactProgram artifact)
  blockValue <- lookupBlock server witness (helloPolicyCommitBlock witness)
  case systemsBlockTerminator blockValue of
    TermRuntimeCheck [] site yes no
      | runtimeSiteKind site == ValidationBoundary "HelloPolicy"
          && yes == helloPolicyAcceptedTarget witness
          && no == helloPolicyRejectedTarget witness -> Right site
    other -> Left (HelloPolicyRuntimeChoiceMismatch
      (helloPolicyServerFunction witness)
      (helloPolicyCommitBlock witness)
      other)

extractSuccessorRuntimeSite
  :: SystemsArtifact
  -> HelloPolicyValidationWitness
  -> Either HelloPolicyValidationError RuntimeSiteRef
extractSuccessorRuntimeSite artifact witness = do
  server <- lookupFunction
    (helloPolicyServerFunction witness)
    (systemsArtifactProgram artifact)
  blockValue <- lookupBlock server witness (helloPolicyCommitBlock witness)
  case systemsBlockTerminator blockValue of
    TermRuntimeChoice name _ (Just site) arms
      | name == helloPolicyRuntimeChoiceName witness
          && arms == expectedRuntimeArms witness -> Right site
    other -> Left (HelloPolicyRuntimeChoiceMismatch
      (helloPolicyServerFunction witness)
      (helloPolicyCommitBlock witness)
      other)

semanticUsesOf :: ValueId -> SystemsFunction -> [(BlockId, Text)]
semanticUsesOf valueId function = concatMap blockUses (Map.elems (systemsFunctionBlocks function))
  where
    blockUses blockValue = operationUsesInBlock blockValue <> terminatorUsesInBlock blockValue
    operationUsesInBlock blockValue =
      [ (systemsBlockId blockValue, description operation)
      | operation <- systemsBlockOps blockValue
      , valueId `elem` operationInputs operation
      ]
    terminatorUsesInBlock blockValue =
      [ (systemsBlockId blockValue, "terminator")
      | valueId `elem` terminatorInputs (systemsBlockTerminator blockValue)
      ]
    description operation = case operation of
      OpRuntimeCall { runtimeCallName = name } -> "runtime-call:" <> name
      OpSessionSelect { sessionSelectLabel = label } -> "session-select:" <> label
      OpCopy {} -> "copy"
      _ -> "operation"

operationInputs :: SystemsOp -> [ValueId]
operationInputs operation = case operation of
  OpReceiveFrame { receivePending = pending, receiveFrameOwner = frame, receiveTransport = transport } ->
    [pending, frame, transport]
  OpBorrowView { borrowOwner = owner } -> [owner]
  OpCommitIngress { commitPending = pending, commitTransport = transport } -> [pending, transport]
  OpDestroyPending { destroyPending = pending, destroyFrameOwner = frame } -> [pending, frame]
  OpReleaseOwner { releaseOwner = owner } -> [owner]
  OpCleanupPartial { cleanupOwner = owner } -> [owner]
  OpRuntimeCall { runtimeCallInputs = inputs } -> inputs
  OpSessionSelect { sessionSelectTransport = transport, sessionSelectPayload = payload } ->
    transport : maybe [] pure payload
  OpCopy { copySource = source } -> [source]
  OpEraseFact {} -> []
  OpDiagnostic {} -> []
  OpScalarLiteral {} -> []
  OpTraceEvent _ -> []

terminatorInputs :: SystemsTerminator -> [ValueId]
terminatorInputs terminator = case terminator of
  TermBranch condition _ _ -> [condition]
  TermRecognize { recognizePending = pending, recognizeRawView = view } -> [pending, view]
  TermRuntimeCheck { checkInputs = inputs } -> inputs
  TermReceiveExact { exactTransport = transport, exactLength = lengthValue, exactPayloadOwner = owner } ->
    [transport, lengthValue, owner]
  TermSendExact { sendExactTransport = transport, sendExactOwner = owner } -> [transport, owner]
  TermStore { storeOwner = owner, storeResult = result } -> [owner, result]
  TermSessionOffer { sessionOfferTransport = transport } -> [transport]
  TermRuntimeChoice { runtimeChoiceInputs = inputs } -> inputs
  TermReturnScalar valueId -> [valueId]
  TermJump _ -> []
  TermEnd _ -> []
  TermFatal _ -> []

verifyRole
  :: SystemsFunction
  -> HelloPolicyValidationWitness
  -> ValueId
  -> SystemsValueRole
  -> Either HelloPolicyValidationError ()
verifyRole function witness valueId expected =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (HelloPolicyValueMissing (helloPolicyServerFunction witness) valueId)
    Just SystemsValue { systemsValueRole = actual }
      | actual == expected -> pure ()
      | otherwise -> Left (HelloPolicyValueRoleMismatch
          (helloPolicyServerFunction witness) valueId actual)

requireAbsent
  :: SystemsFunction
  -> HelloPolicyValidationWitness
  -> ValueId
  -> Either HelloPolicyValidationError ()
requireAbsent function witness valueId =
  when (Map.member valueId (systemsFunctionValues function)) $
    Left (HelloPolicyUnexpectedValuePresent (helloPolicyServerFunction witness) valueId)

lookupFunction
  :: Text
  -> SystemsProgram
  -> Either HelloPolicyValidationError SystemsFunction
lookupFunction functionName program =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (HelloPolicyFunctionMissing functionName)
    Just function -> Right function

lookupBlock
  :: SystemsFunction
  -> HelloPolicyValidationWitness
  -> BlockId
  -> Either HelloPolicyValidationError SystemsBlock
lookupBlock function witness blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (HelloPolicyBlockMissing (helloPolicyServerFunction witness) blockId)
    Just blockValue -> Right blockValue

valueHasProducer :: SystemsFunction -> ValueId -> Bool
valueHasProducer function valueId = any blockProduces (Map.elems (systemsFunctionBlocks function))
  where
    blockProduces blockValue =
      any opProduces (systemsBlockOps blockValue)
        || terminatorProduces (systemsBlockTerminator blockValue)
    opProduces operation = case operation of
      OpRuntimeCall { runtimeCallOutputs = outputs } -> valueId `elem` outputs
      OpCopy { copyTarget = target } -> valueId == target
      OpScalarLiteral { scalarLiteralOutput = output } -> valueId == output
      _ -> False
    terminatorProduces terminator = case terminator of
      TermRuntimeChoice { runtimeChoiceArms = arms } ->
        any ((== Just valueId) . runtimeChoiceArmPayloadBinding) (Map.elems arms)
      TermSessionOffer { sessionOfferArms = arms } ->
        any ((== Just valueId) . choiceArmPayloadBinding) (Map.elems arms)
      _ -> False

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = lowering { loweringTargetArtifactDigest = targetDigest }

deriveHelloPolicyDecision
  :: Digest
  -> Digest
  -> RuntimeSiteRef
  -> HelloPolicyValidationWitness
  -> LoweringDecision
deriveHelloPolicyDecision sourceDigest targetDigest site witness = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = LoweringDecision
      { loweringDecisionId = helloPolicyLoweringDecision witness
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation =
          "operand-free HelloPolicy runtime check + class-only terminal failure"
      , loweringTargetRepresentation =
          "established Hello record + explicit PolicyContext operand + accepted/rejected(reason) local runtime choice + reason-carrying validation-failure effect"
      , loweringSemanticEntities =
          [ "validation:HelloPolicy"
          , "record:Hello"
          , "input:policyContext"
          , "reason:HelloPolicy rejection"
          , "failure:ValidationFailure[HelloPolicy]"
          ]
      , loweringObligationRevisions = [runtimeSiteRevision site]
      , loweringAssuranceEntries = [runtimeSiteEvidence site]
      , loweringAssuranceUses = []
      , loweringAction = Materialize
      , loweringRepresentationBefore =
          "payload-free HelloPolicy success/failure branch with discarded rejection reason"
      , loweringRepresentationAfter =
          "explicit validator subjects and rejected-arm reason consumed by terminal validation-failure effect"
      , loweringInvariantsPreserved =
          [ "HelloPolicy validation remains at the exact runtime assurance site"
          , "accepted validation continues to server.version.choose"
          , "rejected validation continues to server.hello.policy_failure"
          , "rejection reason is bound only on the rejected arm"
          , "the terminal failure consumes exactly that branch-local reason"
          ]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue =
          [ "existing Hello record representation and provenance are preserved from the version-choice operand predecessor"
          , "PolicyContext representation remains target-selected"
          , "validation implementation remains the retained HelloPolicy runtime site"
          , "rejection-reason physical representation and fatal transport ABI are deliberately unselected"
          , "the current BeginPolicy LLVM target must remain fail-closed for this successor"
          ]
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costCodeSize = Just "explicit policy input/reason identity and local choice structure"
          , costDynamicCheckCount = Just "no new check; the existing HelloPolicy runtime validation is retained"
          , costBranchOrDispatch = Just "same validation success/failure branch"
          , costFrequency = Just "once per successfully recognized Hello"
          }
      , loweringTargetPreconditions =
          [ "recognized Hello record materialization from the predecessor remains valid before validation"
          , "rejected payload target is a dedicated single-predecessor block"
          ]
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "verify exact HelloPolicy RuntimeSiteRef is preserved"
          , "verify validator consumes exact PolicyContext and recognized Hello identities"
          , "verify rejected arm binds exactly one HelloPolicy rejection reason"
          , "verify the reason has exactly one semantic use in the terminal validation-failure effect"
          , "verify BeginPolicy and version-choice successor witnesses remain valid"
          , "verify existing LLVM targets fail closed until a HelloPolicy physical profile is selected"
          ]
      }

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
