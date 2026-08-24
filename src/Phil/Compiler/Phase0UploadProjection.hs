{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.Phase0UploadProjection
  ( Phase0UploadProjectionError (..)
  , Phase0UploadProjection (..)
  , phase0UploadSourceDigest
  , projectPhase0UploadSources
  , verifyPhase0UploadProjection
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Surface.Check (checkSurfaceComponent)
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Phase0 (phase0EnvironmentFor)
import Phil.Surface.Syntax
import Phil.Systems.Dataflow (verifyScalarDataflow)
import Phil.Systems.IR
import Phil.Systems.Phase0
  ( phase0SystemsArtifact
  , phase0SystemsVerificationContext
  )
import Phil.Systems.StorageFailure
  ( phase0StorageFailureBundle
  , storageFailureArtifact
  , storageFailureContext
  , verifyStorageFailureBundle
  )
import Phil.Systems.Verify
  ( SystemsVerificationContext (..)
  , verifySystemsArtifact
  )

data Phase0UploadProjectionError
  = Phase0UploadProjectionParseError FilePath Text
  | Phase0UploadProjectionEnvironmentError FilePath Text
  | Phase0UploadProjectionCheckError FilePath Text
  | Phase0UploadProjectionComponentCount FilePath Int
  | Phase0UploadProjectionComponentName FilePath Text Text
  | Phase0UploadProjectionTraceMismatch FilePath [Text] [Text]
  | Phase0UploadProjectionBaselineError Text
  | Phase0UploadProjectionSystemsError Text
  | Phase0UploadProjectionDataflowError Text
  | Phase0UploadProjectionProgramDrift Text
  | Phase0UploadProjectionSourceDigestDrift Text
  deriving (Eq, Show)

data Phase0UploadProjection = Phase0UploadProjection
  { phase0ProjectionSourceDigest :: Digest
  , phase0ProjectionClientTrace :: [Text]
  , phase0ProjectionServerTrace :: [Text]
  , phase0ProjectionBaseArtifact :: SystemsArtifact
  , phase0ProjectionBaseContext :: SystemsVerificationContext
  , phase0ProjectionFinalArtifact :: SystemsArtifact
  , phase0ProjectionFinalContext :: SystemsVerificationContext
  }
  deriving (Eq, Show)

phase0UploadSourceDigest :: Text -> Text -> Digest
phase0UploadSourceDigest clientSource serverSource = digestText $ Text.intercalate "\n"
  [ "phil-source-pair/phase0-upload/v1"
  , "file:client.phil"
  , clientSource
  , "file:server.phil"
  , serverSource
  ]

projectPhase0UploadSources
  :: Text
  -> Text
  -> Either Phase0UploadProjectionError Phase0UploadProjection
projectPhase0UploadSources clientSource serverSource = do
  client <- checkedComponent "client.phil" "UploadClient" clientSource
  server <- checkedComponent "server.phil" "UploadServer" serverSource
  let clientTrace = componentSemanticTrace client
      serverTrace = componentSemanticTrace server
  unless (clientTrace == expectedClientTrace) $
    Left (Phase0UploadProjectionTraceMismatch
      "client.phil" expectedClientTrace clientTrace)
  unless (serverTrace == expectedServerTrace) $
    Left (Phase0UploadProjectionTraceMismatch
      "server.phil" expectedServerTrace serverTrace)

  let sourceDigest = phase0UploadSourceDigest clientSource serverSource
      baseArtifact = rebindSourceArtifact sourceDigest phase0SystemsArtifact
      baseContext = rebindSystemsContext
        sourceDigest baseArtifact phase0SystemsVerificationContext
  mapLeft (Phase0UploadProjectionSystemsError . Text.pack . show) $
    verifySystemsArtifact baseContext baseArtifact
  mapLeft (Phase0UploadProjectionDataflowError . Text.pack . show) $
    verifyScalarDataflow baseArtifact

  baseline <- mapLeft (Phase0UploadProjectionBaselineError . Text.pack . show)
    phase0StorageFailureBundle
  mapLeft (Phase0UploadProjectionBaselineError . Text.pack . show) $
    verifyStorageFailureBundle baseline
  let baselineFinal = storageFailureArtifact baseline
      finalArtifact = rebindSourceArtifact sourceDigest baselineFinal
      finalContext = rebindSystemsContext
        sourceDigest finalArtifact (storageFailureContext baseline)
  mapLeft (Phase0UploadProjectionSystemsError . Text.pack . show) $
    verifySystemsArtifact finalContext finalArtifact
  mapLeft (Phase0UploadProjectionDataflowError . Text.pack . show) $
    verifyScalarDataflow finalArtifact

  let projection = Phase0UploadProjection
        { phase0ProjectionSourceDigest = sourceDigest
        , phase0ProjectionClientTrace = clientTrace
        , phase0ProjectionServerTrace = serverTrace
        , phase0ProjectionBaseArtifact = baseArtifact
        , phase0ProjectionBaseContext = baseContext
        , phase0ProjectionFinalArtifact = finalArtifact
        , phase0ProjectionFinalContext = finalContext
        }
  verifyPhase0UploadProjection projection
  pure projection

verifyPhase0UploadProjection
  :: Phase0UploadProjection
  -> Either Phase0UploadProjectionError ()
verifyPhase0UploadProjection projection = do
  baseline <- mapLeft (Phase0UploadProjectionBaselineError . Text.pack . show)
    phase0StorageFailureBundle
  mapLeft (Phase0UploadProjectionBaselineError . Text.pack . show) $
    verifyStorageFailureBundle baseline

  let sourceDigest = phase0ProjectionSourceDigest projection
      baseArtifact = phase0ProjectionBaseArtifact projection
      finalArtifact = phase0ProjectionFinalArtifact projection
      baselineFinal = storageFailureArtifact baseline
  mapLeft (Phase0UploadProjectionSystemsError . Text.pack . show) $
    verifySystemsArtifact
      (phase0ProjectionBaseContext projection)
      baseArtifact
  mapLeft (Phase0UploadProjectionSystemsError . Text.pack . show) $
    verifySystemsArtifact
      (phase0ProjectionFinalContext projection)
      finalArtifact
  mapLeft (Phase0UploadProjectionDataflowError . Text.pack . show) $
    verifyScalarDataflow baseArtifact
  mapLeft (Phase0UploadProjectionDataflowError . Text.pack . show) $
    verifyScalarDataflow finalArtifact

  unless
    (systemsArtifactProgram baseArtifact == systemsArtifactProgram phase0SystemsArtifact) $
    Left (Phase0UploadProjectionProgramDrift
      "base source projection changed the canonical Phase 0 Systems program")
  unless
    (systemsArtifactProgram finalArtifact == systemsArtifactProgram baselineFinal) $
    Left (Phase0UploadProjectionProgramDrift
      "source rebinding changed the verified StorageFailure successor program")
  verifySourceDigest sourceDigest "base" baseArtifact
  verifySourceDigest sourceDigest "final" finalArtifact
  unless (phase0ProjectionClientTrace projection == expectedClientTrace) $
    Left (Phase0UploadProjectionTraceMismatch
      "client.phil" expectedClientTrace (phase0ProjectionClientTrace projection))
  unless (phase0ProjectionServerTrace projection == expectedServerTrace) $
    Left (Phase0UploadProjectionTraceMismatch
      "server.phil" expectedServerTrace (phase0ProjectionServerTrace projection))

checkedComponent
  :: FilePath
  -> Text
  -> Text
  -> Either Phase0UploadProjectionError Component
checkedComponent filePath expectedName source = do
  surfaceFile <- mapLeft
    (Phase0UploadProjectionParseError filePath . Text.pack . show)
    (parseSurfaceFile (Text.pack filePath) source)
  locatedComponent <- case surfaceComponents surfaceFile of
    [component] -> Right component
    components -> Left
      (Phase0UploadProjectionComponentCount filePath (length components))
  let component = locatedValue locatedComponent
  unless (componentName component == expectedName) $
    Left (Phase0UploadProjectionComponentName
      filePath expectedName (componentName component))
  environment <- mapLeft
    (Phase0UploadProjectionEnvironmentError filePath)
    (phase0EnvironmentFor filePath)
  _ <- mapLeft
    (Phase0UploadProjectionCheckError filePath . Text.pack . show)
    (checkSurfaceComponent environment locatedComponent)
  pure component

rebindSourceArtifact :: Digest -> SystemsArtifact -> SystemsArtifact
rebindSourceArtifact sourceDigest artifact =
  let program = systemsArtifactProgram artifact
      targetDigest = systemsProgramDigest program
      oldContract = systemsArtifactStageContract artifact
      marker = "checked client.phil/server.phil semantic trace -> canonical Phase 0 Systems graph"
      contract = oldContract
        { stageContractId = "surface-to-systems/phase0-upload/v1"
        , stageSourceArtifactDigest = sourceDigest
        , stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = appendUnique marker (stageTraceRelation oldContract)
        }
      oldDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      decisions = Map.map (rebindDecision sourceDigest targetDigest) oldDecisions
      root = deriveLoweringLedgerRoot decisions
  in SystemsArtifact program contract (LoweringLedger decisions root)

rebindDecision :: Digest -> Digest -> LoweringDecision -> LoweringDecision
rebindDecision sourceDigest targetDigest decision =
  let provisional = decision
        { loweringDecisionDigest = digestText ""
        , loweringSourceArtifactDigest = sourceDigest
        , loweringTargetArtifactDigest = targetDigest
        }
  in provisional
      { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }

rebindSystemsContext
  :: Digest
  -> SystemsArtifact
  -> SystemsVerificationContext
  -> SystemsVerificationContext
rebindSystemsContext sourceDigest artifact context =
  let root = loweringLedgerRoot (systemsArtifactLoweringLedger artifact)
      implementationDigest = systemsArtifactDigest artifact
      ledger = systemsAssuranceLedger context
      oldManifest = systemsAssuranceManifest context
      provisionalManifest = oldManifest
        { manifestImplementationDigest = implementationDigest
        , manifestLoweringLedgerRoot = root
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId ledger provisionalManifest }
      verification = (systemsAssuranceVerificationContext context)
        { verificationImplementationDigest = implementationDigest
        , verificationLoweringLedgerRoot = root
        }
  in context
      { systemsAssuranceManifest = manifest
      , systemsAssuranceVerificationContext = verification
      , systemsExpectedSourceArtifactDigest = sourceDigest
      }

verifySourceDigest
  :: Digest
  -> Text
  -> SystemsArtifact
  -> Either Phase0UploadProjectionError ()
verifySourceDigest sourceDigest label artifact = do
  let contract = systemsArtifactStageContract artifact
      decisions = Map.elems
        (loweringLedgerDecisions (systemsArtifactLoweringLedger artifact))
  unless (stageSourceArtifactDigest contract == sourceDigest) $
    Left (Phase0UploadProjectionSourceDigestDrift
      (label <> " stage contract does not carry the source-pair digest"))
  unless (all ((== sourceDigest) . loweringSourceArtifactDigest) decisions) $
    Left (Phase0UploadProjectionSourceDigestDrift
      (label <> " lowering ledger is not uniformly source-bound"))

componentSemanticTrace :: Component -> [Text]
componentSemanticTrace = blockSemanticTrace . locatedValue . componentBody

blockSemanticTrace :: Block -> [Text]
blockSemanticTrace = concatMap (statementSemanticTrace . locatedValue) . blockStatements

statementSemanticTrace :: Statement -> [Text]
statementSemanticTrace statement = case statement of
  LetStatement _ expression -> expressionSemanticTrace (locatedValue expression)
  ReturnStatement expression -> expressionSemanticTrace (locatedValue expression)
  ExpressionStatement expression -> expressionSemanticTrace (locatedValue expression)

expressionSemanticTrace :: SurfaceExpression -> [Text]
expressionSemanticTrace expression = case expression of
  VariableExpression _ -> []
  IntegerExpression _ -> []
  BooleanExpression _ -> []
  UnitExpression -> []
  TupleExpression values -> concatMap locatedExpressionTrace values
  CallExpression name arguments ->
    ("call:" <> name) : concatMap locatedExpressionTrace arguments
  FieldExpression value _ -> locatedExpressionTrace value
  BinaryExpression _ left right ->
    locatedExpressionTrace left <> locatedExpressionTrace right
  ConstructExpression name fields ->
    ("construct:" <> name <> ":" <> Text.intercalate "," (map fst fields))
      : concatMap (locatedExpressionTrace . snd) fields
  ReceiveExpression _ endpoint -> "receive" : locatedExpressionTrace endpoint
  ReceiveFrameExpression endpoint -> "receive_frame" : locatedExpressionTrace endpoint
  RecognizeExpression grammar raw ->
    ("recognize:" <> grammar) : locatedExpressionTrace raw
  ValidateExpression predicate context subject ->
    ("validate:" <> predicate)
      : maybe [] locatedExpressionTrace context <> locatedExpressionTrace subject
  SendExpression value endpoint ->
    "send" : locatedExpressionTrace value <> locatedExpressionTrace endpoint
  SendExactExpression value endpoint ->
    "send_exact" : locatedExpressionTrace value <> locatedExpressionTrace endpoint
  ReceiveExactExpression length endpoint evidence ->
    "receive_exact"
      : locatedExpressionTrace length
      <> locatedExpressionTrace endpoint
      <> maybe [] locatedExpressionTrace evidence
  SelectExpression branch endpoint evidence ->
    ("select:" <> branchValueLabel branch)
      : concatMap locatedExpressionTrace (branchValueArguments branch)
      <> locatedExpressionTrace endpoint
      <> maybe [] locatedExpressionTrace evidence
  CommitReceiveExpression pending parsed ->
    "commit_receive" : locatedExpressionTrace pending <> locatedExpressionTrace parsed
  BorrowExpression owner binder body ->
    ("borrow:" <> binder)
      : locatedExpressionTrace owner <> blockSemanticTrace (locatedValue body)
  DecideExpression scrutinee arms ->
    ("decide:" <> Text.intercalate "," (map armLabel arms))
      : locatedExpressionTrace scrutinee <> concatMap locatedArmTrace arms
  OfferExpression endpoint arms ->
    ("offer:" <> Text.intercalate "," (map armLabel arms))
      : locatedExpressionTrace endpoint <> concatMap locatedArmTrace arms
  FailExpression target value ->
    ("fail:" <> failureTargetClass target)
      : concatMap locatedExpressionTrace (failureTargetArguments target)
      <> locatedExpressionTrace value
  CloseExpression endpoint -> "close" : locatedExpressionTrace endpoint
  ReleaseExpression owner -> "release" : locatedExpressionTrace owner
  AcceptExpression value _ -> "accept" : locatedExpressionTrace value
  ProveExpression _ -> ["prove"]
  FallbackExpression inner fallback ->
    fallbackMarker fallback : locatedExpressionTrace inner

locatedExpressionTrace :: Located SurfaceExpression -> [Text]
locatedExpressionTrace = expressionSemanticTrace . locatedValue

locatedArmTrace :: Located CaseArm -> [Text]
locatedArmTrace locatedArm =
  let arm = locatedValue locatedArm
      patternValue = caseArmPattern arm
      marker = "arm:" <> casePatternLabel patternValue <> ":"
        <> Text.intercalate "," (casePatternBinders patternValue)
  in marker : blockSemanticTrace (locatedValue (caseArmBody arm))

armLabel :: Located CaseArm -> Text
armLabel = casePatternLabel . caseArmPattern . locatedValue

fallbackMarker :: Fallback -> Text
fallbackMarker fallback = case fallback of
  FailFallback failureClass -> "fallback:fail:" <> failureClass
  RejectFallback _ -> "fallback:reject"

expectedClientTrace :: [Text]
expectedClientTrace =
  [ "call:supported_versions"
  , "prove"
  , "construct:Hello:versions"
  , "send"
  , "offer:unsupported,version"
  , "arm:unsupported:"
  , "release"
  , "close"
  , "arm:version:selected"
  , "borrow:payloadView"
  , "call:sha256"
  , "construct:Begin:length,kind,digestAlg,digest"
  , "send"
  , "offer:reject,proceed"
  , "arm:reject:reason"
  , "release"
  , "close"
  , "arm:proceed:"
  , "decide:true,false"
  , "call:should_cancel_upload"
  , "arm:true:"
  , "select:cancel"
  , "release"
  , "close"
  , "arm:false:"
  , "select:payload"
  , "send_exact"
  , "offer:rejected,accepted"
  , "arm:rejected:reason"
  , "close"
  , "arm:accepted:id"
  , "call:record_upload_id"
  , "close"
  ]

expectedServerTrace :: [Text]
expectedServerTrace =
  [ "fallback:fail:transport"
  , "receive_frame"
  , "borrow:rawHello"
  , "recognize:Hello"
  , "decide:rejected,accepted"
  , "arm:rejected:reason"
  , "fail:recognition"
  , "arm:accepted:parsedHello"
  , "commit_receive"
  , "decide:rejected,accepted"
  , "validate:HelloPolicy"
  , "arm:rejected:reason"
  , "fail:validation"
  , "arm:accepted:helloPolicy"
  , "decide:none,some"
  , "call:choose_supported"
  , "arm:none:noCommon"
  , "select:unsupported"
  , "close"
  , "arm:some:version,offered,supported"
  , "select:version"
  , "fallback:fail:transport"
  , "receive_frame"
  , "borrow:rawBegin"
  , "recognize:Begin"
  , "decide:rejected,accepted"
  , "arm:rejected:reason"
  , "fail:recognition"
  , "arm:accepted:parsedBegin"
  , "commit_receive"
  , "decide:rejected,accepted"
  , "validate:BeginPolicy"
  , "arm:rejected:reason"
  , "select:reject"
  , "close"
  , "arm:accepted:beginPolicy"
  , "select:proceed"
  , "offer:payload,cancel"
  , "arm:payload:"
  , "fallback:fail:transport"
  , "receive_exact"
  , "borrow:payloadView"
  , "validate:DigestMatches"
  , "decide:rejected,accepted"
  , "arm:rejected:reason"
  , "release"
  , "select:rejected"
  , "close"
  , "arm:accepted:digestEvidence"
  , "decide:failure,success"
  , "call:store"
  , "arm:failure:err"
  , "fail:internal"
  , "arm:success:id"
  , "select:accepted"
  , "close"
  , "arm:cancel:"
  , "close"
  ]

appendUnique :: Eq a => a -> [a] -> [a]
appendUnique value values
  | value `elem` values = values
  | otherwise = values <> [value]

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
