{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Check.Engine
  ( checkSurfaceComponent
  ) where

import Control.Monad (foldM, unless, when)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context
  ( ResourceContext (..)
  , consumeLinear
  , endSharedLoan
  , ensureComplete
  , insertBinding
  , joinContinuing
  , startSharedLoan
  )
import Phil.Core.Decision
  ( checkDecisionCertificate
  , proposeDecisionCertificate
  )
import Phil.Core.Focusing
  ( FocusMechanism (..)
  , FocusPlan (..)
  , FocusedRequirement (..)
  , checkBranchExhaustiveness
  , elaborateRefTermAs
  , focusProposition
  )
import Phil.Core.Recognition
  ( beginRawLoan
  , commitContext
  , commitReceive
  , failPendingRecognition
  , receiveFrame
  , receiveFrameContext
  , receivePendingSpec
  , trustedRecognitionFailure
  , trustedRecognitionSuccess
  )
import Phil.Core.Refinement
  ( evidenceProposition
  , normalizeProposition
  , normalizeRefTerm
  )
import Phil.Core.Session
  ( MessageSpec (..)
  , SessionStep (..)
  , closeEndpoint
  , exposeSessionHead
  , offerEndpoint
  , receiveEndpoint
  , selectEndpoint
  , sendEndpoint
  )
import Phil.Core.Syntax
  ( Branch (..)
  , Control (..)
  , GrammarId (..)
  , Mode (..)
  , Name (..)
  , Outcome (..)
  , PendingRecvSpec (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Core.Value
  ( EqualityBoundary (..)
  , ValueResult (..)
  , checkValue
  , checkValueUsing
  , compareTypes
  )
import Phil.Surface.Check.Support
import Phil.Surface.Check.Types
import Phil.Surface.Elaborate
  ( elaborateProposition
  , elaborateRefTerm
  )
import Phil.Surface.Syntax
  ( Block (..)
  , BranchValue (..)
  , CaseArm (..)
  , CasePattern (..)
  , Component (..)
  , FailureTarget (..)
  , Fallback (..)
  , Located (..)
  , Parameter (..)
  , Pattern (..)
  , SourceSpan
  , Statement (..)
  , SurfaceExpression (..)
  , SurfaceProposition
  , SurfaceType
  )

checkSurfaceComponent
  :: SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCheckError SurfaceCheckResult
checkSurfaceComponent environment locatedComponent = do
  initial <- initializeState environment (locatedValue locatedComponent)
  checkProvides environment initial (locatedValue locatedComponent)
  paths <- checkBlock environment initial (componentBody (locatedValue locatedComponent))
  finalPaths <- mapM (finalizePath environment (locatedSpan locatedComponent)) paths
  Right SurfaceCheckResult
    { checkedComponentName = componentName (locatedValue locatedComponent)
    , checkedTerminalControls = map toCoreControl finalPaths
    }

initializeState :: SurfaceEnvironment -> Component -> Either SurfaceCheckError SurfaceState
initializeState environment component = do
  withInitial <- foldM insertInitial emptySurfaceState $
    Map.toAscList (surfaceInitialBindings environment)
  foldM insertParameter withInitial (componentParameters component)
  where
    insertInitial state (name, binding) =
      insertBindingMeta syntheticSpan name
        (BindingMeta (initialMode binding) (initialType binding) (initialShape binding))
        state

    insertParameter state locatedParameter =
      let parameter = locatedValue locatedParameter
          name = parameterName parameter
      in case Map.lookup name (stateBindings state) of
          Just existing -> case parameterType parameter of
            Nothing -> Right state
            Just surfaceTy -> do
              (mode, ty, _) <- resolveSurfaceType environment state surfaceTy
              unless
                (mode == bindingMode existing
                  && compareTypes (bindingType existing) ty == DefinitionallyEqual) $
                throw locatedParameter TypeMismatch
                  "parameter type disagrees with the architecture-supplied binding"
              Right state
          Nothing -> case parameterType parameter of
            Nothing -> throw locatedParameter TypeMismatch
              "untyped parameter has no architecture-supplied binding"
            Just surfaceTy -> do
              (mode, ty, shape) <- resolveSurfaceType environment state surfaceTy
              insertBindingMeta (locatedSpan locatedParameter) name
                (BindingMeta mode ty shape) state

checkProvides :: SurfaceEnvironment -> SurfaceState -> Component -> Either SurfaceCheckError ()
checkProvides environment state component =
  case (surfaceExpectedProvides environment, componentProvides component) of
    (Nothing, _) -> Right ()
    (Just expected, Just surfaceTy) -> do
      (_, actual, _) <- resolveSurfaceType environment state surfaceTy
      unless (compareTypes actual expected == DefinitionallyEqual) $
        throw surfaceTy TypeMismatch
          "provides type disagrees with the architecture contract"
    (Just _, Nothing) -> Left SurfaceCheckError
      { surfaceErrorSpan = locatedSpan (componentBody component)
      , surfaceErrorClass = TypeMismatch
      , surfaceErrorDetail = "component is missing its required provides clause"
      }

checkBlock
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located Block
  -> Either SurfaceCheckError [SurfacePath]
checkBlock environment state locatedBlock =
  checkStatements environment [continuePath state] $
    blockStatements (locatedValue locatedBlock)

checkStatements
  :: SurfaceEnvironment
  -> [SurfacePath]
  -> [Located Statement]
  -> Either SurfaceCheckError [SurfacePath]
checkStatements _ paths [] = Right paths
checkStatements environment paths (statement : rest) = do
  let continuing = filter ((== PathContinue) . pathControl) paths
      stopped = filter ((/= PathContinue) . pathControl) paths
  when (null continuing) $
    throw statement ControlAfterTerminal
      "statement occurs after all incoming paths terminated"
  advanced <- concat <$> mapM (checkStatement environment statement) continuing
  checkStatements environment (stopped ++ advanced) rest

checkStatement
  :: SurfaceEnvironment
  -> Located Statement
  -> SurfacePath
  -> Either SurfaceCheckError [SurfacePath]
checkStatement environment locatedStatement path =
  case locatedValue locatedStatement of
    LetStatement pattern' expression -> do
      evaluated <- evalExpression environment (pathState path) expression
      bound <- mapM (bindPath pattern') evaluated
      joinExclusive (locatedSpan locatedStatement) bound
    ReturnStatement expression -> do
      evaluated <- evalExpression environment (pathState path) expression
      mapM (returnPath environment (locatedSpan locatedStatement)) evaluated
    ExpressionStatement expression -> do
      evaluated <- evalExpression environment (pathState path) expression
      discarded <- mapM (discardValue (locatedSpan locatedStatement)) evaluated
      joinExclusive (locatedSpan locatedStatement) discarded

bindPath :: Located Pattern -> SurfacePath -> Either SurfaceCheckError SurfacePath
bindPath _ path | pathControl path /= PathContinue = Right path
bindPath pattern' path = case pathValue path of
  Nothing -> throw pattern' TypeMismatch "expression produced no bindable result"
  Just value -> do
    next <- bindPattern pattern' value (pathState path)
    Right (continuePath next)

bindPattern :: Located Pattern -> RuntimeValue -> SurfaceState -> Either SurfaceCheckError SurfaceState
bindPattern pattern' value state = case (locatedValue pattern', value) of
  (BindPattern name, RuntimeScalar scalar) ->
    insertBindingMeta (locatedSpan pattern') name
      (BindingMeta
        (scalarMode scalar)
        (scalarType scalar)
        (shapeForBinding name (scalarShape scalar)))
      state
  (BindPattern name, RuntimeUnit) ->
    insertBindingMeta (locatedSpan pattern') name
      (BindingMeta Unrestricted TyUnit PlainShape) state
  (TuplePattern patterns, RuntimeTuple values)
    | length patterns == length values ->
        foldM (\current (subPattern, subValue) -> bindPattern subPattern subValue current)
          state
          (zip patterns values)
    | otherwise -> throw pattern' TypeMismatch "tuple binding arity mismatch"
  _ -> throw pattern' TypeMismatch "pattern does not match expression result"

returnPath
  :: SurfaceEnvironment
  -> SourceSpan
  -> SurfacePath
  -> Either SurfaceCheckError SurfacePath
returnPath _ _ path | pathControl path /= PathContinue = Right path
returnPath environment span' path = do
  let state = pathState path
      ty = maybe TyUnit runtimeType (pathValue path)
  ensureTerminalState environment span' Nothing state
  Right path { pathControl = PathReturn ty, pathValue = Nothing }

discardValue :: SourceSpan -> SurfacePath -> Either SurfaceCheckError SurfacePath
discardValue _ path | pathControl path /= PathContinue = Right path
discardValue span' path = case pathValue path of
  Just value | restrictedRuntimeValue value -> Left SurfaceCheckError
    { surfaceErrorSpan = span'
    , surfaceErrorClass = LinearCompletion
    , surfaceErrorDetail = "restricted expression result is discarded"
    }
  _ -> Right path { pathValue = Nothing }

evalExpression
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalExpression environment state locatedExpression =
  case locatedValue locatedExpression of
    VariableExpression name -> do
      (scalar, next) <- moveVariable locatedExpression name state
      Right [valuePath next (RuntimeScalar scalar)]
    IntegerExpression literal -> Right
      [ valuePath state (RuntimeScalar
          (ScalarValue Unrestricted
            (TyOpaque ("Integer[" <> Text.pack (show literal) <> "]"))
            PlainShape))
      ]
    BooleanExpression _ -> Right
      [ valuePath state (RuntimeScalar
          (ScalarValue Unrestricted TyBool (DecisionShape BooleanDecision)))
      ]
    UnitExpression -> Right [valuePath state RuntimeUnit]
    TupleExpression expressions -> do
      (values, next) <- evalSequentialValues environment state expressions
      Right [valuePath next (RuntimeTuple values)]
    FieldExpression base field -> do
      scalar <- readField environment state locatedExpression base field
      Right [valuePath state (RuntimeScalar scalar)]
    BinaryExpression {} -> do
      scalar <- inferReadOnlyScalar environment state locatedExpression
      Right [valuePath state (RuntimeScalar scalar)]
    ConstructExpression constructor fields -> do
      scalar <- constructValue environment state locatedExpression constructor fields
      Right [valuePath state (RuntimeScalar scalar)]
    CallExpression name arguments ->
      evalPrimitive environment state locatedExpression name arguments
    ReceiveExpression messageTy endpoint ->
      evalReceive environment state locatedExpression messageTy endpoint
    ReceiveFrameExpression endpoint ->
      evalReceiveFrame environment state locatedExpression endpoint
    RecognizeExpression grammar raw ->
      evalRecognize environment state locatedExpression grammar raw
    ValidateExpression claim context subject ->
      evalValidate environment state locatedExpression claim context subject
    SendExpression value endpoint ->
      evalSend environment False state locatedExpression value endpoint
    SendExactExpression value endpoint ->
      evalSend environment True state locatedExpression value endpoint
    ReceiveExactExpression count endpoint evidence ->
      evalReceiveExact environment state locatedExpression count endpoint evidence
    SelectExpression branch endpoint evidence ->
      evalSelect environment state locatedExpression branch endpoint evidence
    CommitReceiveExpression pending evidence ->
      evalCommit environment state locatedExpression pending evidence
    BorrowExpression owner view body ->
      evalBorrow environment state locatedExpression owner view body
    DecideExpression scrutinee arms ->
      evalDecide environment state locatedExpression scrutinee arms
    OfferExpression endpoint arms ->
      evalOffer environment state locatedExpression endpoint arms
    FailExpression target resource ->
      evalFail environment state locatedExpression target resource
    CloseExpression target ->
      evalClose environment state locatedExpression target
    ReleaseExpression owner ->
      evalRelease environment state locatedExpression owner
    AcceptExpression value targetTy ->
      evalAccept environment state locatedExpression value targetTy
    ProveExpression proposition ->
      evalProve environment state locatedExpression proposition
    FallbackExpression base fallback ->
      evalFallback environment state locatedExpression base fallback

evalPrimitive
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Text
  -> [Located SurfaceExpression]
  -> Either SurfaceCheckError [SurfacePath]
evalPrimitive environment state located name arguments =
  case Map.lookup name (surfacePrimitives environment) of
    Nothing -> throw located UnknownPrimitive
      ("primitive is not declared in Sigma: " <> name)
    Just primitive -> evalPrimitiveRule environment state located primitive arguments

evalPrimitiveRule
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> PrimitiveSemantics
  -> [Located SurfaceExpression]
  -> Either SurfaceCheckError [SurfacePath]
evalPrimitiveRule environment state located primitive arguments =
  case primitive of
    PrimitiveSupportedVersions -> do
      arity 0
      let binder = Name "$versions"
          base = TyOpaqueSorted "SupportedVersions" versionSetSort
          proposition = LessThan (RefNat 0) (RefLen (RefVar binder))
      scalar (TyRefined binder base proposition) PlainShape
    PrimitiveSha256 -> readArguments 1 >> scalar (TyOpaque "Digest") PlainShape
    PrimitiveShouldCancel -> arity 0 >> scalar TyBool (DecisionShape BooleanDecision)
    PrimitiveChooseSupported ->
      readArguments 2 >> scalar (TyOpaque "SupportedDecision") (DecisionShape ChooseSupportedDecision)
    PrimitiveStore -> do
      arity 1
      (_, next) <- moveLinearArgument state (head arguments)
      Right
        [ valuePath next (RuntimeScalar
            (ScalarValue Unrestricted
              (TyOpaque "StoreResult")
              (DecisionShape StoreDecision)))
        ]
    PrimitiveFixtureBytes -> do
      arity 0
      let (frame, next) = freshFrame state
      Right
        [ valuePath next (RuntimeScalar
            (ScalarValue Unrestricted
              (TyOpaqueSorted "RawBytes" byteSequenceSort)
              (FixtureRawShape frame)))
        ]
    PrimitiveUncheckedU32Add -> do
      readArguments 2
      scalar (TyUInt 32) UncheckedArithmeticShape
    PrimitiveNewCancellationScope -> do
      arity 0
      Right
        [ valuePath state (RuntimeTuple
            [ RuntimeScalar (ScalarValue Linear (TyOpaque "CancelScope") PlainShape)
            , RuntimeScalar (ScalarValue Affine (TyOpaque "CancelCap") PlainShape)
            ])
        ]
    PrimitiveAllocateLinearBuffer ->
      arity 1 >> scalarWithMode Linear (TyOpaque "LinearBuffer") PlainShape
    PrimitiveRecordUploadId -> readArguments 1 >> unit
    PrimitiveConsumeBeginPolicyEvidence -> do
      arity 1
      evidenceName <- namedExpression MissingEvidence (head arguments)
      meta <- lookupMeta (head arguments) (unName evidenceName) state
      case bindingType meta of
        TyValidated "BeginPolicy" _ _ -> unit
        TyProof (Atom "BeginPolicy" _) -> unit
        _ -> throw (head arguments) MissingEvidence
          "binding is not BeginPolicy evidence"
    PrimitiveUse -> do
      next <- foldM consumeRestrictedIfNamed state arguments
      Right [valuePath next RuntimeUnit]
    PrimitiveInspect -> readArguments 1 >> unit
    PrimitiveAuthorizeStore -> consumeOne
    PrimitiveDelegate -> consumeOne
    PrimitiveContinueCommonState -> readArguments 1 >> unit
    PrimitiveHandlePayload -> unit
  where
    arity expected = unless (length arguments == expected) $
      throw located TypeMismatch
        ("primitive arity mismatch; expected " <> Text.pack (show expected))

    readArguments expected = do
      arity expected
      mapM_ (inferReadOnlyScalar environment state) arguments

    scalar ty shape = scalarWithMode Unrestricted ty shape
    scalarWithMode mode ty shape =
      Right [valuePath state (RuntimeScalar (ScalarValue mode ty shape))]
    unit = Right [valuePath state RuntimeUnit]

    consumeOne = do
      arity 1
      (_, next) <- moveVariableArgument state (head arguments)
      Right [valuePath next RuntimeUnit]

    consumeRestrictedIfNamed current expression = case locatedValue expression of
      VariableExpression name -> case Map.lookup name (stateBindings current) of
        Just meta | bindingMode meta /= Unrestricted ->
          snd <$> moveVariable expression name current
        _ -> Right current
      _ -> Right current

moveVariableArgument
  :: SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
moveVariableArgument state expression = do
  name <- namedExpression StructuralUse expression
  moveVariable expression (unName name) state

moveLinearArgument
  :: SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
moveLinearArgument state expression = do
  (scalar, next) <- moveVariableArgument state expression
  unless (scalarMode scalar == Linear) $
    throw expression StructuralUse "operation requires a linear owner"
  Right (scalar, next)

evalSequentialValues
  :: SurfaceEnvironment
  -> SurfaceState
  -> [Located SurfaceExpression]
  -> Either SurfaceCheckError ([RuntimeValue], SurfaceState)
evalSequentialValues environment = go []
  where
    go accumulated current [] = Right (reverse accumulated, current)
    go accumulated current (expression : rest) = do
      paths <- evalExpression environment current expression
      case paths of
        [SurfacePath PathContinue next (Just value)] ->
          go (value : accumulated) next rest
        _ -> throw expression TypeMismatch
          "tuple element cannot branch or terminate"

evalReceive
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceType
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalReceive environment state located surfaceMessage endpointExpression = do
  endpoint <- endpointName endpointExpression
  meta <- lookupMeta endpointExpression endpoint state
  expectedMessage <- sessionReceiveMessage located meta
  (_, writtenMessage, _) <- resolveSurfaceType environment state surfaceMessage
  unless (compareTypes writtenMessage expectedMessage == DefinitionallyEqual) $
    throw surfaceMessage TypeMismatch
      "written receive type does not match the protocol message"
  let (temp, state1) = freshName "$recv" state
  step <- mapSession located $
    receiveEndpoint (Name endpoint) temp (resourceContext (stateCore state1))
  message <- requireMessage located step
  let state2 = applySessionContext endpoint (stepContext step) state1
  (successor, state3) <- extractLinearTemp (locatedSpan located) temp state2
  let received = ScalarValue
        (messageMode (messageType message))
        (messageType message)
        (shapeForType (messageType message))
  Right
    [ valuePath state3
        (RuntimeTuple [RuntimeScalar successor, RuntimeScalar received])
    ]

evalReceiveFrame
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalReceiveFrame environment state located endpointExpression = do
  endpoint <- endpointName endpointExpression
  _ <- sessionReceiveFrameGrammar located =<< lookupMeta endpointExpression endpoint state
  let (pendingTemp, state1) = freshName "$pending" state
      (frame, state2) = freshFrame state1
  step <- mapRecognition located $
    receiveFrame
      (Name endpoint)
      pendingTemp
      frame
      (resourceContext (stateCore state2))
  let state3 = applySessionContext endpoint (receiveFrameContext step) state2
  (pendingScalar, state4) <- extractLinearTemp (locatedSpan located) pendingTemp state3
  if surfaceLegacyReceiveFrameRaw environment
    then Right
      [ valuePath state4 (RuntimeTuple
          [ RuntimeScalar pendingScalar
          , RuntimeScalar
              (ScalarValue Unrestricted
                (TyOpaqueSorted "RawBytes" byteSequenceSort)
                (LegacyRawShape (pendingGrammar (receivePendingSpec step)) frame))
          ])
      ]
    else Right [valuePath state4 (RuntimeScalar pendingScalar)]

evalRecognize
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Text
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalRecognize environment state located grammar rawExpression = do
  raw <- inferReadOnlyScalar environment state rawExpression
  case scalarShape raw of
    PendingRawShape rawView -> do
      parsed <- mapRecognition located $
        trustedRecognitionSuccess
          rawView
          (Name ("$parsed-" <> grammar))
          (resourceContext (stateCore state))
      failure <- mapRecognition located $
        trustedRecognitionFailure
          rawView
          "recognition-failure"
          (resourceContext (stateCore state))
      decision (RecognitionDecision parsed failure grammar)
    LegacyRawShape grammarId frame
      | grammarId == GrammarId grammar ->
          decision (LegacyRecognitionDecision grammarId frame grammar)
      | otherwise -> throw located RecognitionProvenance
          "recognizer grammar differs from pending frame grammar"
    FixtureRawShape frame -> Right
      [ valuePath state (RuntimeScalar
          (ScalarValue Unrestricted
            (TyOpaque ("Parsed[" <> grammar <> "]"))
            (ExternalParsedShape grammar frame)))
      ]
    _ -> throw rawExpression TypeMismatch "recognize requires a raw byte view"
  where
    decision kind = Right
      [ valuePath state (RuntimeScalar
          (ScalarValue Unrestricted
            (TyOpaque "RecognitionDecision")
            (DecisionShape kind)))
      ]

evalValidate
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Text
  -> Maybe (Located SurfaceExpression)
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalValidate environment state located claim context subject
  | claim == "DigestMatches" = do
      validateDigestSubject subject
      decision (DigestDecision digestMatchesProposition)
  | otherwise = do
      contextName <- case context of
        Just expression -> namedExpression MissingEvidence expression
        Nothing -> Right (Name "$implicit-context")
      subjectName <- namedExpression TypeMismatch subject
      _ <- lookupMeta subject (unName subjectName) state
      decision (ValidationDecision claim contextName subjectName)
  where
    validateDigestSubject expression = case locatedValue expression of
      TupleExpression values -> mapM_ (inferReadOnlyScalar environment state) values
      _ -> inferReadOnlyScalar environment state expression >> Right ()

    decision kind = Right
      [ valuePath state (RuntimeScalar
          (ScalarValue Unrestricted
            (TyOpaque "ValidationDecision")
            (DecisionShape kind)))
      ]

    digestMatchesProposition = Atom "DigestMatches"
      [ RefVar (Name "begin")
      , payloadStableTerm
      ]

    _ = located

evalSend
  :: SurfaceEnvironment
  -> Bool
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalSend environment exact state located valueExpression endpointExpression = do
  endpoint <- endpointName endpointExpression
  endpointMeta <- lookupMeta endpointExpression endpoint state
  expected <- sessionSendMessage located endpointMeta
  when (exact && not (isBytesTy expected)) $
    throw located TypeMismatch "send_exact requires a byte protocol message"
  (value, state1) <- moveOrReadValue environment state valueExpression
  checkScalarAgainst state1 valueExpression value expected
  let (temp, state2) = freshName "$send" state1
  step <- mapSession located $
    sendEndpoint (Name endpoint) temp (resourceContext (stateCore state2))
  let state3 = applySessionContext endpoint (stepContext step) state2
  (successor, state4) <- extractLinearTemp (locatedSpan located) temp state3
  Right [valuePath state4 (RuntimeScalar successor)]

evalReceiveExact
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError [SurfacePath]
evalReceiveExact environment state located count endpointExpression explicitEvidence = do
  endpoint <- endpointName endpointExpression
  endpointMeta <- lookupMeta endpointExpression endpoint state
  expected <- sessionReceiveMessage located endpointMeta
  expectedIndex <- case rewriteTy state expected of
    TyBytes index -> Right index
    other -> throw located TypeMismatch
      ("receive_exact requires Bytes, found " <> Text.pack (show other))
  checkConfiguredRequirement
    environment state count (surfaceReceiveExactRequirement environment) explicitEvidence
  rawCount <- mapElaboration count $
    elaborateRefTerm (elaborationEnv environment state) count
  (natCount, _) <- mapFocusing count $
    elaborateRefTermAs
      (surfaceStaticContext environment)
      (stateCore state)
      SortNat
      (rewriteRefTerm state rawCount)
  unless (normalizeRefTerm natCount == normalizeRefTerm expectedIndex) $
    throw count TypeMismatch
      "receive_exact count differs from the protocol byte length"
  let (temp, state1) = freshName "$receive-exact" state
  step <- mapSession located $
    receiveEndpoint (Name endpoint) temp (resourceContext (stateCore state1))
  let state2 = applySessionContext endpoint (stepContext step) state1
  (successor, state3) <- extractLinearTemp (locatedSpan located) temp state2

  let payload = ScalarValue Linear (TyBytes expectedIndex) (OwnedBytesShape expectedIndex)
  Right
    [ valuePath state3
        (RuntimeTuple [RuntimeScalar successor, RuntimeScalar payload])
    ]

evalSelect
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> BranchValue
  -> Located SurfaceExpression
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError [SurfacePath]
evalSelect environment state located branch endpointExpression explicitEvidence = do
  endpoint <- endpointName endpointExpression
  endpointMeta <- lookupMeta endpointExpression endpoint state
  (expectedPayload, _) <- sessionSelectBranch located endpointMeta (branchValueLabel branch)
  mapM_
    (\requirement -> checkRequirement environment state located requirement explicitEvidence)
    (Map.findWithDefault []
      (branchValueLabel branch)
      (surfaceSelectRequirements environment))
  state1 <- checkSelectedPayload
    environment state expectedPayload (branchValueArguments branch) explicitEvidence
  let (temp, state2) = freshName "$select" state1
  step <- mapSession located $
    selectEndpoint
      (Name endpoint)
      temp
      (branchValueLabel branch)
      (resourceContext (stateCore state2))
  let state3 = applySessionContext endpoint (stepContext step) state2
  (successor, state4) <- extractLinearTemp (locatedSpan located) temp state3
  Right [valuePath state4 (RuntimeScalar successor)]

evalCommit
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalCommit environment state located pendingExpression evidenceExpression = do
  pendingName <- namedExpression RecognitionProvenance pendingExpression
  pendingMeta <- lookupMeta pendingExpression (unName pendingName) state
  spec <- case bindingType pendingMeta of
    TyPendingRecv pending -> Right pending
    _ -> throw pendingExpression RecognitionProvenance
      "commit_receive target is not a pending receive"
  evidence <- inferReadOnlyScalar environment state evidenceExpression
  (successor, next) <- case scalarShape evidence of
    ParsedShape parsed _ -> do
      let (temp, state1) = freshName "$commit" state
      step <- mapRecognition located $
        commitReceive pendingName temp parsed (resourceContext (stateCore state1))
      let state2 = applySessionContext (unName pendingName) (commitContext step) state1
      extractLinearTemp (locatedSpan located) temp state2
    LegacyParsedShape grammar frame _
      | grammar == pendingGrammar spec && frame == pendingFrame spec -> do
          (_, context) <- mapCore (locatedSpan located) RecognitionProvenance $
            consumeLinear pendingName (resourceContext (stateCore state))
          let state1 = consumeSurfaceName (unName pendingName) state
              (temp, state2) = freshName "$legacy-commit" state1
          context2 <- mapCore (locatedSpan located) RecognitionProvenance $
            insertBinding Linear temp (TyEndpoint (pendingContinuation spec)) context
          extractLinearTemp
            (locatedSpan located)
            temp
            state2 { stateCore = (stateCore state2) { resourceContext = context2 } }
      | otherwise -> throw evidenceExpression RecognitionProvenance
          "parsed evidence belongs to a different frame"
    ExternalParsedShape _ _ -> throw evidenceExpression RecognitionProvenance
      "fixture recognition evidence cannot commit this pending receive"
    ForgedParsedShape -> throw evidenceExpression RecognitionProvenance
      "forged parsed evidence has no ingress provenance"
    _ -> throw evidenceExpression RecognitionProvenance
      "commit_receive requires Parsed evidence"
  Right [valuePath next (RuntimeScalar successor)]

evalBorrow
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Text
  -> Located Block
  -> Either SurfaceCheckError [SurfacePath]
evalBorrow environment state located ownerExpression viewName body = do
  ownerName <- namedExpression BorrowEscape ownerExpression
  ownerMeta <- lookupMeta ownerExpression (unName ownerName) state
  (view, loaned) <- case bindingType ownerMeta of
    TyPendingRecv _ -> do
      (raw, context) <- mapRecognition located $
        beginRawLoan ownerName (resourceContext (stateCore state))
      Right
        ( ScalarValue Unrestricted
            (TyOpaqueSorted "RawBytes" byteSequenceSort)
            (PendingRawShape raw)
        , state { stateCore = (stateCore state) { resourceContext = context } }
        )
    _
      | bindingMode ownerMeta == Linear || bindingMode ownerMeta == Affine -> do
          context <- mapCore (locatedSpan located) BorrowEscape $
            startSharedLoan ownerName (resourceContext (stateCore state))
          Right
            ( ScalarValue Unrestricted
                (TyOpaqueSorted "SharedBytes" byteSequenceSort)
                (BorrowedViewShape ownerName)
            , state { stateCore = (stateCore state) { resourceContext = context } }
            )
      | otherwise -> throw ownerExpression BorrowEscape
          "borrow requires an affine or linear owner"
  withView <- insertBindingMeta (locatedSpan located) viewName
    (BindingMeta Unrestricted (scalarType view) (scalarShape view)) loaned
  bodyPaths <- checkValueBlock environment withView body
  mapM (finish ownerName) bodyPaths
  where
    finish owner path
      | pathControl path /= PathContinue =
          throw located BorrowEscape "borrow body terminates before the loan ends"
      | otherwise = do
          case pathValue path of
            Just value | containsBorrowedView owner value ->
              throw located BorrowEscape "shared view escapes its lexical scope"
            _ -> Right ()
          state1 <- removeScopedBinding (locatedSpan located) viewName (pathState path)
          context <- mapCore (locatedSpan located) BorrowEscape $
            endSharedLoan owner (resourceContext (stateCore state1))
          Right path
            { pathState = state1
                { stateCore = (stateCore state1) { resourceContext = context }
                }
            }

containsBorrowedView :: Name -> RuntimeValue -> Bool
containsBorrowedView _ RuntimeUnit = False
containsBorrowedView owner (RuntimeTuple values) = any (containsBorrowedView owner) values
containsBorrowedView owner (RuntimeScalar scalar) = case scalarShape scalar of
  BorrowedViewShape actual -> actual == owner
  PendingRawShape _ -> True
  _ -> False

-- | A decision scrutinee is an expression, not merely a read-only term.
-- Evaluate it once, carry its resource effects into every arm, and refuse a
-- scrutinee that itself branches or terminates.  This is the surface analogue
-- of A-normalization and is essential for validate/recognize/store decisions.
evalDecide
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> [Located CaseArm]
  -> Either SurfaceCheckError [SurfacePath]
evalDecide environment state located scrutinee arms = do
  evaluated <- evalExpression environment state scrutinee
  (scalar, decisionState) <- case evaluated of
    [SurfacePath PathContinue next (Just (RuntimeScalar value))] -> Right (value, next)
    [SurfacePath PathContinue _ (Just _)] ->
      throw scrutinee TypeMismatch "decide requires a scalar decision value"
    [SurfacePath PathContinue _ Nothing] ->
      throw scrutinee TypeMismatch "decide scrutinee produced no value"
    _ -> throw scrutinee TypeMismatch
      "decide scrutinee may not branch or terminate"
  decision <- case scalarShape scalar of
    DecisionShape value -> Right value
    _
      | scalarType scalar == TyBool -> Right BooleanDecision
      | otherwise -> throw scrutinee TypeMismatch
          "decide requires a declared decision value"
  let expected = Set.fromList (decisionLabels decision)
      actual = Set.fromList $
        map (casePatternLabel . caseArmPattern . locatedValue) arms
  unless (expected == actual && Set.size expected == length arms) $
    throw located BranchExhaustiveness
      "decision handlers do not exactly cover all alternatives"
  concat <$> mapM (checkDecisionArm environment decisionState decision) arms

checkDecisionArm
  :: SurfaceEnvironment
  -> SurfaceState
  -> DecisionKind
  -> Located CaseArm
  -> Either SurfaceCheckError [SurfacePath]
checkDecisionArm environment state decision locatedArm = do
  let pattern' = caseArmPattern (locatedValue locatedArm)
  withBinders <- bindDecisionPattern
    state
    decision
    (casePatternLabel pattern')
    (casePatternBinders pattern')
    locatedArm
  checkScopedValueBlock
    environment
    state
    withBinders
    (caseArmBody (locatedValue locatedArm))

decisionLabels :: DecisionKind -> [Text]
decisionLabels decision = case decision of
  BooleanDecision -> ["true", "false"]
  ChooseSupportedDecision -> ["none", "some"]
  RecognitionDecision {} -> ["rejected", "accepted"]
  LegacyRecognitionDecision {} -> ["failure", "success"]
  ValidationDecision {} -> ["rejected", "accepted"]
  DigestDecision {} -> ["rejected", "accepted"]
  StoreDecision -> ["failure", "success"]

bindDecisionPattern
  :: SurfaceState
  -> DecisionKind
  -> Text
  -> [Text]
  -> Located a
  -> Either SurfaceCheckError SurfaceState
bindDecisionPattern state decision label binders located =
  case (decision, label, binders) of
    (BooleanDecision, "true", []) -> Right state
    (BooleanDecision, "false", []) -> Right state
    (ChooseSupportedDecision, "none", [noCommon]) ->
      insertProof located noCommon
        (Disjoint serverSupportedTerm helloVersionsTerm) state
    (ChooseSupportedDecision, "some", [version, offered, supported]) -> do
      state1 <- insertBindingMeta (locatedSpan located) version
        (BindingMeta Unrestricted (TyUInt 16) PlainShape) state
      state2 <- insertProof located offered
        (Member (RefVar (Name version)) helloVersionsTerm) state1
      insertProof located supported
        (Member (RefVar (Name version)) serverSupportedTerm) state2
    (RecognitionDecision parsed _ grammar, "accepted", [parsedName]) ->
      insertBindingMeta (locatedSpan located) parsedName
        (BindingMeta Unrestricted
          (TyOpaque ("Parsed[" <> grammar <> "]"))
          (ParsedShape parsed grammar))
        state
    (RecognitionDecision _ failure _, "rejected", [reason]) ->
      insertBindingMeta (locatedSpan located) reason
        (BindingMeta Unrestricted
          (TyOpaque "RecognitionFailure")
          (RecognitionFailureShape failure))
        state
    (LegacyRecognitionDecision grammar frame grammarText, "success", [parsedName]) ->
      insertBindingMeta (locatedSpan located) parsedName
        (BindingMeta Unrestricted
          (TyOpaque ("Parsed[" <> grammarText <> "]"))
          (LegacyParsedShape grammar frame grammarText))
        state
    (LegacyRecognitionDecision grammar frame _, "failure", [reason]) ->
      insertBindingMeta (locatedSpan located) reason
        (BindingMeta Unrestricted
          (TyOpaque "RecognitionFailure")
          (LegacyRecognitionFailureShape grammar frame))
        state
    (ValidationDecision claim context subject, "accepted", [evidence]) ->
      insertBindingMeta (locatedSpan located) evidence
        (BindingMeta Unrestricted
          (TyValidated claim context subject)
          PlainShape)
        state
    (ValidationDecision claim _ _, "rejected", [reason]) ->
      insertBindingMeta (locatedSpan located) reason
        (BindingMeta Unrestricted
          (TyOpaque ("ValidationFailure[" <> claim <> "]"))
          PlainShape)
        state
    (DigestDecision proposition, "accepted", [evidence]) ->
      insertProof located evidence proposition state
    (DigestDecision _, "rejected", [reason]) ->
      insertBindingMeta (locatedSpan located) reason
        (BindingMeta Unrestricted (TyOpaque "DigestFailure") PlainShape) state
    (StoreDecision, "success", [identifier]) ->
      insertBindingMeta (locatedSpan located) identifier
        (BindingMeta Unrestricted (TyOpaque "UploadId") PlainShape) state
    (StoreDecision, "failure", [reason]) ->
      insertBindingMeta (locatedSpan located) reason
        (BindingMeta Unrestricted (TyOpaque "StorageFailure") PlainShape) state
    _ -> throw located TypeMismatch
      "decision arm binder shape is incompatible with the decision result"

insertProof
  :: Located a
  -> Text
  -> Proposition
  -> SurfaceState
  -> Either SurfaceCheckError SurfaceState
insertProof located name proposition =
  insertBindingMeta (locatedSpan located) name
    (BindingMeta Unrestricted (TyProof proposition) PlainShape)

evalOffer
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> [Located CaseArm]
  -> Either SurfaceCheckError [SurfacePath]
evalOffer environment state located endpointExpression arms = do
  endpoint <- endpointName endpointExpression
  endpointMeta <- lookupMeta endpointExpression endpoint state
  branches <- sessionOfferBranches located endpointMeta
  mapBranchExhaustiveness
    located branches (map (casePatternLabel . caseArmPattern . locatedValue) arms)
  concat <$> mapM (checkOfferArm environment state endpoint) arms

checkOfferArm
  :: SurfaceEnvironment
  -> SurfaceState
  -> Text
  -> Located CaseArm
  -> Either SurfaceCheckError [SurfacePath]
checkOfferArm environment incoming endpoint locatedArm = do
  let pattern' = caseArmPattern (locatedValue locatedArm)
      label = casePatternLabel pattern'
      (temp, state1) = freshName "$offer" incoming
  step <- mapSession locatedArm $
    offerEndpoint
      (Name endpoint)
      temp
      label
      (resourceContext (stateCore state1))
  let state2 = applySessionContext endpoint (stepContext step) state1
  (successor, state3) <- extractLinearTemp (locatedSpan locatedArm) temp state2
  rebound <- insertBindingMeta (locatedSpan locatedArm) endpoint
    (BindingMeta Linear (scalarType successor) PlainShape) state3
  withPayload <- bindOfferPayload
    locatedArm
    (stepMessage step)
    (casePatternBinders pattern')
    rebound
  checkScopedValueBlock
    environment incoming withPayload (caseArmBody (locatedValue locatedArm))

bindOfferPayload
  :: Located a
  -> Maybe MessageSpec
  -> [Text]
  -> SurfaceState
  -> Either SurfaceCheckError SurfaceState
bindOfferPayload _ Nothing [] state = Right state
bindOfferPayload located (Just message) [name] state =
  insertBindingMeta (locatedSpan located) name
    (BindingMeta
      (messageMode (messageType message))
      (messageType message)
      (shapeForBinding name (shapeForType (messageType message))))
    state
bindOfferPayload located Nothing (_ : _) _ =
  throw located TypeMismatch "branch carries no payload"
bindOfferPayload located (Just _) _ _ =
  throw located TypeMismatch "branch payload binder arity mismatch"

checkValueBlock
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located Block
  -> Either SurfaceCheckError [SurfacePath]
checkValueBlock environment state locatedBlock =
  case blockStatements (locatedValue locatedBlock) of
    [] -> Right [valuePath state RuntimeUnit]
    statements -> do
      prefix <- checkStatements environment [continuePath state] (init statements)
      concat <$> mapM (finish (last statements)) prefix
  where
    finish statement path
      | pathControl path /= PathContinue = Right [path]
      | otherwise = case locatedValue statement of
          ExpressionStatement expression ->
            evalExpression environment (pathState path) expression
          _ -> checkStatement environment statement path

checkScopedValueBlock
  :: SurfaceEnvironment
  -> SurfaceState
  -> SurfaceState
  -> Located Block
  -> Either SurfaceCheckError [SurfacePath]
checkScopedValueBlock environment incoming scoped body = do
  paths <- checkValueBlock environment scoped body
  mapM
    (pruneScopedPath
      (locatedSpan body)
      (Map.keysSet (stateBindings incoming)))
    paths

pruneScopedPath
  :: SourceSpan
  -> Set Text
  -> SurfacePath
  -> Either SurfaceCheckError SurfacePath
pruneScopedPath _ _ path | pathControl path /= PathContinue = Right path
pruneScopedPath span' incoming path = do
  let state = pathState path
      localNames = Map.keysSet (stateBindings state) `Set.difference` incoming
      locals = mapMaybe
        (\name -> fmap ((,) name) (Map.lookup name (stateBindings state)))
        (Set.toList localNames)
  mapM_ ensureDiscardable locals
  next <- foldM (\current name -> removeScopedBinding span' name current)
    state
    (map fst locals)
  Right path { pathState = next }
  where
    ensureDiscardable (name, meta)
      | bindingMode meta == Linear = Left SurfaceCheckError
          { surfaceErrorSpan = span'
          , surfaceErrorClass = LinearCompletion
          , surfaceErrorDetail = "linear branch-local binding remains live: " <> name
          }
      | otherwise = Right ()

evalFail
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> FailureTarget
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalFail environment state located target resourceExpression = do
  resourceName <- namedExpression StructuralUse resourceExpression
  next <- if failureTargetClass target == "recognition"
    then failRecognition state located resourceName target
    else consumeFatal state located resourceName
  ensureTerminalState
    environment
    (locatedSpan located)
    (Just (Outcome "failure"))
    next
  Right
    [ SurfacePath
        (PathFailed (failureTargetClass target) "explicit")
        next
        Nothing
    ]

failRecognition
  :: SurfaceState
  -> Located a
  -> Name
  -> FailureTarget
  -> Either SurfaceCheckError SurfaceState
failRecognition state located pendingName target =
  case failureTargetArguments target of
    [reasonExpression] -> do
      reason <- namedExpression RecognitionProvenance reasonExpression
      reasonMeta <- lookupMeta reasonExpression (unName reason) state
      pendingMeta <- lookupMeta located (unName pendingName) state
      spec <- case bindingType pendingMeta of
        TyPendingRecv pending -> Right pending
        _ -> throw located RecognitionProvenance
          "recognition failure target is not PendingRecv"
      case bindingShape reasonMeta of
        RecognitionFailureShape failure -> do
          context <- mapRecognition located $
            failPendingRecognition
              pendingName
              failure
              (resourceContext (stateCore state))
          Right (applySessionContext (unName pendingName) context state)
        LegacyRecognitionFailureShape grammar frame
          | grammar == pendingGrammar spec && frame == pendingFrame spec ->
              consumeFatal state located pendingName
          | otherwise -> throw reasonExpression RecognitionProvenance
              "recognition failure belongs to a different frame"
        _ -> throw reasonExpression RecognitionProvenance
          "failure value lacks matching recognition provenance"
    _ -> throw located RecognitionProvenance
      "recognition failure requires exactly one reason value"

consumeFatal :: SurfaceState -> Located a -> Name -> Either SurfaceCheckError SurfaceState
consumeFatal state located name = do
  (_, context) <- mapCore (locatedSpan located) StructuralUse $
    consumeLinear name (resourceContext (stateCore state))
  Right (applySessionContext (unName name) context state)

evalClose
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalClose environment state located target = do
  (endpoint, outcome) <- resolveCloseTarget state target
  step <- mapSession located $
    closeEndpoint (Name endpoint) outcome (resourceContext (stateCore state))
  let next = applySessionContext endpoint (stepContext step) state
  ensureTerminalState environment (locatedSpan located) (Just outcome) next
  Right [SurfacePath (PathClosed outcome) next Nothing]

resolveCloseTarget
  :: SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (Text, Outcome)
resolveCloseTarget state target = case locatedValue target of
  VariableExpression name
    | name `elem` ["success", "failure", "cancelled"] -> do
        endpoint <- currentEndpoint target state
        Right (endpoint, Outcome name)
  VariableExpression name -> do
    meta <- lookupMeta target name state
    case bindingType meta of
      TyEndpoint session -> do
        headSession <- mapSession target (exposeSessionHead session)
        case headSession of
          End outcome -> Right (name, outcome)
          _ -> throw target SessionAction "endpoint is not at an end state"
      _ -> throw target SessionAction "close requires an endpoint or terminal outcome"
  _ -> throw target SessionAction "close target must be a name"

evalRelease
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalRelease environment state located ownerExpression = do
  name <- namedExpression ReleaseCompetence ownerExpression
  meta <- lookupMeta ownerExpression (unName name) state
  when (bindingMode meta == Unrestricted) $
    throw ownerExpression ReleaseCompetence
      "release requires an owning affine or linear resource"
  transition <- case selectReleaseTransition environment (bindingType meta) of
    Left selectionError ->
      throw ownerExpression ReleaseCompetence (Text.pack (show selectionError))
    Right selected -> Right selected
  (_, next) <- moveVariable ownerExpression (unName name) state
  case releaseTransitionOutcome transition of
    ReleaseContinuesUnit -> Right [valuePath next RuntimeUnit]
    ReleaseTerminates outcome -> do
      ensureTerminalState environment (locatedSpan located) (Just outcome) next
      Right [SurfacePath (PathClosed outcome) next Nothing]
    ReleaseFails failureClass detail -> do
      ensureTerminalState environment
        (locatedSpan located)
        (Just (Outcome "failure"))
        next
      Right [SurfacePath (PathFailed failureClass detail) next Nothing]
    ReleaseBranchSensitive outcomes ->
      throw ownerExpression ReleaseCompetence
        ("branch-sensitive release escaped competence selection: "
          <> Text.pack (show outcomes))

evalAccept
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Located SurfaceType
  -> Either SurfaceCheckError [SurfacePath]
evalAccept environment state located valueExpression surfaceTarget = do
  valueName <- namedExpression TypeMismatch valueExpression
  (_, target, _) <- resolveSurfaceType environment state surfaceTarget
  result <- case checkValue
      (VVar valueName)
      (rewriteTy state target)
      (stateCore state) of
    Left errorValue -> Left (valueError located errorValue)
    Right checked -> Right checked
  let next = applyValueResult (unName valueName) state result
      mode = maybe Unrestricted bindingMode $
        Map.lookup (unName valueName) (stateBindings state)
  Right
    [ valuePath next (RuntimeScalar (ScalarValue mode target PlainShape))
    ]

evalProve
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceProposition
  -> Either SurfaceCheckError [SurfacePath]
evalProve environment state located propositionSource = do
  proposition <- mapElaboration propositionSource $
    elaborateProposition (elaborationEnv environment state) propositionSource
  plan <- mapFocusing propositionSource $
    focusProposition
      (surfaceStaticContext environment)
      (stateCore state)
      proposition
  let requirements = focusPrerequisites plan ++ [focusGoal plan]
      unresolved = filter (not . dischargedRequirement) requirements
  if null unresolved
    then proofValue proposition
    else if any ((== FocusNeedsExplicitMechanism) . focusedMechanism) unresolved
      then throw located OpaqueProof
        "opaque claim cannot be introduced by generic prove"
      else if propositionMentionsUnchecked state proposition
        then throw located UncheckedArithmetic
          "unchecked machine arithmetic has no mathematical proof postcondition"
        else do
          solved <- mapM (solveRequirement state) unresolved
          if and solved
            then proofValue proposition
            else throw located MissingEvidence
              "transparent proposition is not established by checked evidence/certificate"
  where
    proofValue proposition = Right
      [ valuePath state (RuntimeScalar
          (ScalarValue Unrestricted (TyProof proposition) PlainShape))
      ]

evalFallback
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Fallback
  -> Either SurfaceCheckError [SurfacePath]
evalFallback environment state located base fallback = do
  case fallback of
    FailFallback _ -> validateFatalFallback environment state located base
    RejectFallback _ -> Right ()
  evalExpression environment state base

validateFatalFallback
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located a
  -> Located SurfaceExpression
  -> Either SurfaceCheckError ()
validateFatalFallback environment state located base = do
  failureState <- case locatedValue base of
    ReceiveFrameExpression endpoint -> consumeEndpoint endpoint
    ReceiveExactExpression _ endpoint _ -> consumeEndpoint endpoint
    SendExpression _ endpoint -> consumeEndpoint endpoint
    SendExactExpression _ endpoint -> consumeEndpoint endpoint
    _ -> Right state
  ensureTerminalState
    environment
    (locatedSpan located)
    (Just (Outcome "failure"))
    failureState
  where
    consumeEndpoint expression = do
      endpoint <- endpointName expression
      (_, context) <- mapCore (locatedSpan located) StructuralUse $
        consumeLinear (Name endpoint) (resourceContext (stateCore state))
      Right (applySessionContext endpoint context state)

checkSelectedPayload
  :: SurfaceEnvironment
  -> SurfaceState
  -> Maybe MessageSpec
  -> [Located SurfaceExpression]
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError SurfaceState
checkSelectedPayload _ state Nothing [] _ = Right state
checkSelectedPayload environment state (Just message) [argument] explicitEvidence =
  case locatedValue argument of
    VariableExpression name -> do
      result <- case explicitEvidence of
        Just evidence | isRefined (messageType message) -> do
          evidenceName <- namedExpression MissingEvidence evidence
          mapValueResult argument $
            checkValueUsing
              evidenceName
              (VVar (Name name))
              (rewriteTy state (messageType message))
              (stateCore state)
        _ -> mapValueResult argument $
          checkValue
            (VVar (Name name))
            (rewriteTy state (messageType message))
            (stateCore state)
      Right (applyValueResult name state result)
    _ -> do
      scalar <- inferReadOnlyScalar environment state argument
      checkScalarAgainst state argument scalar (messageType message)
      Right state
checkSelectedPayload _ _ Nothing (_ : _) _ = Left SurfaceCheckError
  { surfaceErrorSpan = syntheticSpan
  , surfaceErrorClass = TypeMismatch
  , surfaceErrorDetail = "branch carries no payload"
  }
checkSelectedPayload _ _ (Just _) _ _ = Left SurfaceCheckError
  { surfaceErrorSpan = syntheticSpan
  , surfaceErrorClass = TypeMismatch
  , surfaceErrorDetail = "branch payload arity mismatch"
  }

checkConfiguredRequirement
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located a
  -> Maybe Proposition
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError ()
checkConfiguredRequirement _ _ _ Nothing _ = Right ()
checkConfiguredRequirement environment state located (Just proposition) explicitEvidence =
  checkRequirement environment state located proposition explicitEvidence

checkRequirement
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located a
  -> Proposition
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError ()
checkRequirement environment state located proposition explicitEvidence = do
  let required = rewriteProposition state proposition
  if hasExactEvidence required state
    then Right ()
    else case explicitEvidence of
      Just expression -> do
        evidenceName <- namedExpression MissingEvidence expression
        meta <- lookupMeta expression (unName evidenceName) state
        case evidenceProposition (bindingType meta) of
          Just actual
            | normalizeProposition (rewriteProposition state actual)
                == normalizeProposition required -> Right ()
          _ -> throw expression MissingEvidence
              "explicit evidence proves a different proposition/context/subject"
      Nothing -> do
        plan <- mapFocusing located $
          focusProposition
            (surfaceStaticContext environment)
            (stateCore state)
            required
        if dischargedRequirement (focusGoal plan)
            && all dischargedRequirement (focusPrerequisites plan)
          then Right ()
          else throw located MissingEvidence
            ("required proposition is not established: " <> Text.pack (show required))

hasExactEvidence :: Proposition -> SurfaceState -> Bool
hasExactEvidence proposition state =
  any matches $ Map.elems $ unrestrictedBindings $ resourceContext $ stateCore state
  where
    required = normalizeProposition proposition
    matches ty = case evidenceProposition ty of
      Just actual ->
        normalizeProposition (rewriteProposition state actual) == required
      Nothing -> False

checkScalarAgainst
  :: SurfaceState
  -> Located a
  -> ScalarValue
  -> Ty
  -> Either SurfaceCheckError ()
checkScalarAgainst state located scalar expected =
  case compareTypes
      (rewriteTy state (scalarType scalar))
      (rewriteTy state expected) of
    DefinitionallyEqual -> Right ()
    RequiresPropositionalEquality ->
      throw located ExplicitTransport
        "dependent value requires explicit equality transport"
    IncompatibleTypes ->
      throw located TypeMismatch
        "value type is incompatible with protocol/target type"

moveOrReadValue
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
moveOrReadValue environment state expression = case locatedValue expression of
  VariableExpression name -> moveVariable expression name state
  _ -> do
    scalar <- inferReadOnlyScalar environment state expression
    Right (scalar, state)

joinExclusive :: SourceSpan -> [SurfacePath] -> Either SurfaceCheckError [SurfacePath]
joinExclusive _ [] = Right []
joinExclusive span' paths = do
  let continuing = filter ((== PathContinue) . pathControl) paths
      stopped = filter ((/= PathContinue) . pathControl) paths
  case continuing of
    [] -> Right stopped
    [single] -> Right (stopped ++ [single])
    _ -> do
      joined <- mapCore span' IncompatibleBranchResidue $
        joinContinuing $ map (resourceContext . stateCore . pathState) continuing
      state <- joinMetadata span' continuing joined
      Right (stopped ++ [continuePath state])

joinMetadata
  :: SourceSpan
  -> [SurfacePath]
  -> ResourceContext
  -> Either SurfaceCheckError SurfaceState
joinMetadata span' paths joined = do
  let states = map pathState paths
      firstState = head states
      surviving = Map.filterWithKey
        (bindingSurvives joined)
        (stateBindings firstState)
  mapM_ (ensureAgrees surviving) (tail states)
  Right firstState
    { stateCore = (stateCore firstState) { resourceContext = joined }
    , stateBindings = surviving
    , stateFresh = maximum (map stateFresh states)
    , stateFrame = maximum (map stateFrame states)
    , stateActiveEndpoint = commonActiveEndpoint states surviving
    }
  where
    ensureAgrees surviving state = mapM_
      (\(name, meta) -> case Map.lookup name (stateBindings state) of
        Just other | other == meta -> Right ()
        _ -> Left SurfaceCheckError
          { surfaceErrorSpan = span'
          , surfaceErrorClass = IncompatibleBranchResidue
          , surfaceErrorDetail =
              "continuing branches disagree on metadata for " <> name
          })
      (Map.toList surviving)

bindingSurvives :: ResourceContext -> Text -> BindingMeta -> Bool
bindingSurvives context name meta = case bindingMode meta of
  Unrestricted -> Map.member (Name name) (unrestrictedBindings context)
  Affine -> Map.member (Name name) (affineBindings context)
  Linear -> Map.member (Name name) (linearBindings context)

commonActiveEndpoint :: [SurfaceState] -> Map.Map Text BindingMeta -> Maybe Text
commonActiveEndpoint states surviving = case map stateActiveEndpoint states of
  first : rest | all (== first) rest -> first
  _ -> case
    [ name
    | (name, meta) <- Map.toList surviving
    , isEndpointTy (bindingType meta)
    ] of
      [name] -> Just name
      _ -> Nothing

finalizePath
  :: SurfaceEnvironment
  -> SourceSpan
  -> SurfacePath
  -> Either SurfaceCheckError SurfacePath
finalizePath environment span' path = do
  case pathControl path of
    PathContinue -> ensureTerminalState environment span' Nothing (pathState path)
    PathReturn _ -> ensureTerminalState environment span' Nothing (pathState path)
    PathClosed outcome ->
      ensureTerminalState environment span' (Just outcome) (pathState path)
    PathFailed _ _ ->
      ensureTerminalState environment span' (Just (Outcome "failure")) (pathState path)
  Right path

ensureTerminalState
  :: SurfaceEnvironment
  -> SourceSpan
  -> Maybe Outcome
  -> SurfaceState
  -> Either SurfaceCheckError ()
ensureTerminalState environment span' maybeOutcome state =
  let allowed = maybe Set.empty
        (\outcome -> Map.findWithDefault Set.empty outcome (surfaceTerminalAllowances environment))
        maybeOutcome
      context = resourceContext (stateCore state)
      reduced = context
        { linearBindings = Map.withoutKeys
            (linearBindings context)
            (Set.map Name allowed)
        }
  in case ensureComplete reduced of
      Right () -> Right ()
      Left errorValue -> Left SurfaceCheckError
        { surfaceErrorSpan = span'
        , surfaceErrorClass = LinearCompletion
        , surfaceErrorDetail = Text.pack (show errorValue)
        }

toCoreControl :: SurfacePath -> Control
toCoreControl path = case pathControl path of
  PathContinue -> Continue
  PathReturn ty -> Return ty
  PathClosed outcome -> Closed outcome
  PathFailed failureClass detail -> Failed failureClass detail

mapBranchExhaustiveness
  :: Located a
  -> [Branch]
  -> [Text]
  -> Either SurfaceCheckError ()
mapBranchExhaustiveness located branches handlers =
  case checkBranchExhaustiveness branches handlers of
    Right () -> Right ()
    Left errorValue -> Left SurfaceCheckError
      { surfaceErrorSpan = locatedSpan located
      , surfaceErrorClass = BranchExhaustiveness
      , surfaceErrorDetail = Text.pack (show errorValue)
      }

dischargedRequirement :: FocusedRequirement -> Bool
dischargedRequirement requirement = case focusedMechanism requirement of
  FocusByDefinition -> True
  FocusByEvidence _ -> True
  _ -> False

solveRequirement :: SurfaceState -> FocusedRequirement -> Either SurfaceCheckError Bool
solveRequirement state requirement = case focusedMechanism requirement of
  FocusNeedsDecisionProcedure ->
    case proposeDecisionCertificate
      (stateCore state)
      []
      (focusedCanonical requirement) of
        Nothing -> Right False
        Just certificate -> case checkDecisionCertificate
            (stateCore state)
            []
            (focusedCanonical requirement)
            certificate of
          Right () -> Right True
          Left _ -> Right False
  _ -> Right False

propositionMentionsUnchecked :: SurfaceState -> Proposition -> Bool
propositionMentionsUnchecked state proposition = any tainted (propositionNames proposition)
  where
    tainted (Name name) = case Map.lookup name (stateBindings state) of
      Just meta -> bindingShape meta == UncheckedArithmeticShape
      Nothing -> False

propositionNames :: Proposition -> [Name]
propositionNames proposition = case proposition of
  Truth -> []
  Falsehood -> []
  Equal left right -> names left ++ names right
  NotEqual left right -> names left ++ names right
  LessThan left right -> names left ++ names right
  LessEqual left right -> names left ++ names right
  Member left right -> names left ++ names right
  Disjoint left right -> names left ++ names right
  Conjunction left right -> propositionNames left ++ propositionNames right
  Disjunction left right -> propositionNames left ++ propositionNames right
  Negation inner -> propositionNames inner
  Atom _ arguments -> concatMap names arguments
  where
    names = termNames

termNames :: RefTerm -> [Name]
termNames term = case term of
  RefVar name -> [name]
  RefField base _ _ -> termNames base
  RefLen value -> termNames value
  RefToNat value -> termNames value
  RefAdd left right -> termNames left ++ termNames right
  RefSub left right -> termNames left ++ termNames right
  RefScale _ value -> termNames value
  _ -> []

applyValueResult :: Text -> SurfaceState -> ValueResult -> SurfaceState
applyValueResult source state result =
  let next = state { stateCore = valueResultState result }
      coreName = Name source
      context = resourceContext (stateCore next)
      stillPresent =
        Map.member coreName (unrestrictedBindings context)
          || Map.member coreName (affineBindings context)
          || Map.member coreName (linearBindings context)
  in if stillPresent then next else consumeSurfaceName source next

serverSupportedTerm :: RefTerm
serverSupportedTerm = RefVar (Name "serverSupported")

helloVersionsTerm :: RefTerm
helloVersionsTerm = RefField (RefVar (Name "hello")) "versions" versionSetSort
