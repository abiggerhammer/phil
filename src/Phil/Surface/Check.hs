{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , FieldInfo (..)
  , SurfaceShape (..)
  , InitialBinding (..)
  , PrimitiveSemantics (..)
  , SurfaceEnvironment (..)
  , SurfaceCheckResult (..)
  , emptySurfaceEnvironment
  , checkSurfaceComponent
  ) where

import Control.Monad (foldM, unless, when)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , consumeLinear
  , emptyContext
  , endSharedLoan
  , ensureComplete
  , insertBinding
  , joinContinuing
  , startSharedLoan
  , useBinding
  )
import Phil.Core.Decision
  ( checkDecisionCertificate
  , proposeDecisionCertificate
  )
import Phil.Core.Focusing
  ( FocusMechanism (..)
  , FocusPlan (..)
  , FocusedRequirement (..)
  , FocusingError
  , checkBranchExhaustiveness
  , elaborateRefTermAs
  , focusProposition
  )
import Phil.Core.Recognition
  ( ParsedWitness
  , PendingRawView
  , RecognitionError
  , RecognitionFailure
  , beginRawLoan
  , commitContext
  , commitReceive
  , failPendingRecognition
  , parsedValueName
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
  , SessionError
  , SessionStep (..)
  , closeEndpoint
  , exposeSessionHead
  , offerEndpoint
  , receiveEndpoint
  , selectEndpoint
  , sendEndpoint
  )
import Phil.Core.SortCheck (refSortOfTy)
import Phil.Core.Static
  ( ClaimDefinition (..)
  , StaticContext
  , lookupClaim
  )
import Phil.Core.Syntax
  ( Branch (..)
  , Control (..)
  , FrameId (..)
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
  , ValueError (..)
  , checkValue
  , checkValueUsing
  , compareTypes
  )
import Phil.Surface.Elaborate
  ( ElaborationEnv
  , ElaborationError
  , elaborateProposition
  , elaborateRefTerm
  , elaborateType
  , emptyElaborationEnv
  , withProjectionSort
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
  , SurfaceType (..)
  )

-- | Stable rejection classes used by the Phase 0 conformance harness.  These
-- are deliberately coarser than individual implementation errors but finer
-- than "the checker rejected it somewhere".
data RejectionClass
  = StructuralUse
  | LinearCompletion
  | SessionAction
  | BranchExhaustiveness
  | IllegalProjection
  | MissingEvidence
  | ExplicitTransport
  | IncompatibleBranchResidue
  | ControlAfterTerminal
  | RecognitionProvenance
  | BorrowEscape
  | OpaqueProof
  | UncheckedArithmetic
  | UnknownPrimitive
  | TypeMismatch
  deriving (Eq, Ord, Show)

data SurfaceCheckError = SurfaceCheckError
  { surfaceErrorSpan :: SourceSpan
  , surfaceErrorClass :: RejectionClass
  , surfaceErrorDetail :: Text
  }
  deriving (Eq, Show)

data FieldInfo = FieldInfo
  { fieldType :: Ty
  , fieldSort :: RefSort
  , fieldAlias :: Maybe RefTerm
  }
  deriving (Eq, Show)

data SurfaceShape
  = PlainShape
  | RecordShape Text (Map Text FieldInfo)
  | OwnedBytesShape RefTerm
  | PendingRawShape PendingRawView
  | LegacyRawShape Name GrammarId FrameId
  | BorrowedViewShape Name
  | ParsedShape ParsedWitness Text
  | ExternalParsedShape Text FrameId
  | FixtureRawShape FrameId
  | DecisionShape DecisionKind
  | UncheckedArithmeticShape
  | ForgedParsedShape
  deriving (Eq, Show)

data InitialBinding = InitialBinding
  { initialMode :: Mode
  , initialType :: Ty
  , initialShape :: SurfaceShape
  }
  deriving (Eq, Show)

data PrimitiveSemantics
  = PrimitiveSupportedVersions
  | PrimitiveSha256
  | PrimitiveShouldCancel
  | PrimitiveChooseSupported
  | PrimitiveStore
  | PrimitiveFixtureBytes
  | PrimitiveUncheckedU32Add
  | PrimitiveNewCancellationScope
  | PrimitiveAllocateLinearBuffer
  | PrimitiveRecordUploadId
  | PrimitiveConsumeBeginPolicyEvidence
  | PrimitiveUse
  | PrimitiveInspect
  | PrimitiveAuthorizeStore
  | PrimitiveDelegate
  | PrimitiveContinueCommonState
  | PrimitiveHandlePayload
  deriving (Eq, Ord, Show)

data SurfaceEnvironment = SurfaceEnvironment
  { surfaceStaticContext :: StaticContext
  , surfaceInitialBindings :: Map Text InitialBinding
  , surfacePrimitives :: Map Text PrimitiveSemantics
  , surfaceSelectRequirements :: Map Text [Proposition]
  , surfaceReceiveExactRequirement :: Maybe Proposition
  , surfaceTerminalAllowances :: Map Outcome (Set Text)
  , surfaceExpectedProvides :: Maybe Ty
  , surfaceLegacyReceiveFrameRaw :: Bool
  }
  deriving (Eq, Show)

data SurfaceCheckResult = SurfaceCheckResult
  { checkedComponentName :: Text
  , checkedTerminalControls :: [Control]
  }
  deriving (Eq, Show)

emptySurfaceEnvironment :: StaticContext -> SurfaceEnvironment
emptySurfaceEnvironment staticContext = SurfaceEnvironment
  { surfaceStaticContext = staticContext
  , surfaceInitialBindings = Map.empty
  , surfacePrimitives = Map.empty
  , surfaceSelectRequirements = Map.empty
  , surfaceReceiveExactRequirement = Nothing
  , surfaceTerminalAllowances = Map.empty
  , surfaceExpectedProvides = Nothing
  , surfaceLegacyReceiveFrameRaw = False
  }

data BindingMeta = BindingMeta
  { bindingMode :: Mode
  , bindingType :: Ty
  , bindingShape :: SurfaceShape
  }
  deriving (Eq, Show)

data SurfaceState = SurfaceState
  { stateCore :: CheckState
  , stateBindings :: Map Text BindingMeta
  , stateFresh :: Int
  , stateFrame :: Int
  , stateActiveEndpoint :: Maybe Text
  }
  deriving (Eq, Show)

data ScalarValue = ScalarValue
  { scalarMode :: Mode
  , scalarType :: Ty
  , scalarShape :: SurfaceShape
  }
  deriving (Eq, Show)

data RuntimeValue
  = RuntimeScalar ScalarValue
  | RuntimeTuple [RuntimeValue]
  | RuntimeUnit
  deriving (Eq, Show)

data PathControl
  = PathContinue
  | PathReturn Ty
  | PathClosed Outcome
  | PathFailed Text Text
  deriving (Eq, Show)

data SurfacePath = SurfacePath
  { surfacePathControl :: PathControl
  , surfacePathState :: SurfaceState
  , surfacePathValue :: Maybe RuntimeValue
  }
  deriving (Eq, Show)

data DecisionKind
  = BooleanDecision
  | ChooseSupportedDecision
  | RecognitionDecision ParsedWitness RecognitionFailure Text
  | LegacyRecognitionDecision Name GrammarId FrameId Text
  | ValidationDecision Text Name Name
  | DigestDecision Proposition
  | StoreDecision
  deriving (Eq, Show)

checkSurfaceComponent
  :: SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCheckError SurfaceCheckResult
checkSurfaceComponent environment locatedComponent = do
  initial <- initializeState environment (locatedValue locatedComponent)
  checkProvides environment initial (locatedValue locatedComponent)
  paths <- checkBlock environment initial (componentBody (locatedValue locatedComponent))
  finalized <- mapM (finalizePath environment (locatedSpan locatedComponent)) paths
  let controls = map pathControlToCore finalized
  pure SurfaceCheckResult
    { checkedComponentName = componentName (locatedValue locatedComponent)
    , checkedTerminalControls = controls
    }

initializeState :: SurfaceEnvironment -> Component -> Either SurfaceCheckError SurfaceState
initializeState environment component = do
  base <- foldM insertInitial emptySurfaceState (Map.toAscList (surfaceInitialBindings environment))
  foldM insertParameter base (componentParameters component)
  where
    insertInitial state (name, binding) =
      insertNamedBinding noSpan name (BindingMeta
        (initialMode binding)
        (initialType binding)
        (initialShape binding)) state

    insertParameter state locatedParameter =
      let parameter = locatedValue locatedParameter
          name = parameterName parameter
      in case Map.lookup name (stateBindings state) of
          Just existing -> do
            case parameterType parameter of
              Nothing -> pure ()
              Just surfaceTy -> do
                (mode, ty, _) <- resolveSurfaceType environment state surfaceTy
                unless (mode == bindingMode existing && sameTy state ty (bindingType existing)) $
                  throw locatedParameter TypeMismatch "parameter type disagrees with the architecture-supplied binding"
            pure state
          Nothing ->
            case parameterType parameter of
              Nothing -> throw locatedParameter TypeMismatch "untyped parameter has no architecture-supplied type"
              Just surfaceTy -> do
                (mode, ty, shape) <- resolveSurfaceType environment state surfaceTy
                insertNamedBinding (locatedSpan locatedParameter) name (BindingMeta mode ty shape) state

emptySurfaceState :: SurfaceState
emptySurfaceState = SurfaceState
  { stateCore = emptyCheckState
  , stateBindings = Map.empty
  , stateFresh = 0
  , stateFrame = 0
  , stateActiveEndpoint = Nothing
  }

checkProvides :: SurfaceEnvironment -> SurfaceState -> Component -> Either SurfaceCheckError ()
checkProvides environment state component =
  case (surfaceExpectedProvides environment, componentProvides component) of
    (Nothing, _) -> Right ()
    (Just expected, Just surfaceTy) -> do
      (_, actual, _) <- resolveSurfaceType environment state surfaceTy
      unless (sameTy state actual expected) $
        throw surfaceTy TypeMismatch "component provider type does not match the architecture contract"
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
checkBlock environment initial locatedBlock =
  checkStatements environment [continuePath initial] (blockStatements (locatedValue locatedBlock))

checkStatements
  :: SurfaceEnvironment
  -> [SurfacePath]
  -> [Located Statement]
  -> Either SurfaceCheckError [SurfacePath]
checkStatements _ paths [] = Right paths
checkStatements environment paths (statement : rest) = do
  let continuing = filter ((== PathContinue) . surfacePathControl) paths
      terminal = filter ((/= PathContinue) . surfacePathControl) paths
  when (null continuing) $
    throw statement ControlAfterTerminal "statement appears after every incoming path has terminated"
  advanced <- concat <$> mapM (checkStatement environment statement) continuing
  checkStatements environment (terminal ++ advanced) rest

checkStatement
  :: SurfaceEnvironment
  -> Located Statement
  -> SurfacePath
  -> Either SurfaceCheckError [SurfacePath]
checkStatement environment locatedStatement path =
  case locatedValue locatedStatement of
    LetStatement pattern' expression -> do
      evaluated <- evalExpression environment (surfacePathState path) expression
      bound <- concat <$> mapM (bindEvaluatedPath environment pattern') evaluated
      joinExclusive environment (locatedSpan locatedStatement) bound
    ReturnStatement expression -> do
      evaluated <- evalExpression environment (surfacePathState path) expression
      mapM (returnEvaluated environment (locatedSpan locatedStatement)) evaluated
    ExpressionStatement expression -> do
      evaluated <- evalExpression environment (surfacePathState path) expression
      checked <- mapM (discardExpressionValue (locatedSpan locatedStatement)) evaluated
      joinExclusive environment (locatedSpan locatedStatement) checked

bindEvaluatedPath
  :: SurfaceEnvironment
  -> Located Pattern
  -> SurfacePath
  -> Either SurfaceCheckError [SurfacePath]
bindEvaluatedPath _ _ path | surfacePathControl path /= PathContinue = Right [path]
bindEvaluatedPath _ pattern' path =
  case surfacePathValue path of
    Nothing -> throw pattern' TypeMismatch "expression did not produce a bindable value"
    Just value -> do
      state <- bindPattern pattern' value (surfacePathState path)
      Right [continuePath state]

returnEvaluated
  :: SurfaceEnvironment
  -> SourceSpan
  -> SurfacePath
  -> Either SurfaceCheckError SurfacePath
returnEvaluated environment span' path
  | surfacePathControl path /= PathContinue = Right path
  | otherwise = do
      let ty = maybe TyUnit runtimeType (surfacePathValue path)
          state = surfacePathState path
      ensureTerminalState environment span' Nothing state
      Right path
        { surfacePathControl = PathReturn ty
        , surfacePathValue = Nothing
        }

runtimeType :: RuntimeValue -> Ty
runtimeType RuntimeUnit = TyUnit
runtimeType (RuntimeScalar scalar) = scalarType scalar
runtimeType (RuntimeTuple values) = TyOpaque ("Tuple" <> Text.pack (show (length values)))

discardExpressionValue :: SourceSpan -> SurfacePath -> Either SurfaceCheckError SurfacePath
discardExpressionValue _ path | surfacePathControl path /= PathContinue = Right path
discardExpressionValue span' path =
  case surfacePathValue path of
    Just (RuntimeScalar scalar)
      | scalarMode scalar /= Unrestricted -> Left SurfaceCheckError
          { surfaceErrorSpan = span'
          , surfaceErrorClass = LinearCompletion
          , surfaceErrorDetail = "restricted expression result is discarded instead of being bound or transferred"
          }
    Just (RuntimeTuple values)
      | any runtimeRestricted values -> Left SurfaceCheckError
          { surfaceErrorSpan = span'
          , surfaceErrorClass = LinearCompletion
          , surfaceErrorDetail = "tuple expression discards a restricted result"
          }
    _ -> Right path { surfacePathValue = Nothing }

runtimeRestricted :: RuntimeValue -> Bool
runtimeRestricted RuntimeUnit = False
runtimeRestricted (RuntimeScalar scalar) = scalarMode scalar /= Unrestricted
runtimeRestricted (RuntimeTuple values) = any runtimeRestricted values

continuePath :: SurfaceState -> SurfacePath
continuePath state = SurfacePath PathContinue state Nothing

evalExpression
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalExpression environment state locatedExpression =
  case locatedValue locatedExpression of
    VariableExpression name -> do
      (scalar, next) <- moveVariable locatedExpression name state
      pure [valuePath next (RuntimeScalar scalar)]
    IntegerExpression literal ->
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted (TyOpaque ("Integer[" <> Text.pack (show literal) <> "]")) PlainShape))]
    BooleanExpression _ ->
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted TyBool (DecisionShape BooleanDecision)))]
    UnitExpression -> pure [valuePath state RuntimeUnit]
    TupleExpression expressions -> do
      (values, next) <- evalSequentialValues environment state expressions
      pure [valuePath next (RuntimeTuple values)]
    FieldExpression base field -> do
      (scalar, next) <- readField environment state locatedExpression base field
      pure [valuePath next (RuntimeScalar scalar)]
    ConstructExpression constructor fields -> do
      scalar <- constructValue environment state locatedExpression constructor fields
      pure [valuePath state (RuntimeScalar scalar)]
    CallExpression name arguments -> evalPrimitive environment state locatedExpression name arguments
    ReceiveExpression messageTy endpoint -> evalReceive environment state locatedExpression messageTy endpoint
    ReceiveFrameExpression endpoint -> evalReceiveFrame environment state locatedExpression endpoint
    RecognizeExpression grammar raw -> evalRecognize environment state locatedExpression grammar raw
    ValidateExpression claim context subject -> evalValidate environment state locatedExpression claim context subject
    SendExpression value endpoint -> evalSend environment False state locatedExpression value endpoint
    SendExactExpression value endpoint -> evalSend environment True state locatedExpression value endpoint
    ReceiveExactExpression count endpoint evidence ->
      evalReceiveExact environment state locatedExpression count endpoint evidence
    SelectExpression branch endpoint evidence ->
      evalSelect environment state locatedExpression branch endpoint evidence
    CommitReceiveExpression pending evidence ->
      evalCommitReceive environment state locatedExpression pending evidence
    BorrowExpression owner view body -> evalBorrow environment state locatedExpression owner view body
    DecideExpression scrutinee arms -> evalDecide environment state locatedExpression scrutinee arms
    OfferExpression endpoint arms -> evalOffer environment state locatedExpression endpoint arms
    FailExpression target resource -> evalFail environment state locatedExpression target resource
    CloseExpression target -> evalClose environment state locatedExpression target
    ReleaseExpression owner -> evalRelease state locatedExpression owner
    AcceptExpression value targetTy -> evalAccept environment state locatedExpression value targetTy
    ProveExpression proposition -> evalProve environment state locatedExpression proposition
    FallbackExpression base fallback -> evalFallback environment state locatedExpression base fallback
    BinaryExpression {} -> do
      scalar <- inferReadOnlyScalar environment state locatedExpression
      pure [valuePath state (RuntimeScalar scalar)]

valuePath :: SurfaceState -> RuntimeValue -> SurfacePath
valuePath state value = SurfacePath PathContinue state (Just value)

moveVariable
  :: Located a
  -> Text
  -> SurfaceState
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
moveVariable located name state = do
  meta <- lookupBindingMeta located name state
  let coreName = Name name
  (mode, ty, nextContext) <- mapCore located StructuralUse $
    useBinding coreName (resourceContext (stateCore state))
  let nextCore = (stateCore state) { resourceContext = nextContext }
      nextBindings
        | mode == Unrestricted = stateBindings state
        | otherwise = Map.delete name (stateBindings state)
      nextActive
        | mode /= Unrestricted && stateActiveEndpoint state == Just name = Nothing
        | otherwise = stateActiveEndpoint state
  pure
    ( ScalarValue mode ty (bindingShape meta)
    , state
        { stateCore = nextCore
        , stateBindings = nextBindings
        , stateActiveEndpoint = nextActive
        }
    )

lookupBindingMeta :: Located a -> Text -> SurfaceState -> Either SurfaceCheckError BindingMeta
lookupBindingMeta located name state =
  case Map.lookup name (stateBindings state) of
    Just meta -> Right meta
    Nothing -> throw located StructuralUse ("unknown or already-consumed binding: " <> name)

bindPattern :: Located Pattern -> RuntimeValue -> SurfaceState -> Either SurfaceCheckError SurfaceState
bindPattern pattern' value state =
  case (locatedValue pattern', value) of
    (BindPattern name, RuntimeScalar scalar) ->
      insertNamedBinding (locatedSpan pattern') name
        (BindingMeta (scalarMode scalar) (scalarType scalar) (scalarShape scalar)) state
    (BindPattern name, RuntimeUnit) ->
      insertNamedBinding (locatedSpan pattern') name
        (BindingMeta Unrestricted TyUnit PlainShape) state
    (TuplePattern patterns, RuntimeTuple values)
      | length patterns == length values -> foldM bindOne state (zip patterns values)
      | otherwise -> throw pattern' TypeMismatch "tuple pattern arity does not match expression result"
    _ -> throw pattern' TypeMismatch "binding pattern does not match expression result shape"
  where
    bindOne current (subPattern, subValue) = bindPattern subPattern subValue current

insertNamedBinding
  :: SourceSpan
  -> Text
  -> BindingMeta
  -> SurfaceState
  -> Either SurfaceCheckError SurfaceState
insertNamedBinding span' name meta state = do
  context <- mapCoreSpan span' StructuralUse $
    insertBinding (bindingMode meta) (Name name) (bindingType meta) (resourceContext (stateCore state))
  let active =
        case bindingType meta of
          TyEndpoint _ -> Just name
          _ -> stateActiveEndpoint state
  pure state
    { stateCore = (stateCore state) { resourceContext = context }
    , stateBindings = Map.insert name meta (stateBindings state)
    , stateActiveEndpoint = active
    }

readField
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Text
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
readField environment state whole base field = do
  baseScalar <- inferReadOnlyScalar environment state base
  case scalarShape baseScalar of
    RecordShape _ fields ->
      case Map.lookup field fields of
        Just info -> pure (ScalarValue Unrestricted (fieldType info) PlainShape, state)
        Nothing -> throw whole IllegalProjection ("field is not declared on this value: " <> field)
    ParsedShape parsed grammar
      | field == "value" ->
          pure
            ( ScalarValue Unrestricted (TyFrame (GrammarId grammar)) (recordShapeForGrammar grammar Nothing)
            , state
            )
      | otherwise -> throw whole IllegalProjection "Parsed evidence exposes its semantic value through .value only"
    ExternalParsedShape grammar _
      | field == "value" ->
          pure
            ( ScalarValue Unrestricted (TyFrame (GrammarId grammar)) (recordShapeForGrammar grammar Nothing)
            , state
            )
      | otherwise ->
          -- Older negative witnesses use the parsed semantic value directly.
          readSemanticGrammarField whole grammar (baseVariableName base) field state
    OwnedBytesShape index -> readOwnedBytesField whole (baseVariableName base) index field state
    FixtureRawShape _ -> throw whole IllegalProjection "raw bytes have no structured semantic fields"
    LegacyRawShape {} -> throw whole IllegalProjection "raw bytes have no structured semantic fields"
    PendingRawShape {} -> throw whole IllegalProjection "raw bytes have no structured semantic fields"
    BorrowedViewShape {} -> throw whole IllegalProjection "borrowed byte views have no structured semantic fields"
    _ ->
      case semanticGrammarName (scalarType baseScalar) of
        Just grammar -> readSemanticGrammarField whole grammar (baseVariableName base) field state
        Nothing -> throw whole IllegalProjection "value has no declared structured fields"
  where
    _ = parsed

readSemanticGrammarField
  :: Located a
  -> Text
  -> Maybe Text
  -> Text
  -> SurfaceState
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
readSemanticGrammarField whole grammar baseName field state =
  case recordShapeForGrammar grammar baseName of
    RecordShape _ fields ->
      case Map.lookup field fields of
        Just info -> pure (ScalarValue Unrestricted (fieldType info) PlainShape, state)
        Nothing -> throw whole IllegalProjection ("unknown semantic field " <> field <> " on " <> grammar)
    _ -> throw whole IllegalProjection "internal record-shape error"

readOwnedBytesField
  :: Located a
  -> Maybe Text
  -> RefTerm
  -> Text
  -> SurfaceState
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
readOwnedBytesField whole baseName index field state =
  case field of
    "length" ->
      pure (ScalarValue Unrestricted (TyUInt 64) PlainShape, state)
    "kind" ->
      pure (ScalarValue Unrestricted (TyOpaqueSorted "PayloadKind" (SortEnum "PayloadKind")) PlainShape, state)
    "id" ->
      pure (ScalarValue Unrestricted (TyOpaqueSorted "PayloadId" (SortStableId "OwnedBytes")) PlainShape, state)
    _ -> throw whole IllegalProjection "owned byte values do not have that field"
  where
    _ = (baseName, index)

inferReadOnlyScalar
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError ScalarValue
inferReadOnlyScalar environment state located =
  case locatedValue located of
    VariableExpression name -> do
      meta <- lookupBindingMeta located name state
      pure (ScalarValue (bindingMode meta) (bindingType meta) (bindingShape meta))
    IntegerExpression literal ->
      pure (ScalarValue Unrestricted (TyOpaque ("Integer[" <> Text.pack (show literal) <> "]")) PlainShape)
    BooleanExpression _ -> pure (ScalarValue Unrestricted TyBool (DecisionShape BooleanDecision))
    UnitExpression -> pure (ScalarValue Unrestricted TyUnit PlainShape)
    FieldExpression base field -> fst <$> readField environment state located base field
    BinaryExpression _ _ _ ->
      pure (ScalarValue Unrestricted (TyOpaqueSorted "NatExpr" SortNat) PlainShape)
    _ -> throw located TypeMismatch "expression is not a read-only value in this context"

constructValue
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Text
  -> [(Text, Located SurfaceExpression)]
  -> Either SurfaceCheckError ScalarValue
constructValue environment state located constructor assignments =
  case constructor of
    "Hello" -> do
      fields <- constructFields ["versions"]
      pure (ScalarValue Unrestricted (TyFrame (GrammarId "Hello")) (RecordShape "Hello" fields))
    "Begin" -> do
      fields <- constructFields ["length", "kind", "digestAlg", "digest"]
      pure (ScalarValue Unrestricted (TyFrame (GrammarId "Begin")) (RecordShape "Begin" fields))
    _ -> throw located TypeMismatch ("unknown constructed semantic value: " <> constructor)
  where
    table = Map.fromList assignments
    constructFields required = do
      mapM_ requireField required
      Map.fromList <$> mapM fieldEntry required
    requireField name =
      unless (Map.member name table) $
        throw located TypeMismatch ("missing constructor field: " <> name)
    fieldEntry name = do
      expression <- maybe (throw located TypeMismatch "missing constructor field") Right (Map.lookup name table)
      scalar <- inferReadOnlyScalar environment state expression
      alias <- optionalRefTerm environment state expression
      sort <- maybe (throw expression TypeMismatch "constructor field is not refinement-visible") Right (refSortOfTy (scalarType scalar))
      pure (name, FieldInfo (scalarType scalar) sort alias)

optionalRefTerm
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (Maybe RefTerm)
optionalRefTerm environment state expression =
  case elaborateRefTerm (elaborationEnv environment state) expression of
    Right term -> Right (Just (rewriteRefTerm state term))
    Left _ -> Right Nothing

evalPrimitive
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Text
  -> [Located SurfaceExpression]
  -> Either SurfaceCheckError [SurfacePath]
evalPrimitive environment state located name arguments =
  case Map.lookup name (surfacePrimitives environment) of
    Nothing -> throw located UnknownPrimitive ("primitive is not declared in Sigma: " <> name)
    Just semantics -> evalPrimitiveSemantics environment state located semantics arguments

evalPrimitiveSemantics
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> PrimitiveSemantics
  -> [Located SurfaceExpression]
  -> Either SurfaceCheckError [SurfacePath]
evalPrimitiveSemantics environment state located semantics arguments =
  case semantics of
    PrimitiveSupportedVersions -> do
      expectArity 0
      let binder = Name "$versions"
          base = TyOpaqueSorted "SupportedVersions" (SortFiniteSet (SortUInt 16))
          refinement = LessThan (RefNat 0) (RefLen (RefVar binder))
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted (TyRefined binder base refinement) PlainShape))]
    PrimitiveSha256 -> do
      expectArity 1
      _ <- inferReadOnlyScalar environment state (head arguments)
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted (TyOpaque "Digest") PlainShape))]
    PrimitiveShouldCancel -> do
      expectArity 0
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted TyBool (DecisionShape BooleanDecision)))]
    PrimitiveChooseSupported -> do
      expectArity 2
      mapM_ (inferReadOnlyScalar environment state) arguments
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted (TyOpaque "SupportedDecision") (DecisionShape ChooseSupportedDecision)))]
    PrimitiveStore -> do
      expectArity 1
      (payload, next) <- moveRequiredLinear environment state (head arguments)
      unless (isOwnedBytes payload) $
        throw (head arguments) TypeMismatch "store requires an owned byte value"
      pure [valuePath next (RuntimeScalar (ScalarValue Unrestricted (TyOpaque "StoreResult") (DecisionShape StoreDecision)))]
    PrimitiveFixtureBytes -> do
      expectArity 0
      let (frameId, next) = freshFrame state
      pure [valuePath next (RuntimeScalar (ScalarValue Unrestricted (TyOpaqueSorted "RawBytes" (SortFiniteSeq (SortUInt 8))) (FixtureRawShape frameId)))]
    PrimitiveUncheckedU32Add -> do
      expectArity 2
      mapM_ (requireUIntRead 32) arguments
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted (TyUInt 32) UncheckedArithmeticShape))]
    PrimitiveNewCancellationScope -> do
      expectArity 0
      pure [valuePath state (RuntimeTuple
        [ RuntimeScalar (ScalarValue Linear (TyOpaque "CancelScope") PlainShape)
        , RuntimeScalar (ScalarValue Affine (TyOpaque "CancelCap") PlainShape)
        ])]
    PrimitiveAllocateLinearBuffer -> do
      expectArity 1
      pure [valuePath state (RuntimeScalar (ScalarValue Linear (TyOpaque "LinearBuffer") PlainShape))]
    PrimitiveRecordUploadId -> pureUnitAfterReads
    PrimitiveConsumeBeginPolicyEvidence -> do
      expectArity 1
      case locatedValue (head arguments) of
        VariableExpression evidenceName -> do
          meta <- lookupBindingMeta (head arguments) evidenceName state
          case bindingType meta of
            TyValidated "BeginPolicy" _ _ -> pure [valuePath state RuntimeUnit]
            TyProof (Atom "BeginPolicy" _) -> pure [valuePath state RuntimeUnit]
            _ -> throw (head arguments) MissingEvidence "binding is not BeginPolicy evidence"
        _ -> throw (head arguments) MissingEvidence "BeginPolicy evidence must be a named reusable binding"
    PrimitiveUse -> pureUnitAfterReads
    PrimitiveInspect -> pureUnitAfterReads
    PrimitiveAuthorizeStore -> consumeFirstRestricted
    PrimitiveDelegate -> consumeFirstRestricted
    PrimitiveContinueCommonState -> pureUnitAfterReads
    PrimitiveHandlePayload -> pureUnitAfterReads
  where
    expectArity n = unless (length arguments == n) $
      throw located TypeMismatch ("primitive arity mismatch: expected " <> Text.pack (show n))

    requireUIntRead width expression = do
      scalar <- inferReadOnlyScalar environment state expression
      unless (scalarType scalar == TyUInt width) $
        throw expression TypeMismatch ("primitive requires U" <> Text.pack (show width))

    pureUnitAfterReads = do
      mapM_ (inferReadOnlyScalar environment state) arguments
      pure [valuePath state RuntimeUnit]

    consumeFirstRestricted = do
      expectArity 1
      case locatedValue (head arguments) of
        VariableExpression name -> do
          (_, next) <- moveVariable (head arguments) name state
          pure [valuePath next RuntimeUnit]
        _ -> throw (head arguments) TypeMismatch "authority-consuming primitive requires a named capability"

evalSequentialValues
  :: SurfaceEnvironment
  -> SurfaceState
  -> [Located SurfaceExpression]
  -> Either SurfaceCheckError ([RuntimeValue], SurfaceState)
evalSequentialValues environment = go []
  where
    go accumulated state [] = Right (reverse accumulated, state)
    go accumulated state (expression : rest) = do
      paths <- evalExpression environment state expression
      case paths of
        [SurfacePath PathContinue next (Just value)] -> go (value : accumulated) next rest
        _ -> throw expression TypeMismatch "tuple element may not branch or terminate"

evalReceive
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceType
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalReceive environment state located messageTy endpointExpression = do
  endpoint <- endpointName endpointExpression
  (temp, state1) <- freshName "$recv" state
  step <- mapSession located $ receiveEndpoint (Name endpoint) temp (resourceContext (stateCore state1))
  expected <- resolveMessageType environment state1 messageTy
  message <- maybe (throw located TypeMismatch "receive did not expose a message") Right (stepMessage step)
  unless (sameTy state1 expected (messageType message)) $
    throw messageTy TypeMismatch "surface receive type does not match the session message type"
  let state2 = consumeSurfaceName endpoint state1
      withStep = state2 { stateCore = (stateCore state2) { resourceContext = stepContext step } }
  (successor, state3) <- extractLinearTemp temp withStep
  let messageScalar = ScalarValue (messageMode (messageType message)) (messageType message) (shapeForType (messageType message))
  pure [valuePath state3 (RuntimeTuple [RuntimeScalar successor, RuntimeScalar messageScalar])]

resolveMessageType
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceType
  -> Either SurfaceCheckError Ty
resolveMessageType environment state surfaceTy = do
  (_, ty, _) <- resolveSurfaceType environment state surfaceTy
  pure ty

evalReceiveFrame
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalReceiveFrame environment state located endpointExpression = do
  endpoint <- endpointName endpointExpression
  (pendingTemp, state1) <- freshName "$pending" state
  let (frameId, state2) = freshFrame state1
  step <- mapRecognition located $
    receiveFrame (Name endpoint) pendingTemp frameId (resourceContext (stateCore state2))
  let state3 = consumeSurfaceName endpoint state2
      withStep = state3 { stateCore = (stateCore state3) { resourceContext = receiveFrameContext step } }
  (pendingScalar, state4) <- extractLinearTemp pendingTemp withStep
  if surfaceLegacyReceiveFrameRaw environment
    then do
      let pending = receivePendingSpec step
          raw = ScalarValue Unrestricted
            (TyOpaqueSorted "RawBytes" (SortFiniteSeq (SortUInt 8)))
            (LegacyRawShape pendingTemp (pendingGrammar pending) frameId)
      pure [valuePath state4 (RuntimeTuple [RuntimeScalar pendingScalar, RuntimeScalar raw])]
    else pure [valuePath state4 (RuntimeScalar pendingScalar)]

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
      let valueName = Name ("$parsed-value-" <> grammar)
      parsed <- mapRecognition located $
        trustedRecognitionSuccess rawView valueName (resourceContext (stateCore state))
      failure <- mapRecognition located $
        trustedRecognitionFailure rawView "recognition-failure" (resourceContext (stateCore state))
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted (TyOpaque "RecognitionResult")
        (DecisionShape (RecognitionDecision parsed failure grammar))))]
    LegacyRawShape pending grammarId frameId ->
      if grammarId == GrammarId grammar
        then pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted (TyOpaque "RecognitionResult")
          (DecisionShape (LegacyRecognitionDecision pending grammarId frameId grammar))))]
        else throw located RecognitionProvenance "recognizer grammar does not match the pending frame"
    FixtureRawShape frameId ->
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted (TyFrame (GrammarId grammar))
        (ExternalParsedShape grammar frameId)))]
    _ -> throw rawExpression TypeMismatch "recognize requires a raw byte view"

evalValidate
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Text
  -> Maybe (Located SurfaceExpression)
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalValidate environment state located claim context subject =
  case claim of
    "DigestMatches" -> do
      _ <- inferReadOnlyScalar environment state subject
      let proposition = digestMatchesProposition
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted (TyOpaque "DigestValidation")
        (DecisionShape (DigestDecision proposition))))]
    _ -> do
      contextName <- case context of
        Just expression -> namedExpression MissingEvidence expression
        Nothing -> pure (Name "$implicit-context")
      subjectName <- namedSubject subject
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted (TyOpaque "ValidationResult")
        (DecisionShape (ValidationDecision claim contextName subjectName))))]
  where
    _ = located
    namedSubject expression =
      case locatedValue expression of
        VariableExpression name -> Right (Name name)
        _ -> throw expression TypeMismatch "validation subject must be a named semantic value in Phase 0"

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
  (temp, state1) <- freshName "$send" state
  step <- mapSession located $ sendEndpoint (Name endpoint) temp (resourceContext (stateCore state1))
  message <- maybe (throw located TypeMismatch "send did not expose a message") Right (stepMessage step)
  let actionState0 = consumeSurfaceName endpoint state1
      actionState = actionState0 { stateCore = (stateCore actionState0) { resourceContext = stepContext step } }
  (valueScalar, valueState) <- moveExpressionAsValue environment actionState valueExpression
  checkScalarCompatibility environment valueState valueExpression valueScalar (messageType message)
  when (exact && not (isBytesType (messageType message))) $
    throw located TypeMismatch "send_exact is only valid for byte payload messages"
  (successor, nextState) <- extractLinearTemp temp valueState
  pure [valuePath nextState (RuntimeScalar successor)]

evalReceiveExact
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError [SurfacePath]
evalReceiveExact environment state located countExpression endpointExpression explicitEvidence = do
  checkConfiguredRequirement environment state countExpression (surfaceReceiveExactRequirement environment) explicitEvidence
  endpoint <- endpointName endpointExpression
  countTerm <- mapElaboration countExpression $
    elaborateRefTerm (elaborationEnv environment state) countExpression
  (natCount, _) <- mapFocusing countExpression $
    elaborateRefTermAs (surfaceStaticContext environment) (stateCore state) SortNat (rewriteRefTerm state countTerm)
  (temp, state1) <- freshName "$recv-exact" state
  step <- mapSession located $ receiveEndpoint (Name endpoint) temp (resourceContext (stateCore state1))
  message <- maybe (throw located TypeMismatch "receive_exact did not expose a message") Right (stepMessage step)
  expectedIndex <- case rewriteTy state1 (messageType message) of
    TyBytes index -> Right index
    other -> throw located TypeMismatch ("receive_exact requires a byte message, found " <> Text.pack (show other))
  unless (normalizeRefTerm natCount == normalizeRefTerm expectedIndex) $
    throw countExpression TypeMismatch "receive_exact count does not match the session's dependent byte length"
  let state2 = consumeSurfaceName endpoint state1
      withStep = state2 { stateCore = (stateCore state2) { resourceContext = stepContext step } }
  (successor, state3) <- extractLinearTemp temp withStep
  let payload = ScalarValue Linear (TyBytes expectedIndex) (OwnedBytesShape expectedIndex)
  pure [valuePath state3 (RuntimeTuple [RuntimeScalar successor, RuntimeScalar payload])]

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
  mapM_ (\requirement -> checkRequirement environment state located requirement explicitEvidence)
    (Map.findWithDefault [] (branchValueLabel branch) (surfaceSelectRequirements environment))
  (temp, state1) <- freshName "$select" state
  step <- mapSession located $
    selectEndpoint (Name endpoint) temp (branchValueLabel branch) (resourceContext (stateCore state1))
  payloadState <- checkBranchPayload environment state1 located (stepMessage step) (branchValueArguments branch) explicitEvidence
  let state2 = consumeSurfaceName endpoint payloadState
      withStep = state2 { stateCore = (stateCore state2) { resourceContext = stepContext step } }
  -- payload checking was performed against state1. Reapply any value consumption
  -- to the step context by removing consumed source bindings from the step context.
  reconciled <- reconcileConsumedBindings payloadState withStep
  (successor, next) <- extractLinearTemp temp reconciled
  pure [valuePath next (RuntimeScalar successor)]

evalCommitReceive
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalCommitReceive _environment state located pendingExpression evidenceExpression = do
  pending <- namedExpression RecognitionProvenance pendingExpression
  evidenceName <- namedExpression RecognitionProvenance evidenceExpression
  evidenceMeta <- lookupBindingMeta evidenceExpression (unName evidenceName) state
  parsed <- case bindingShape evidenceMeta of
    ParsedShape witness _ -> Right witness
    ExternalParsedShape _ _ -> throw evidenceExpression RecognitionProvenance "parsed evidence belongs to unrelated fixture bytes"
    ForgedParsedShape -> throw evidenceExpression RecognitionProvenance "forged parsed evidence has no matching ingress provenance"
    _ -> throw evidenceExpression RecognitionProvenance "commit_receive requires Parsed evidence"
  (temp, state1) <- freshName "$commit" state
  step <- mapRecognition located $
    commitReceive pending temp parsed (resourceContext (stateCore state1))
  let pendingText = unName pending
      state2 = consumeSurfaceName pendingText state1
      withStep = state2 { stateCore = (stateCore state2) { resourceContext = commitContext step } }
  (successor, next) <- extractLinearTemp temp withStep
  pure [valuePath next (RuntimeScalar successor)]

evalBorrow
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Text
  -> Located Block
  -> Either SurfaceCheckError [SurfacePath]
evalBorrow environment state located ownerExpression viewName body = do
  owner <- namedExpression BorrowEscape ownerExpression
  ownerMeta <- lookupBindingMeta ownerExpression (unName owner) state
  (viewScalar, loanedState) <- case bindingType ownerMeta of
    TyPendingRecv _ -> do
      (raw, context) <- mapRecognition located $ beginRawLoan owner (resourceContext (stateCore state))
      pure
        ( ScalarValue Unrestricted (TyOpaqueSorted "RawBytes" (SortFiniteSeq (SortUInt 8))) (PendingRawShape raw)
        , state { stateCore = (stateCore state) { resourceContext = context } }
        )
    _ | bindingMode ownerMeta == Linear || bindingMode ownerMeta == Affine -> do
          context <- mapCore located BorrowEscape $ startSharedLoan owner (resourceContext (stateCore state))
          pure
            ( ScalarValue Unrestricted (TyOpaqueSorted "SharedBytes" (SortFiniteSeq (SortUInt 8))) (BorrowedViewShape owner)
            , state { stateCore = (stateCore state) { resourceContext = context } }
            )
      | otherwise -> throw ownerExpression BorrowEscape "borrow requires an affine or linear owner"
  withView <- insertNamedBinding (locatedSpan located) viewName
    (BindingMeta Unrestricted (scalarType viewScalar) (scalarShape viewScalar)) loanedState
  bodyPaths <- checkBlockValue environment withView body
  mapM (finishBorrow owner viewName) bodyPaths
  where
    finishBorrow owner viewName path
      | surfacePathControl path /= PathContinue =
          throw located BorrowEscape "borrow scope terminated before releasing its loan"
      | otherwise = do
          case surfacePathValue path of
            Just value | valueContainsBorrowedView owner value ->
              throw located BorrowEscape "shared view escapes its lexical borrow scope"
            _ -> pure ()
          stripped <- removeUnrestrictedBinding viewName (surfacePathState path)
          context <- mapCore located BorrowEscape $
            endSharedLoan owner (resourceContext (stateCore stripped))
          pure path
            { surfacePathState = stripped { stateCore = (stateCore stripped) { resourceContext = context } }
            }

checkBlockValue
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located Block
  -> Either SurfaceCheckError [SurfacePath]
checkBlockValue environment initial locatedBlock =
  case blockStatements (locatedValue locatedBlock) of
    [] -> Right [valuePath initial RuntimeUnit]
    statements -> do
      let prefix = init statements
          lastStatement = last statements
      prefixPaths <- checkStatements environment [continuePath initial] prefix
      concat <$> mapM (finishLast lastStatement) prefixPaths
  where
    finishLast statement path
      | surfacePathControl path /= PathContinue = Right [path]
      | otherwise =
          case locatedValue statement of
            ExpressionStatement expression -> evalExpression environment (surfacePathState path) expression
            _ -> checkStatement environment statement path

valueContainsBorrowedView :: Name -> RuntimeValue -> Bool
valueContainsBorrowedView owner value =
  case value of
    RuntimeUnit -> False
    RuntimeTuple values -> any (valueContainsBorrowedView owner) values
    RuntimeScalar scalar ->
      case scalarShape scalar of
        BorrowedViewShape borrowedOwner -> borrowedOwner == owner
        PendingRawShape _ -> True
        LegacyRawShape {} -> True
        _ -> False

evalDecide
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> [Located CaseArm]
  -> Either SurfaceCheckError [SurfacePath]
evalDecide environment state located scrutinee arms = do
  scrutineeScalar <- inferReadOnlyScalar environment state scrutinee
  decision <- case scalarShape scrutineeScalar of
    DecisionShape kind -> Right kind
    _ | scalarType scrutineeScalar == TyBool -> Right BooleanDecision
      | otherwise -> throw scrutinee TypeMismatch "decide requires a declared decision result"
  let expectedLabels = decisionLabels decision
      handledLabels = map (casePatternLabel . caseArmPattern . locatedValue) arms
  unless (Set.fromList expectedLabels == Set.fromList handledLabels && length expectedLabels == length handledLabels) $
    throw located BranchExhaustiveness "decision handlers do not exactly cover the declared result alternatives"
  concat <$> mapM (checkDecisionArm environment state decision) arms

decisionLabels :: DecisionKind -> [Text]
decisionLabels decision =
  case decision of
    BooleanDecision -> ["true", "false"]
    ChooseSupportedDecision -> ["none", "some"]
    RecognitionDecision {} -> ["rejected", "accepted"]
    LegacyRecognitionDecision {} -> ["failure", "success"]
    ValidationDecision {} -> ["rejected", "accepted"]
    DigestDecision {} -> ["rejected", "accepted"]
    StoreDecision -> ["failure", "success"]

checkDecisionArm
  :: SurfaceEnvironment
  -> SurfaceState
  -> DecisionKind
  -> Located CaseArm
  -> Either SurfaceCheckError [SurfacePath]
checkDecisionArm environment state decision locatedArm = do
  let pattern' = caseArmPattern (locatedValue locatedArm)
      binders = casePatternBinders pattern'
  bound <- bindDecisionPattern environment state decision (casePatternLabel pattern') binders locatedArm
  checkScopedBlock environment bound (caseArmBody (locatedValue locatedArm))

bindDecisionPattern
  :: SurfaceEnvironment
  -> SurfaceState
  -> DecisionKind
  -> Text
  -> [Text]
  -> Located a
  -> Either SurfaceCheckError SurfaceState
bindDecisionPattern _environment state decision label binders located =
  case (decision, label, binders) of
    (BooleanDecision, "true", []) -> Right state
    (BooleanDecision, "false", []) -> Right state
    (ChooseSupportedDecision, "none", [noCommon]) -> do
      let proposition = Disjoint
            (RefVar (Name "serverSupported"))
            (RefField (RefVar (Name "hello")) "versions" (SortFiniteSet (SortUInt 16)))
      insertProof noCommon proposition state
    (ChooseSupportedDecision, "some", [version, offered, supported]) -> do
      withVersion <- insertNamedBinding (locatedSpan located) version
        (BindingMeta Unrestricted (TyUInt 16) PlainShape) state
      let offeredProp = Member
            (RefVar (Name version))
            (RefField (RefVar (Name "hello")) "versions" (SortFiniteSet (SortUInt 16)))
          supportedProp = Member
            (RefVar (Name version))
            (RefVar (Name "serverSupported"))
      withOffered <- insertProof offered offeredProp withVersion
      insertProof supported supportedProp withOffered
    (RecognitionDecision parsed _ grammar, "accepted", [parsedName]) ->
      insertNamedBinding (locatedSpan located) parsedName
        (BindingMeta Unrestricted (TyOpaque ("Parsed[" <> grammar <> "]")) (ParsedShape parsed grammar)) state
    (RecognitionDecision _ failure _, "rejected", [reason]) ->
      insertNamedBinding (locatedSpan located) reason
        (BindingMeta Unrestricted (TyOpaque "RecognitionFailure") (FailureShape failure)) state
    (LegacyRecognitionDecision pending grammar frame grammarText, "success", [parsedName]) ->
      insertNamedBinding (locatedSpan located) parsedName
        (BindingMeta Unrestricted (TyOpaque ("Parsed[" <> grammarText <> "]"))
          (LegacyParsedShape pending grammar frame grammarText)) state
    (LegacyRecognitionDecision pending grammar frame _, "failure", [reason]) ->
      insertNamedBinding (locatedSpan located) reason
        (BindingMeta Unrestricted (TyOpaque "RecognitionFailure")
          (LegacyFailureShape pending grammar frame)) state
    (ValidationDecision claim context subject, "accepted", [evidenceName]) ->
      insertNamedBinding (locatedSpan located) evidenceName
        (BindingMeta Unrestricted (TyValidated claim context subject) PlainShape) state
    (ValidationDecision claim _ _, "rejected", [reason]) ->
      insertNamedBinding (locatedSpan located) reason
        (BindingMeta Unrestricted (TyOpaque ("ValidationFailure[" <> claim <> "]")) PlainShape) state
    (DigestDecision proposition, "accepted", [evidenceName]) -> insertProof evidenceName proposition state
    (DigestDecision _, "rejected", [reason]) ->
      insertNamedBinding (locatedSpan located) reason
        (BindingMeta Unrestricted (TyOpaque "DigestFailure") PlainShape) state
    (StoreDecision, "success", [identifier]) ->
      insertNamedBinding (locatedSpan located) identifier
        (BindingMeta Unrestricted (TyOpaque "UploadId") PlainShape) state
    (StoreDecision, "failure", [err]) ->
      insertNamedBinding (locatedSpan located) err
        (BindingMeta Unrestricted (TyOpaque "StorageFailure") PlainShape) state
    _ -> throw located TypeMismatch "decision arm binder shape does not match the declared result"

-- Additional private shapes used only after decision refinement.
pattern FailureShape :: RecognitionFailure -> SurfaceShape
pattern FailureShape failure <- FailureCarrierShape failure where
  FailureShape failure = FailureCarrierShape failure

pattern LegacyParsedShape :: Name -> GrammarId -> FrameId -> Text -> SurfaceShape
pattern LegacyParsedShape pending grammar frame text <- LegacyParsedCarrier pending grammar frame text where
  LegacyParsedShape pending grammar frame text = LegacyParsedCarrier pending grammar frame text

pattern LegacyFailureShape :: Name -> GrammarId -> FrameId -> SurfaceShape
pattern LegacyFailureShape pending grammar frame <- LegacyFailureCarrier pending grammar frame where
  LegacyFailureShape pending grammar frame = LegacyFailureCarrier pending grammar frame

insertProof :: Text -> Proposition -> SurfaceState -> Either SurfaceCheckError SurfaceState
insertProof name proposition =
  insertNamedBinding noSpan name (BindingMeta Unrestricted (TyProof proposition) PlainShape)

evalOffer
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> [Located CaseArm]
  -> Either SurfaceCheckError [SurfacePath]
evalOffer environment state located endpointExpression arms = do
  endpoint <- endpointName endpointExpression
  meta <- lookupBindingMeta endpointExpression endpoint state
  session <- case bindingType meta of
    TyEndpoint sessionTy -> mapSession located (exposeSessionHead sessionTy)
    other -> throw endpointExpression SessionAction ("offer requires an endpoint, found " <> Text.pack (show other))
  branches <- case session of
    Offer declared -> Right declared
    other -> throw located SessionAction ("offer used at non-offer session head: " <> Text.pack (show other))
  mapFocusing located $ checkBranchExhaustiveness branches (map (casePatternLabel . caseArmPattern . locatedValue) arms)
  concat <$> mapM (checkOfferArm environment state endpoint) arms

checkOfferArm
  :: SurfaceEnvironment
  -> SurfaceState
  -> Text
  -> Located CaseArm
  -> Either SurfaceCheckError [SurfacePath]
checkOfferArm environment state endpoint locatedArm = do
  let pattern' = caseArmPattern (locatedValue locatedArm)
      label = casePatternLabel pattern'
  (temp, state1) <- freshName "$offer" state
  step <- mapSession locatedArm $
    offerEndpoint (Name endpoint) temp label (resourceContext (stateCore state1))
  let state2 = consumeSurfaceName endpoint state1
      withStep = state2 { stateCore = (stateCore state2) { resourceContext = stepContext step } }
  (successor, extracted) <- extractLinearTemp temp withStep
  rebound <- insertNamedBinding (locatedSpan locatedArm) endpoint
    (BindingMeta Linear (scalarType successor) PlainShape) extracted
  withPayload <- bindOfferPayload (locatedSpan locatedArm) (stepMessage step) (casePatternBinders pattern') rebound
  checkScopedBlock environment withPayload (caseArmBody (locatedValue locatedArm))

bindOfferPayload
  :: SourceSpan
  -> Maybe MessageSpec
  -> [Text]
  -> SurfaceState
  -> Either SurfaceCheckError SurfaceState
bindOfferPayload _ Nothing [] state = Right state
bindOfferPayload span' (Just message) [name] state =
  insertNamedBinding span' name
    (BindingMeta (messageMode (messageType message)) (messageType message) (shapeForType (messageType message))) state
bindOfferPayload span' Nothing (_ : _) _ = Left SurfaceCheckError
  { surfaceErrorSpan = span'
  , surfaceErrorClass = TypeMismatch
  , surfaceErrorDetail = "branch does not carry a payload"
  }
bindOfferPayload span' (Just _) _ _ = Left SurfaceCheckError
  { surfaceErrorSpan = span'
  , surfaceErrorClass = TypeMismatch
  , surfaceErrorDetail = "branch payload binder arity mismatch"
  }

checkScopedBlock
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located Block
  -> Either SurfaceCheckError [SurfacePath]
checkScopedBlock environment state body = do
  let incomingNames = Map.keysSet (stateBindings state)
  paths <- checkBlock environment state body
  mapM (pruneScope (locatedSpan body) incomingNames) paths

pruneScope :: SourceSpan -> Set Text -> SurfacePath -> Either SurfaceCheckError SurfacePath
pruneScope span' incoming path
  | surfacePathControl path /= PathContinue = Right path
  | otherwise = do
      let state = surfacePathState path
          newNames = Map.keysSet (stateBindings state) `Set.difference` incoming
          newBindings = mapMaybe (\name -> fmap ((,) name) (Map.lookup name (stateBindings state))) (Set.toList newNames)
      mapM_ ensureDiscardable newBindings
      stripped <- foldM (flip removeScopedBinding) state (Set.toList newNames)
      Right path { surfacePathState = stripped }
  where
    ensureDiscardable (name, meta)
      | bindingMode meta == Linear = Left SurfaceCheckError
          { surfaceErrorSpan = span'
          , surfaceErrorClass = LinearCompletion
          , surfaceErrorDetail = "linear branch-local binding escapes scope: " <> name
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
  resource <- namedExpression StructuralUse resourceExpression
  next <- case failureTargetClass target of
    "recognition" -> failRecognition resource target
    _ -> consumeFatalResource resource
  ensureTerminalState environment (locatedSpan located) Nothing next
  let detail = case failureTargetArguments target of
        [] -> ""
        _ -> "explicit"
  pure [SurfacePath (PathFailed (failureTargetClass target) detail) next Nothing]
  where
    failRecognition resource failureTarget =
      case failureTargetArguments failureTarget of
        [reasonExpression] -> do
          reasonName <- namedExpression RecognitionProvenance reasonExpression
          reasonMeta <- lookupBindingMeta reasonExpression (unName reasonName) state
          case bindingShape reasonMeta of
            FailureCarrierShape failure -> do
              context <- mapRecognition located $
                failPendingRecognition resource failure (resourceContext (stateCore state))
              pure (consumeSurfaceName (unName resource) state)
                { stateCore = (stateCore state) { resourceContext = context }
                }
            LegacyFailureCarrier pending grammar frame -> do
              pendingMeta <- lookupBindingMeta resourceExpression (unName resource) state
              case bindingType pendingMeta of
                TyPendingRecv spec
                  | pending == resource
                    && grammar == pendingGrammar spec
                    && frame == pendingFrame spec -> consumeFatalResource resource
                _ -> throw located RecognitionProvenance "recognition failure does not match the pending receive"
            _ -> throw reasonExpression RecognitionProvenance "recognition failure lacks matching ingress provenance"
        _ -> throw located RecognitionProvenance "recognition failure requires one failure value"

    consumeFatalResource resource = do
      (_, context) <- mapCore located StructuralUse $
        consumeLinear resource (resourceContext (stateCore state))
      pure (consumeSurfaceName (unName resource) state)
        { stateCore = (stateCore state) { resourceContext = context }
        }

evalClose
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalClose environment state located targetExpression = do
  (endpoint, outcome) <- resolveCloseTarget state targetExpression
  step <- mapSession located $ closeEndpoint (Name endpoint) outcome (resourceContext (stateCore state))
  let consumed = consumeSurfaceName endpoint state
      next = consumed { stateCore = (stateCore consumed) { resourceContext = stepContext step } }
  ensureTerminalState environment (locatedSpan located) (Just outcome) next
  pure [SurfacePath (PathClosed outcome) next Nothing]

resolveCloseTarget :: SurfaceState -> Located SurfaceExpression -> Either SurfaceCheckError (Text, Outcome)
resolveCloseTarget state target =
  case locatedValue target of
    VariableExpression name
      | name `elem` ["success", "failure", "cancelled"] -> do
          endpoint <- currentEndpoint target state
          pure (endpoint, Outcome name)
      | otherwise -> do
          meta <- lookupBindingMeta target name state
          case bindingType meta of
            TyEndpoint session -> do
              headSession <- mapSession target (exposeSessionHead session)
              case headSession of
                End outcome -> pure (name, outcome)
                _ -> throw target SessionAction "close endpoint is not at an end state"
            _ -> throw target SessionAction "close requires an endpoint or a declared terminal outcome"
    _ -> throw target SessionAction "close target must be an endpoint name or terminal outcome"

evalRelease
  :: SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalRelease state located ownerExpression = do
  name <- namedExpression StructuralUse ownerExpression
  meta <- lookupBindingMeta ownerExpression (unName name) state
  unless (bindingMode meta == Linear) $
    throw ownerExpression StructuralUse "release requires a linear owner"
  (_, context) <- mapCore located StructuralUse $
    consumeLinear name (resourceContext (stateCore state))
  let next = (consumeSurfaceName (unName name) state)
        { stateCore = (stateCore state) { resourceContext = context }
        }
  pure [valuePath next RuntimeUnit]

evalAccept
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Located SurfaceType
  -> Either SurfaceCheckError [SurfacePath]
evalAccept environment state located valueExpression targetSurfaceTy = do
  valueName <- namedExpression TypeMismatch valueExpression
  (_, targetTy, _) <- resolveSurfaceType environment state targetSurfaceTy
  case checkValue (VVar valueName) (rewriteTy state targetTy) (stateCore state) of
    Left (ExplicitTransportRequired _ _) -> throw located ExplicitTransport "dependent type change requires explicit equality transport"
    Left err -> mapValue located err
    Right result -> do
      let next0 = state { stateCore = valueResultStateCompat result }
          next = if bindingWasConsumed valueName next0 then consumeSurfaceName (unName valueName) next0 else next0
      pure [valuePath next (RuntimeScalar (ScalarValue (bindingModeForName state (unName valueName)) targetTy PlainShape))]

evalProve
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located a
  -> Either SurfaceCheckError [SurfacePath]
evalProve environment state located propositionLocated = do
  proposition <- mapElaboration propositionLocated $
    elaborateProposition (elaborationEnv environment state) propositionLocated
  plan <- mapFocusing propositionLocated $
    focusProposition (surfaceStaticContext environment) (stateCore state) proposition
  let unresolved = filter (not . focusedIsDischarged)
        (focusPrerequisites plan ++ [focusGoal plan])
  case unresolved of
    [] -> proofSuccess proposition
    requirements -> do
      let opaque = any ((== FocusNeedsExplicitMechanism) . focusedMechanism) requirements
          hasUnchecked = propositionMentionsUnchecked state proposition
      if opaque
        then throw located OpaqueProof "opaque claim cannot be introduced by generic prove"
        else if hasUnchecked
          then throw located UncheckedArithmetic "unchecked machine arithmetic supplies no mathematical equality evidence"
          else do
            solved <- mapM (solveRequirement state) requirements
            if and solved
              then proofSuccess proposition
              else throw located MissingEvidence "transparent proposition is not established by checked evidence or a checked certificate"
  where
    proofSuccess proposition =
      pure [valuePath state (RuntimeScalar (ScalarValue Unrestricted (TyProof proposition) PlainShape))]

focusedIsDischarged :: FocusedRequirement -> Bool
focusedIsDischarged requirement =
  case focusedMechanism requirement of
    FocusByDefinition -> True
    FocusByEvidence _ -> True
    _ -> False

solveRequirement :: SurfaceState -> FocusedRequirement -> Either SurfaceCheckError Bool
solveRequirement state requirement =
  case focusedMechanism requirement of
    FocusNeedsDecisionProcedure ->
      case proposeDecisionCertificate (stateCore state) [] (focusedCanonical requirement) of
        Nothing -> Right False
        Just certificate ->
          case checkDecisionCertificate (stateCore state) [] (focusedCanonical requirement) certificate of
            Right () -> Right True
            Left _ -> Right False
    _ -> Right False

evalFallback
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Fallback
  -> Either SurfaceCheckError [SurfacePath]
evalFallback environment state located base fallback = do
  case fallback of
    FailFallback failureClass -> validateFatalFallback environment state located base failureClass
    RejectFallback _ -> Right ()
  evalExpression environment state base

validateFatalFallback
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Text
  -> Either SurfaceCheckError ()
validateFatalFallback environment state located base _failureClass = do
  fatalState <- case locatedValue base of
    ReceiveFrameExpression endpoint -> consumeEndpointForFailure endpoint
    ReceiveExactExpression _ endpoint _ -> consumeEndpointForFailure endpoint
    SendExpression _ endpoint -> consumeEndpointForFailure endpoint
    SendExactExpression _ endpoint -> consumeEndpointForFailure endpoint
    _ -> Right state
  ensureTerminalState environment (locatedSpan located) (Just (Outcome "failure")) fatalState
  where
    consumeEndpointForFailure endpointExpression = do
      endpoint <- endpointName endpointExpression
      (_, context) <- mapCore located StructuralUse $
        consumeLinear (Name endpoint) (resourceContext (stateCore state))
      let stripped = consumeSurfaceName endpoint state
      Right stripped { stateCore = (stateCore stripped) { resourceContext = context } }

checkBranchPayload
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located a
  -> Maybe MessageSpec
  -> [Located SurfaceExpression]
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError SurfaceState
checkBranchPayload _ state _ Nothing [] _ = Right state
checkBranchPayload environment state located (Just message) [argument] explicitEvidence = do
  case locatedValue argument of
    VariableExpression name -> do
      let expected = rewriteTy state (messageType message)
      result <- case explicitEvidence of
        Just evidenceExpression
          | TyRefined {} <- expected -> do
              evidenceName <- namedExpression MissingEvidence evidenceExpression
              mapValueLocated located $ checkValueUsing evidenceName (VVar (Name name)) expected (stateCore state)
        _ -> mapValueLocated located $ checkValue (VVar (Name name)) expected (stateCore state)
      pure (applyValueResult name state result)
    _ -> do
      scalar <- inferReadOnlyScalar environment state argument
      checkScalarCompatibility environment state argument scalar (messageType message)
      pure state
checkBranchPayload _ _ located Nothing (_ : _) _ = throw located TypeMismatch "branch carries no payload"
checkBranchPayload _ _ located (Just _) _ _ = throw located TypeMismatch "branch payload arity mismatch"

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
  let canonical = rewriteProposition state proposition
  plan <- mapFocusing located $
    focusProposition (surfaceStaticContext environment) (stateCore state) canonical
  if focusedIsDischarged (focusGoal plan) && all focusedIsDischarged (focusPrerequisites plan)
    then Right ()
    else case explicitEvidence of
      Nothing -> throw located MissingEvidence ("required proposition lacks matching evidence: " <> Text.pack (show canonical))
      Just evidenceExpression -> do
        evidenceName <- namedExpression MissingEvidence evidenceExpression
        meta <- lookupBindingMeta evidenceExpression (unName evidenceName) state
        case evidenceProposition (bindingType meta) of
          Just actual
            | normalizeProposition (rewriteProposition state actual) == normalizeProposition canonical -> Right ()
            | otherwise -> throw evidenceExpression MissingEvidence "explicit evidence proves a different proposition/context/subject"
          Nothing -> throw evidenceExpression MissingEvidence "explicit binding is not reusable proof/validation evidence"

checkScalarCompatibility
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located a
  -> ScalarValue
  -> Ty
  -> Either SurfaceCheckError ()
checkScalarCompatibility _environment state located scalar expected =
  case compareTypes (rewriteTy state (scalarType scalar)) (rewriteTy state expected) of
    DefinitionallyEqual -> Right ()
    RequiresPropositionalEquality -> throw located ExplicitTransport "dependent values require explicit propositional transport"
    IncompatibleTypes -> throw located TypeMismatch "value type is incompatible with the session/target type"

moveExpressionAsValue
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
moveExpressionAsValue environment state expression =
  case locatedValue expression of
    VariableExpression name -> moveVariable expression name state
    _ -> do
      scalar <- inferReadOnlyScalar environment state expression
      pure (scalar, state)

moveRequiredLinear
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
moveRequiredLinear environment state expression = do
  (scalar, next) <- moveExpressionAsValue environment state expression
  unless (scalarMode scalar == Linear) $
    throw expression StructuralUse "operation requires a linear owner"
  pure (scalar, next)

endpointName :: Located SurfaceExpression -> Either SurfaceCheckError Text
endpointName = fmap unName . namedExpression SessionAction

namedExpression :: RejectionClass -> Located SurfaceExpression -> Either SurfaceCheckError Name
namedExpression rejection located =
  case locatedValue located of
    VariableExpression name -> Right (Name name)
    _ -> throw located rejection "operation requires a named binding"

currentEndpoint :: Located a -> SurfaceState -> Either SurfaceCheckError Text
currentEndpoint located state =
  case stateActiveEndpoint state of
    Just name -> Right name
    Nothing ->
      case [name | (name, meta) <- Map.toAscList (stateBindings state), isEndpointTy (bindingType meta)] of
        [name] -> Right name
        [] -> throw located SessionAction "no live endpoint is available for implicit close"
        _ -> throw located SessionAction "implicit close is ambiguous because multiple endpoints are live"

extractLinearTemp
  :: Name
  -> SurfaceState
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
extractLinearTemp temp state = do
  (ty, context) <- mapCoreSpan noSpan StructuralUse $
    consumeLinear temp (resourceContext (stateCore state))
  let scalar = ScalarValue Linear ty (shapeForType ty)
  pure (scalar, state { stateCore = (stateCore state) { resourceContext = context } })

freshName :: Text -> SurfaceState -> Either SurfaceCheckError (Name, SurfaceState)
freshName prefix state =
  let n = stateFresh state + 1
  in Right (Name (prefix <> "." <> Text.pack (show n)), state { stateFresh = n })

freshFrame :: SurfaceState -> (FrameId, SurfaceState)
freshFrame state =
  let n = stateFrame state + 1
  in (FrameId ("frame-" <> Text.pack (show n)), state { stateFrame = n })

consumeSurfaceName :: Text -> SurfaceState -> SurfaceState
consumeSurfaceName name state = state
  { stateBindings = Map.delete name (stateBindings state)
  , stateActiveEndpoint = if stateActiveEndpoint state == Just name then Nothing else stateActiveEndpoint state
  }

removeUnrestrictedBinding :: Text -> SurfaceState -> Either SurfaceCheckError SurfaceState
removeUnrestrictedBinding name state =
  case Map.lookup name (unrestrictedBindings context) of
    Nothing -> Right (consumeSurfaceName name state)
    Just _ -> Right (consumeSurfaceName name state)
      { stateCore = (stateCore state)
          { resourceContext = context { unrestrictedBindings = Map.delete (Name name) (unrestrictedBindings context) }
          }
      }
  where
    context = resourceContext (stateCore state)

removeScopedBinding :: Text -> SurfaceState -> Either SurfaceCheckError SurfaceState
removeScopedBinding name state =
  case Map.lookup name (stateBindings state) of
    Nothing -> Right state
    Just meta ->
      case bindingMode meta of
        Unrestricted -> removeUnrestrictedBinding name state
        Affine -> do
          let context = resourceContext (stateCore state)
              next = context { affineBindings = Map.delete (Name name) (affineBindings context) }
          Right (consumeSurfaceName name state)
            { stateCore = (stateCore state) { resourceContext = next }
            }
        Linear -> throwSpan noSpan LinearCompletion ("cannot discard scoped linear binding " <> name)

joinExclusive
  :: SurfaceEnvironment
  -> SourceSpan
  -> [SurfacePath]
  -> Either SurfaceCheckError [SurfacePath]
joinExclusive _ _ [] = Right []
joinExclusive _ span' paths = do
  let continuing = filter ((== PathContinue) . surfacePathControl) paths
      terminal = filter ((/= PathContinue) . surfacePathControl) paths
  case continuing of
    [] -> Right terminal
    [single] -> Right (terminal ++ [single])
    _ -> do
      joined <- mapCoreSpan span' IncompatibleBranchResidue $
        joinContinuing (map (resourceContext . stateCore . surfacePathState) continuing)
      state <- joinSurfaceMetadata span' continuing joined
      Right (terminal ++ [continuePath state])

joinSurfaceMetadata
  :: SourceSpan
  -> [SurfacePath]
  -> ResourceContext
  -> Either SurfaceCheckError SurfaceState
joinSurfaceMetadata span' paths joined = do
  let states = map surfacePathState paths
      firstState = head states
      surviving = Map.filterWithKey (bindingSurvives joined) (stateBindings firstState)
  mapM_ (ensureMetadataAgrees surviving) (tail states)
  pure firstState
    { stateCore = (stateCore firstState) { resourceContext = joined }
    , stateBindings = surviving
    , stateFresh = maximum (map stateFresh states)
    , stateFrame = maximum (map stateFrame states)
    , stateActiveEndpoint = commonActive states surviving
    }
  where
    ensureMetadataAgrees surviving state =
      mapM_ (\(name, meta) ->
        case Map.lookup name (stateBindings state) of
          Just other | other == meta -> Right ()
          _ -> Left SurfaceCheckError
            { surfaceErrorSpan = span'
            , surfaceErrorClass = IncompatibleBranchResidue
            , surfaceErrorDetail = "continuing branches disagree on semantic metadata for " <> name
            }) (Map.toList surviving)

bindingSurvives :: ResourceContext -> Text -> BindingMeta -> Bool
bindingSurvives context name meta =
  case bindingMode meta of
    Unrestricted -> Map.member (Name name) (unrestrictedBindings context)
    Affine -> Map.member (Name name) (affineBindings context)
    Linear -> Map.member (Name name) (linearBindings context)

commonActive :: [SurfaceState] -> Map Text BindingMeta -> Maybe Text
commonActive states surviving =
  case map stateActiveEndpoint states of
    first : rest | all (== first) rest -> first
    _ -> case [name | (name, meta) <- Map.toList surviving, isEndpointTy (bindingType meta)] of
      [name] -> Just name
      _ -> Nothing

finalizePath
  :: SurfaceEnvironment
  -> SourceSpan
  -> SurfacePath
  -> Either SurfaceCheckError SurfacePath
finalizePath environment span' path = do
  case surfacePathControl path of
    PathContinue -> ensureTerminalState environment span' Nothing (surfacePathState path)
    PathReturn _ -> ensureTerminalState environment span' Nothing (surfacePathState path)
    PathClosed outcome -> ensureTerminalState environment span' (Just outcome) (surfacePathState path)
    PathFailed _ _ -> ensureTerminalState environment span' (Just (Outcome "failure")) (surfacePathState path)
  pure path

ensureTerminalState
  :: SurfaceEnvironment
  -> SourceSpan
  -> Maybe Outcome
  -> SurfaceState
  -> Either SurfaceCheckError ()
ensureTerminalState environment span' maybeOutcome state = do
  let allowedNames = maybe Set.empty (\outcome -> Map.findWithDefault Set.empty outcome (surfaceTerminalAllowances environment)) maybeOutcome
      context = resourceContext (stateCore state)
      allowedCoreNames = Set.map Name allowedNames
      disallowedLinear = Map.withoutKeys (linearBindings context) allowedCoreNames
      reduced = context { linearBindings = disallowedLinear }
  case ensureComplete reduced of
    Right () -> Right ()
    Left errorValue -> Left SurfaceCheckError
      { surfaceErrorSpan = span'
      , surfaceErrorClass = LinearCompletion
      , surfaceErrorDetail = "component path leaves unresolved linear/loan state: " <> Text.pack (show errorValue)
      }

pathControlToCore :: SurfacePath -> Control
pathControlToCore path =
  case surfacePathControl path of
    PathContinue -> Continue
    PathReturn ty -> Return ty
    PathClosed outcome -> Closed outcome
    PathFailed failureClass detail -> Failed failureClass detail

resolveSurfaceType
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceType
  -> Either SurfaceCheckError (Mode, Ty, SurfaceShape)
resolveSurfaceType environment state surfaceTy =
  case locatedValue surfaceTy of
    SurfaceNamedType "OwnedBytes" [indexExpression] -> do
      term <- mapElaboration indexExpression $
        elaborateRefTerm (elaborationEnv environment state) indexExpression
      (index, _) <- mapFocusing indexExpression $
        elaborateRefTermAs (surfaceStaticContext environment) (stateCore state) SortNat (rewriteRefTerm state term)
      Right (Linear, TyBytes index, OwnedBytesShape index)
    SurfaceNamedType "StoreCap" _ -> do
      ty <- mapElaboration surfaceTy $ elaborateType (elaborationEnv environment state) surfaceTy
      Right (Affine, ty, PlainShape)
    SurfaceNamedType "CancelScope" _ -> do
      ty <- mapElaboration surfaceTy $ elaborateType (elaborationEnv environment state) surfaceTy
      Right (Linear, ty, PlainShape)
    SurfaceNamedType "CancelCap" _ -> do
      ty <- mapElaboration surfaceTy $ elaborateType (elaborationEnv environment state) surfaceTy
      Right (Affine, ty, PlainShape)
    _ -> do
      ty <- mapElaboration surfaceTy $ elaborateType (elaborationEnv environment state) surfaceTy
      Right (defaultMode ty, ty, shapeForType ty)

defaultMode :: Ty -> Mode
defaultMode ty =
  case ty of
    TyEndpoint _ -> Linear
    TyPendingRecv _ -> Linear
    _ -> Unrestricted

messageMode :: Ty -> Mode
messageMode ty =
  case ty of
    TyBytes _ -> Linear
    _ -> defaultMode ty

shapeForType :: Ty -> SurfaceShape
shapeForType ty =
  case ty of
    TyFrame (GrammarId grammar) -> recordShapeForGrammar grammar Nothing
    TyBytes index -> OwnedBytesShape index
    _ -> PlainShape

recordShapeForGrammar :: Text -> Maybe Text -> SurfaceShape
recordShapeForGrammar grammar baseName =
  case grammar of
    "Hello" -> RecordShape "Hello" (Map.fromList
      [ ("versions", selfField (TyOpaqueSorted "Versions" versionSetSort) versionSetSort "versions")
      ])
    "Begin" -> RecordShape "Begin" (Map.fromList
      [ ("length", selfField (TyUInt 64) (SortUInt 64) "length")
      , ("kind", selfField (TyOpaqueSorted "PayloadKind" (SortEnum "PayloadKind")) (SortEnum "PayloadKind") "kind")
      , ("digestAlg", selfField (TyOpaque "DigestAlgorithm") (SortOpaque "DigestAlgorithm") "digestAlg")
      , ("digest", selfField (TyOpaque "Digest") (SortOpaque "Digest") "digest")
      ])
    _ -> RecordShape grammar Map.empty
  where
    selfField ty sort field = FieldInfo ty sort $ fmap
      (\name -> RefField (RefVar (Name name)) field sort) baseName

versionSetSort :: RefSort
versionSetSort = SortFiniteSet (SortUInt 16)

semanticGrammarName :: Ty -> Maybe Text
semanticGrammarName ty =
  case ty of
    TyFrame (GrammarId grammar) -> Just grammar
    _ -> Nothing

baseVariableName :: Located SurfaceExpression -> Maybe Text
baseVariableName expression =
  case locatedValue expression of
    VariableExpression name -> Just name
    _ -> Nothing

isOwnedBytes :: ScalarValue -> Bool
isOwnedBytes scalar =
  case scalarShape scalar of
    OwnedBytesShape _ -> True
    _ -> case scalarType scalar of
      TyBytes _ -> True
      _ -> False

isBytesType :: Ty -> Bool
isBytesType (TyBytes _) = True
isBytesType _ = False

isEndpointTy :: Ty -> Bool
isEndpointTy (TyEndpoint _) = True
isEndpointTy _ = False

sameTy :: SurfaceState -> Ty -> Ty -> Bool
sameTy state left right =
  compareTypes (rewriteTy state left) (rewriteTy state right) == DefinitionallyEqual

rewriteTy :: SurfaceState -> Ty -> Ty
rewriteTy state ty =
  case ty of
    TyBytes index -> TyBytes (rewriteRefTerm state index)
    TyProof proposition -> TyProof (rewriteProposition state proposition)
    TyRefined binder base proposition -> TyRefined binder (rewriteTy state base) (rewriteProposition state proposition)
    other -> other

rewriteProposition :: SurfaceState -> Proposition -> Proposition
rewriteProposition state proposition =
  case proposition of
    Truth -> Truth
    Falsehood -> Falsehood
    Equal left right -> Equal (term left) (term right)
    NotEqual left right -> NotEqual (term left) (term right)
    LessThan left right -> LessThan (term left) (term right)
    LessEqual left right -> LessEqual (term left) (term right)
    Member value collection -> Member (term value) (term collection)
    Disjoint left right -> Disjoint (term left) (term right)
    Conjunction left right -> Conjunction (rewriteProposition state left) (rewriteProposition state right)
    Disjunction left right -> Disjunction (rewriteProposition state left) (rewriteProposition state right)
    Negation inner -> Negation (rewriteProposition state inner)
    Atom claim arguments -> Atom claim (map term arguments)
  where
    term = rewriteRefTerm state

rewriteRefTerm :: SurfaceState -> RefTerm -> RefTerm
rewriteRefTerm state term =
  case term of
    RefField (RefVar (Name base)) field sort ->
      case Map.lookup base (stateBindings state) >>= fieldAliasFor field of
        Just alias -> rewriteRefTerm state alias
        Nothing -> RefField (RefVar (Name base)) field sort
    RefField base field sort -> RefField (rewriteRefTerm state base) field sort
    RefLen value -> RefLen (rewriteRefTerm state value)
    RefToNat value -> RefToNat (rewriteRefTerm state value)
    RefAdd left right -> RefAdd (rewriteRefTerm state left) (rewriteRefTerm state right)
    RefSub left right -> RefSub (rewriteRefTerm state left) (rewriteRefTerm state right)
    RefScale coefficient value -> RefScale coefficient (rewriteRefTerm state value)
    other -> other

fieldAliasFor :: Text -> BindingMeta -> Maybe RefTerm
fieldAliasFor field meta =
  case bindingShape meta of
    RecordShape _ fields -> Map.lookup field fields >>= fieldAlias
    OwnedBytesShape index
      | field == "length" -> Just (RefOpaque (SortUInt 64) ("owned-length:" <> Text.pack (show index)))
      | field == "id" -> Just payloadStableTerm
    _ -> Nothing

payloadStableTerm :: RefTerm
payloadStableTerm = RefOpaque (SortStableId "OwnedBytes") "payload"

digestMatchesProposition :: Proposition
digestMatchesProposition = Atom "DigestMatches" [RefVar (Name "begin"), payloadStableTerm]

elaborationEnv :: SurfaceEnvironment -> SurfaceState -> ElaborationEnv
elaborationEnv environment state =
  foldl addProjection base projections
  where
    base = emptyElaborationEnv (surfaceStaticContext environment) (stateCore state)
    projections = concatMap bindingProjections (Map.toList (stateBindings state))
    addProjection current (path, sort) = withProjectionSort path sort current
    bindingProjections (name, meta) =
      case bindingShape meta of
        RecordShape _ fields -> [([name, field], fieldSort info) | (field, info) <- Map.toList fields]
        OwnedBytesShape _ ->
          [ ([name, "length"], SortUInt 64)
          , ([name, "kind"], SortEnum "PayloadKind")
          , ([name, "id"], SortStableId "OwnedBytes")
          ]
        ExternalParsedShape grammar _ ->
          case recordShapeForGrammar grammar (Just name) of
            RecordShape _ fields -> [([name, field], fieldSort info) | (field, info) <- Map.toList fields]
            _ -> []
        _ -> []

propositionMentionsUnchecked :: SurfaceState -> Proposition -> Bool
propositionMentionsUnchecked state proposition = any isUnchecked (propositionNames proposition)
  where
    isUnchecked (Name name) =
      case Map.lookup name (stateBindings state) of
        Just meta -> bindingShape meta == UncheckedArithmeticShape
        Nothing -> False

propositionNames :: Proposition -> [Name]
propositionNames proposition =
  case proposition of
    Truth -> []
    Falsehood -> []
    Equal left right -> termNames left ++ termNames right
    NotEqual left right -> termNames left ++ termNames right
    LessThan left right -> termNames left ++ termNames right
    LessEqual left right -> termNames left ++ termNames right
    Member left right -> termNames left ++ termNames right
    Disjoint left right -> termNames left ++ termNames right
    Conjunction left right -> propositionNames left ++ propositionNames right
    Disjunction left right -> propositionNames left ++ propositionNames right
    Negation inner -> propositionNames inner
    Atom _ arguments -> concatMap termNames arguments

termNames :: RefTerm -> [Name]
termNames term =
  case term of
    RefVar name -> [name]
    RefField base _ _ -> termNames base
    RefLen value -> termNames value
    RefToNat value -> termNames value
    RefAdd left right -> termNames left ++ termNames right
    RefSub left right -> termNames left ++ termNames right
    RefScale _ value -> termNames value
    _ -> []

reconcileConsumedBindings :: SurfaceState -> SurfaceState -> Either SurfaceCheckError SurfaceState
reconcileConsumedBindings source target =
  let sourceNames = Map.keysSet (stateBindings source)
      targetNames = Map.keysSet (stateBindings target)
      consumed = targetNames `Set.difference` sourceNames
  in foldM (flip removeBindingFromCore) target (Set.toList consumed)

removeBindingFromCore :: Text -> SurfaceState -> Either SurfaceCheckError SurfaceState
removeBindingFromCore name state =
  case Map.lookup name (stateBindings state) of
    Nothing -> Right state
    Just meta ->
      let context = resourceContext (stateCore state)
          next = case bindingMode meta of
            Unrestricted -> context
            Affine -> context { affineBindings = Map.delete (Name name) (affineBindings context) }
            Linear -> context { linearBindings = Map.delete (Name name) (linearBindings context) }
      in Right (consumeSurfaceName name state)
          { stateCore = (stateCore state) { resourceContext = next }
          }

bindingWasConsumed :: Name -> SurfaceState -> Bool
bindingWasConsumed name state =
  let context = resourceContext (stateCore state)
  in not
    ( Map.member name (unrestrictedBindings context)
      || Map.member name (affineBindings context)
      || Map.member name (linearBindings context)
    )

bindingModeForName :: SurfaceState -> Text -> Mode
bindingModeForName state name = maybe Unrestricted bindingMode (Map.lookup name (stateBindings state))

-- Compatibility shim so this module does not expose ValueResult internals in
-- its public API.
valueResultStateCompat :: Phil.Core.Value.ValueResult -> CheckState
valueResultStateCompat = Phil.Core.Value.valueResultState

applyValueResult :: Text -> SurfaceState -> Phil.Core.Value.ValueResult -> SurfaceState
applyValueResult sourceName state result =
  let next = state { stateCore = Phil.Core.Value.valueResultState result }
  in if bindingWasConsumed (Name sourceName) next
      then consumeSurfaceName sourceName next
      else next

mapCore :: Located a -> RejectionClass -> Either CheckError b -> Either SurfaceCheckError b
mapCore located rejection = mapCoreSpan (locatedSpan located) rejection

mapCoreSpan :: SourceSpan -> RejectionClass -> Either CheckError b -> Either SurfaceCheckError b
mapCoreSpan span' rejection = either
  (\err -> Left SurfaceCheckError
    { surfaceErrorSpan = span'
    , surfaceErrorClass = rejection
    , surfaceErrorDetail = Text.pack (show err)
    })
  Right

mapSession :: Located a -> Either SessionError b -> Either SurfaceCheckError b
mapSession located = either
  (\err -> Left SurfaceCheckError
    { surfaceErrorSpan = locatedSpan located
    , surfaceErrorClass = SessionAction
    , surfaceErrorDetail = Text.pack (show err)
    })
  Right

mapRecognition :: Located a -> Either RecognitionError b -> Either SurfaceCheckError b
mapRecognition located = either
  (\err -> Left SurfaceCheckError
    { surfaceErrorSpan = locatedSpan located
    , surfaceErrorClass = RecognitionProvenance
    , surfaceErrorDetail = Text.pack (show err)
    })
  Right

mapFocusing :: Located a -> Either FocusingError b -> Either SurfaceCheckError b
mapFocusing located = either
  (\err -> Left SurfaceCheckError
    { surfaceErrorSpan = locatedSpan located
    , surfaceErrorClass = MissingEvidence
    , surfaceErrorDetail = Text.pack (show err)
    })
  Right

mapElaboration :: Located a -> Either ElaborationError b -> Either SurfaceCheckError b
mapElaboration located = either
  (\err -> Left SurfaceCheckError
    { surfaceErrorSpan = locatedSpan located
    , surfaceErrorClass = TypeMismatch
    , surfaceErrorDetail = Text.pack (show err)
    })
  Right

mapValueLocated :: Located a -> Either ValueError b -> Either SurfaceCheckError b
mapValueLocated located = either (mapValueError located) Right

mapValue :: Located a -> ValueError -> Either SurfaceCheckError b
mapValue located = Left . mapValueError located

mapValueError :: Located a -> ValueError -> SurfaceCheckError
mapValueError located err = SurfaceCheckError
  { surfaceErrorSpan = locatedSpan located
  , surfaceErrorClass = case err of
      ExplicitTransportRequired _ _ -> ExplicitTransport
      ValueResourceError _ -> StructuralUse
      ValueRefinementError _ -> MissingEvidence
      _ -> TypeMismatch
  , surfaceErrorDetail = Text.pack (show err)
  }

throw :: Located a -> RejectionClass -> Text -> Either SurfaceCheckError b
throw located rejection detail = Left SurfaceCheckError
  { surfaceErrorSpan = locatedSpan located
  , surfaceErrorClass = rejection
  , surfaceErrorDetail = detail
  }

throwSpan :: SourceSpan -> RejectionClass -> Text -> Either SurfaceCheckError b
throwSpan span' rejection detail = Left SurfaceCheckError
  { surfaceErrorSpan = span'
  , surfaceErrorClass = rejection
  , surfaceErrorDetail = detail
  }

noSpan :: SourceSpan
noSpan = error "noSpan is used only on paths where a real source span is unavailable"
